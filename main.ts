'use strict';
/*
 * makeforge — a standalone GitHub-compatible git forge in one Node process.
 *
 * Surfaces, all from one in-memory store:
 *   - git smart HTTP at /{owner}/{repo}.git (upload-pack v2 + v0, receive-pack v0)
 *   - REST v3 under /api/v3
 *   - GraphQL v4 at /api/graphql
 *   - MCP (JSON-RPC 2.0, streamable HTTP) at /mcp
 *
 * Lifecycle: bind an ephemeral port, POST {"port": N} to
 * $MAKEFUN_ENV_URL/register, long-poll $MAKEFUN_ENV_URL/done, exit 0 when the
 * suite says it is done. Node 22 standard library only; no git binary.
 */
const http = require('node:http');
const crypto = require('node:crypto');
const zlib = require('node:zlib');

/* ------------------------------------------------------------------ */
/* Configuration and a deterministic logical clock                     */
/* ------------------------------------------------------------------ */

const ENV_URL = (process.env.MAKEFUN_ENV_URL || '').replace(/\/+$/, '');
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN || '';
const OWNER = 'adaiversen'; // the login the bearer token names (the suite's seeded viewer)
const OWNER_ID = 1;
const VERSION = '1.0.0';

const NOW_BASE = (() => {
  const raw = process.env.MAKEFUN_TRIAL_NOW;
  const t = raw ? Date.parse(raw) : NaN;
  return Number.isFinite(t) ? Math.floor(t / 1000) : 1767225600; // 2026-01-01
})();
let clockTick = 0;
function nowSec() { return NOW_BASE + clockTick++; }
function nowIso() { return new Date(nowSec() * 1000).toISOString().replace(/\.\d+Z$/, 'Z'); }
function isoOf(sec) { return new Date(sec * 1000).toISOString().replace(/\.\d+Z$/, 'Z'); }

let requestSeq = 0;
function nextRequestId() { return 'F' + (++requestSeq).toString(16).padStart(6, '0'); }

/* ------------------------------------------------------------------ */
/* Small helpers                                                       */
/* ------------------------------------------------------------------ */

function sha1hex(buf) { return crypto.createHash('sha1').update(buf).digest('hex'); }
function b64encode(s) { return Buffer.from(s, 'utf8').toString('base64'); }
function b64decode(s) { return Buffer.from(String(s), 'base64').toString('utf8'); }
function nodeId(kind, key) { return b64encode(kind + ':' + key); }
function parseNodeId(id) {
  try {
    const s = b64decode(id);
    const i = s.indexOf(':');
    if (i < 0) return null;
    return { kind: s.slice(0, i), key: s.slice(i + 1) };
  } catch { return null; }
}
const ZERO_SHA = '0'.repeat(40);
const isSha = (s) => typeof s === 'string' && /^[0-9a-f]{40}$/.test(s);

/* pkt-line framing */
function pkt(payload) {
  const b = Buffer.isBuffer(payload) ? payload : Buffer.from(String(payload), 'utf8');
  const len = b.length + 4;
  return Buffer.concat([Buffer.from(len.toString(16).padStart(4, '0'), 'ascii'), b]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
const PKT_RESP_END = Buffer.from('0002', 'ascii');

/* Parse a buffer of pkt-lines. Returns {lines: [{data:Buffer}|{flush:true}|{delim:true}|{respEnd:true}], rest: Buffer} */
function parsePkts(buf, offset) {
  const lines = [];
  let pos = offset || 0;
  while (pos + 4 <= buf.length) {
    const hex = buf.toString('ascii', pos, pos + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) break;
    const len = parseInt(hex, 16);
    if (len === 0) { lines.push({ flush: true }); pos += 4; break; }
    if (len === 1) { lines.push({ delim: true }); pos += 4; continue; }
    if (len === 2) { lines.push({ respEnd: true }); pos += 4; break; }
    if (len === 3) { pos += 4; continue; }
    if (pos + len > buf.length) break;
    lines.push({ data: buf.subarray(pos + 4, pos + len) });
    pos += len;
  }
  return { lines, rest: buf.subarray(pos), pos };
}

/* Find the exact length of the zlib stream starting at `start` by probing for
 * the shortest prefix that inflates cleanly (inflateSync ignores trailing
 * bytes and throws on a truncated stream). */
function inflateAt(buf, start) {
  let lo = 1;
  let hi = Math.min(buf.length - start, 64);
  let data = null;
  const total = buf.length - start;
  while (true) {
    try {
      data = zlib.inflateSync(buf.subarray(start, start + hi));
      break;
    } catch (e) {
      if (hi >= total) throw e;
      lo = hi + 1;
      hi = Math.min(total, hi * 2);
    }
  }
  // binary search the minimal successful length in [lo, hi]
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    try { zlib.inflateSync(buf.subarray(start, start + mid)); hi = mid; }
    catch { lo = mid + 1; }
  }
  return { data, length: lo };
}

/* ------------------------------------------------------------------ */
/* The store                                                           */
/* ------------------------------------------------------------------ */

let nextRepoDbId = 1;
let nextIssueDbId = 1;
let nextCommentDbId = 1;
let nextLabelDbId = 1;

const reposByName = new Map(); // name -> repo

function makeRepo(name, description, isPrivate) {
  const repo = {
    dbId: nextRepoDbId++,
    name,
    description: description || '',
    private: !!isPrivate,
    defaultBranch: 'main',
    createdAt: nowIso(),
    updatedAt: null,
    version: 1,          // bumped on any mutation; drives serializer caches
    objects: new Map(),  // sha -> {t, buf}
    refs: new Map(),     // 'refs/heads/main' -> sha
    labels: new Map(),   // name -> label
    items: new Map(),    // number -> issue or pull (shared number space)
    nextNumber: 1,
    packCache: new Map(),
  };
  repo.updatedAt = repo.createdAt;
  reposByName.set(name, repo);
  return repo;
}
function touchRepo(repo) { repo.version++; repo.updatedAt = nowIso(); repo.packCache.clear(); }

function headRef(repo) { return 'refs/heads/' + repo.defaultBranch; }
function headSha(repo) { return repo.refs.get(headRef(repo)) || null; }

/* ------------------------------------------------------------------ */
/* Git objects                                                         */
/* ------------------------------------------------------------------ */

const TYPE_NAMES = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
const TYPE_CODES = { commit: 1, tree: 2, blob: 3, tag: 4 };

function hashObject(type, buf) {
  const head = Buffer.from(type + ' ' + buf.length + '\0', 'utf8');
  return sha1hex(Buffer.concat([head, buf]));
}
function storeObject(repo, type, buf) {
  const sha = hashObject(type, buf);
  if (!repo.objects.has(sha)) repo.objects.set(sha, { t: type, buf });
  return sha;
}
function getObject(repo, sha) { return repo.objects.get(sha) || null; }

function parseCommit(buf) {
  const text = buf.toString('utf8');
  const split = text.indexOf('\n\n');
  const headText = split >= 0 ? text.slice(0, split) : text;
  const message = split >= 0 ? text.slice(split + 2) : '';
  const out = { tree: null, parents: [], author: null, committer: null, message };
  for (const line of headText.split('\n')) {
    if (line.startsWith('tree ')) out.tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) out.parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) out.author = parseIdent(line.slice(7));
    else if (line.startsWith('committer ')) out.committer = parseIdent(line.slice(10));
  }
  return out;
}
function parseIdent(s) {
  const m = /^(.*?) <(.*?)> (\d+) ([+-]\d{4})$/.exec(s || '');
  if (!m) return { name: s || '', email: '', ts: NOW_BASE, tz: '+0000' };
  return { name: m[1], email: m[2], ts: parseInt(m[3], 10), tz: m[4] };
}
function formatIdent(id) { return id.name + ' <' + id.email + '> ' + id.ts + ' ' + id.tz; }
function forgeIdent() {
  return { name: OWNER, email: OWNER + '@localhost', ts: nowSec(), tz: '+0000' };
}
function buildCommit(repo, { tree, parents, message, author, committer }) {
  const a = author || forgeIdent();
  const c = committer || a;
  let head = 'tree ' + tree + '\n';
  for (const p of parents) head += 'parent ' + p + '\n';
  head += 'author ' + formatIdent(a) + '\n';
  head += 'committer ' + formatIdent(c) + '\n';
  return storeObject(repo, 'commit', Buffer.from(head + '\n' + (message || ''), 'utf8'));
}

/* Tree entries: [{mode, name, sha}] — mode as written in the raw object. */
function parseTree(buf) {
  const entries = [];
  let pos = 0;
  while (pos < buf.length) {
    const sp = buf.indexOf(0x20, pos);
    const mode = buf.toString('ascii', pos, sp);
    const nul = buf.indexOf(0x00, sp + 1);
    const name = buf.toString('utf8', sp + 1, nul);
    const sha = buf.toString('hex', nul + 1, nul + 21);
    entries.push({ mode, name, sha });
    pos = nul + 21;
  }
  return entries;
}
function entryKind(mode) {
  if (mode === '40000') return 'tree';
  if (mode === '160000') return 'commit';
  return 'blob';
}
function buildTree(repo, entries) {
  const sorted = [...entries].sort((a, b) => {
    const an = a.name + (entryKind(a.mode) === 'tree' ? '/' : '');
    const bn = b.name + (entryKind(b.mode) === 'tree' ? '/' : '');
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts = [];
  for (const e of sorted) {
    parts.push(Buffer.from(e.mode + ' ' + e.name + '\0', 'utf8'));
    parts.push(Buffer.from(e.sha, 'hex'));
  }
  return storeObject(repo, 'tree', Buffer.concat(parts));
}

/* Flatten a tree into Map<path, {sha, mode}> for files (blobs) only. */
function flattenTree(repo, treeSha, prefix, out) {
  out = out || new Map();
  prefix = prefix || '';
  if (!treeSha) return out;
  const obj = getObject(repo, treeSha);
  if (!obj || obj.t !== 'tree') return out;
  for (const e of parseTree(obj.buf)) {
    const path = prefix + e.name;
    const kind = entryKind(e.mode);
    if (kind === 'tree') flattenTree(repo, e.sha, path + '/', out);
    else if (kind === 'blob') out.set(path, { sha: e.sha, mode: e.mode });
  }
  return out;
}
/* Rebuild a tree hierarchy from a flat Map<path, {sha, mode}>. */
function unflattenTree(repo, files) {
  function buildLevel(prefix) {
    const dirs = new Map();
    const entries = [];
    for (const [path, f] of files) {
      if (!path.startsWith(prefix)) continue;
      const rest = path.slice(prefix.length);
      const slash = rest.indexOf('/');
      if (slash < 0) entries.push({ mode: f.mode, name: rest, sha: f.sha });
      else {
        const dir = rest.slice(0, slash);
        if (!dirs.has(dir)) dirs.set(dir, true);
      }
    }
    for (const dir of dirs.keys()) {
      entries.push({ mode: '40000', name: dir, sha: buildLevel(prefix + dir + '/') });
    }
    return buildTree(repo, entries);
  }
  return buildLevel('');
}
/* Look up one path in a tree; returns {sha, mode, kind} or null. */
function treeLookup(repo, treeSha, path) {
  const parts = path.split('/').filter((p) => p.length > 0);
  let cur = treeSha;
  for (let i = 0; i < parts.length; i++) {
    const obj = cur ? getObject(repo, cur) : null;
    if (!obj || obj.t !== 'tree') return null;
    const e = parseTree(obj.buf).find((x) => x.name === parts[i]);
    if (!e) return null;
    if (i === parts.length - 1) return { sha: e.sha, mode: e.mode, kind: entryKind(e.mode) };
    if (entryKind(e.mode) !== 'tree') return null;
    cur = e.sha;
  }
  return null;
}
function commitTreeSha(repo, commitSha) {
  const obj = commitSha ? getObject(repo, commitSha) : null;
  if (!obj || obj.t !== 'commit') return null;
  return parseCommit(obj.buf).tree;
}
/* Walk a ref name (branch, full ref or sha) to a commit sha. */
function resolveRef(repo, ref) {
  if (!ref) return null;
  if (isSha(ref) && getObject(repo, ref)) return ref;
  const candidates = [ref, 'refs/heads/' + ref, 'refs/tags/' + ref, 'refs/' + ref];
  for (const c of candidates) if (repo.refs.has(c)) return repo.refs.get(c);
  if (ref === 'HEAD') return headSha(repo);
  return null;
}
/* Is `anc` an ancestor of (or equal to) `desc`? */
function isAncestor(repo, anc, desc) {
  if (!anc || !desc) return false;
  if (anc === desc) return true;
  const seen = new Set();
  const stack = [desc];
  while (stack.length) {
    const cur = stack.pop();
    if (cur === anc) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = getObject(repo, cur);
    if (!obj || obj.t !== 'commit') continue;
    for (const p of parseCommit(obj.buf).parents) stack.push(p);
  }
  return false;
}
function mergeBase(repo, a, b) {
  const ancA = new Set();
  const stack = [a];
  while (stack.length) {
    const cur = stack.pop();
    if (ancA.has(cur)) continue;
    ancA.add(cur);
    const obj = getObject(repo, cur);
    if (obj && obj.t === 'commit') for (const p of parseCommit(obj.buf).parents) stack.push(p);
  }
  const seen = new Set();
  const queue = [b];
  while (queue.length) {
    const cur = queue.shift();
    if (ancA.has(cur)) return cur;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = getObject(repo, cur);
    if (obj && obj.t === 'commit') for (const p of parseCommit(obj.buf).parents) queue.push(p);
  }
  return null;
}
/* Commits reachable from `tip` but not from `excludeTip`, newest first. */
function commitsBetween(repo, tip, excludeTip) {
  const excluded = new Set();
  if (excludeTip) {
    const stack = [excludeTip];
    while (stack.length) {
      const cur = stack.pop();
      if (excluded.has(cur)) continue;
      excluded.add(cur);
      const obj = getObject(repo, cur);
      if (obj && obj.t === 'commit') for (const p of parseCommit(obj.buf).parents) stack.push(p);
    }
  }
  const out = [];
  const seen = new Set();
  const stack = [tip];
  while (stack.length) {
    const cur = stack.pop();
    if (!cur || seen.has(cur) || excluded.has(cur)) continue;
    seen.add(cur);
    const obj = getObject(repo, cur);
    if (!obj || obj.t !== 'commit') continue;
    out.push(cur);
    for (const p of parseCommit(obj.buf).parents) stack.push(p);
  }
  return out;
}

/* ------------------------------------------------------------------ */
/* Packfiles                                                           */
/* ------------------------------------------------------------------ */

function packObjectHeader(typeCode, size) {
  const bytes = [];
  let b = (typeCode << 4) | (size & 0x0f);
  size = Math.floor(size / 16);
  while (size > 0) {
    bytes.push(b | 0x80);
    b = size & 0x7f;
    size = Math.floor(size / 128);
  }
  bytes.push(b);
  return Buffer.from(bytes);
}
function buildPack(objects) {
  const parts = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const o of objects) {
    parts.push(packObjectHeader(TYPE_CODES[o.t], o.buf.length));
    parts.push(zlib.deflateSync(o.buf, { level: 6 }));
  }
  const body = Buffer.concat(parts);
  const trailer = crypto.createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}
/* Collect the object set for a fetch: closure of wants minus closure of
 * haves, optionally limited to `depth` commits (shallow). When the client
 * reports shallow commits (`shallowSet`), those commits are held only at
 * their boundary (commit + tree, no ancestors): `depth` then counts the
 * extra generations to send below that boundary (a deepen request). */
function collectObjects(repo, wants, haves, depth, shallowSet) {
  const shallowIn = shallowSet || new Set();
  const excluded = new Set();
  const markExcluded = (sha) => {
    const stack = [sha];
    while (stack.length) {
      const cur = stack.pop();
      if (excluded.has(cur)) continue;
      const obj = getObject(repo, cur);
      if (!obj) continue;
      excluded.add(cur);
      if (obj.t === 'commit') {
        const c = parseCommit(obj.buf);
        if (c.tree) stack.push(c.tree);
        for (const p of c.parents) stack.push(p);
      } else if (obj.t === 'tree') {
        for (const e of parseTree(obj.buf)) stack.push(e.sha);
      } else if (obj.t === 'tag') {
        const m = /^object ([0-9a-f]{40})/m.exec(obj.buf.toString('utf8'));
        if (m) stack.push(m[1]);
      }
    }
  };
  // A shallow-held commit: the client has the commit and its tree only.
  const markShallowHeld = (sha) => {
    const obj = getObject(repo, sha);
    if (!obj) return;
    excluded.add(sha);
    if (obj.t === 'commit') {
      const c = parseCommit(obj.buf);
      if (c.tree) markExcluded(c.tree);
    }
  };
  for (const h of haves) {
    if (shallowIn.has(h)) markShallowHeld(h);
    else markExcluded(h);
  }

  const included = new Map();
  const shallow = [];
  const includeTree = (treeSha) => {
    const stack = [treeSha];
    while (stack.length) {
      const cur = stack.pop();
      if (included.has(cur) || excluded.has(cur)) continue;
      const obj = getObject(repo, cur);
      if (!obj) continue;
      included.set(cur, obj);
      if (obj.t === 'tree') for (const e of parseTree(obj.buf)) stack.push(e.sha);
    }
  };
  // BFS over commits; each commit carries its level (generations below the
  // want). A shallow-held want is excluded from the pack by markShallowHeld
  // but still traversed, so a deepen delivers the generations below it.
  const queue = wants
    .filter((w) => getObject(repo, w))
    .map((w) => [w, 1]);
  const seenCommits = new Map();
  let qi = 0;
  while (qi < queue.length) {
    const [sha, level] = queue[qi++];
    if (seenCommits.has(sha) && seenCommits.get(sha) <= level) continue;
    seenCommits.set(sha, level);
    const obj = getObject(repo, sha);
    if (!obj) continue;
    if (obj.t === 'tag') {
      if (!excluded.has(sha)) included.set(sha, obj);
      const m = /^object ([0-9a-f]{40})/m.exec(obj.buf.toString('utf8'));
      if (m) queue.push([m[1], level + 1]);
      continue;
    }
    if (obj.t !== 'commit') { if (!excluded.has(sha)) included.set(sha, obj); continue; }
    const c = parseCommit(obj.buf);
    const atBoundary = depth > 0 && level >= depth;
    if (!excluded.has(sha)) {
      included.set(sha, obj);
      if (c.tree) includeTree(c.tree);
      if (atBoundary && c.parents.length) shallow.push(sha);
    }
    if (!atBoundary) for (const p of c.parents) queue.push([p, level + 1]);
  }
  // A shallow-held commit whose parent was delivered is no longer shallow.
  const unshallow = [];
  for (const s of shallowIn) {
    const obj = getObject(repo, s);
    if (!obj || obj.t !== 'commit') continue;
    const c = parseCommit(obj.buf);
    if (c.parents.some((p) => included.has(p))) unshallow.push(s);
  }
  const order = { commit: 0, tree: 1, blob: 2, tag: 3 };
  const objects = [...included.entries()]
    .map(([sha, o]) => ({ sha, t: o.t, buf: o.buf }))
    .sort((a, b) => order[a.t] - order[b.t]);
  return { objects, shallow, unshallow };
}
function packFor(repo, wants, haves, depth, shallowSet) {
  const shallowKey = shallowSet && shallowSet.size ? [...shallowSet].sort().join(',') : '';
  const key = sha1hex(Buffer.from(
    [...wants].sort().join(',') + '|' + [...haves].sort().join(',') + '|' + depth + '|' + shallowKey, 'utf8'));
  let pack = repo.packCache.get(key);
  if (!pack) {
    const { objects, shallow, unshallow } = collectObjects(repo, wants, haves, depth, shallowSet);
    pack = { bytes: buildPack(objects), shallow, unshallow };
    repo.packCache.set(key, pack);
  }
  return pack;
}

/* Delta application (for receive-pack packs that use deltas). */
function applyDelta(base, delta) {
  let off = 0;
  const readVarint = () => {
    let v = 0, s = 0;
    for (;;) {
      const b = delta[off++];
      v += (b & 0x7f) * Math.pow(2, s);
      s += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  };
  readVarint(); // source size
  const dstSize = readVarint();
  const parts = [];
  let produced = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let o = 0, sz = 0;
      if (op & 0x01) o = delta[off++];
      if (op & 0x02) o += delta[off++] << 8;
      if (op & 0x04) o += delta[off++] << 16;
      if (op & 0x08) o += delta[off++] * 16777216;
      if (op & 0x10) sz = delta[off++];
      if (op & 0x20) sz += delta[off++] << 8;
      if (op & 0x40) sz += delta[off++] << 16;
      if (sz === 0) sz = 0x10000;
      parts.push(base.subarray(o, o + sz));
      produced += sz;
    } else if (op) {
      parts.push(delta.subarray(off, off + op));
      off += op;
      produced += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  const out = Buffer.concat(parts);
  if (out.length !== dstSize) throw new Error('delta size mismatch');
  return out;
}
/* Parse a pack stream into the repo store. Returns the object count. */
function receivePack(repo, buf) {
  if (buf.length < 12 || buf.toString('ascii', 0, 4) !== 'PACK') throw new Error('not a pack');
  const count = buf.readUInt32BE(8);
  let pos = 12;
  const objs = [];
  for (let i = 0; i < count; i++) {
    const headerStart = pos;
    let byte = buf[pos++];
    const typeCode = (byte >> 4) & 0x07;
    while (byte & 0x80) { byte = buf[pos++]; }
    let baseSha = null, baseHeaderStart = -1;
    if (typeCode === 6) { // ofs-delta: base is `offset` bytes before this header
      let b = buf[pos++];
      let offset = b & 0x7f;
      while (b & 0x80) { b = buf[pos++]; offset = ((offset + 1) << 7) | (b & 0x7f); }
      baseHeaderStart = headerStart - offset;
    } else if (typeCode === 7) { // ref-delta: base named by sha
      baseSha = buf.toString('hex', pos, pos + 20);
      pos += 20;
    }
    const inf = inflateAt(buf, pos);
    pos += inf.length;
    objs.push({ headerStart, typeCode, data: inf.data, baseSha, baseHeaderStart, resolved: null, sha: null });
  }
  const byHeaderStart = new Map(objs.map((o) => [o.headerStart, o]));
  const resolve = (o) => {
    if (o.resolved) return o.resolved;
    let type, data;
    if (o.typeCode === 6) {
      const base = byHeaderStart.get(o.baseHeaderStart);
      if (!base) throw new Error('ofs-delta base missing');
      const b = resolve(base);
      type = b.t; data = applyDelta(b.buf, o.data);
    } else if (o.typeCode === 7) {
      let baseObj = getObject(repo, o.baseSha);
      if (!baseObj) {
        for (const cand of objs) {
          if (cand === o) continue;
          const r = resolve(cand);
          if (cand.sha === o.baseSha) { baseObj = r; break; }
        }
      }
      if (!baseObj) throw new Error('ref-delta base missing');
      type = baseObj.t; data = applyDelta(baseObj.buf, o.data);
    } else {
      type = TYPE_NAMES[o.typeCode];
      data = o.data;
    }
    o.sha = storeObject(repo, type, data);
    o.resolved = { t: type, buf: data };
    return o.resolved;
  };
  for (const o of objs) resolve(o);
  return count;
}

/* ------------------------------------------------------------------ */
/* Git smart HTTP                                                      */
/* ------------------------------------------------------------------ */

const UPLOAD_CAPS = 'multi_ack_detailed no-done side-band-64k thin-pack ofs-delta deepen-since deepen-not agent=makeforge/' + VERSION;
const RECEIVE_CAPS = 'report-status delete-refs side-band-64k quiet ofs-delta agent=makeforge/' + VERSION;

function sortedRefs(repo) {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
}
function peelToCommit(repo, sha) {
  let cur = sha;
  const seen = new Set();
  while (!seen.has(cur)) {
    seen.add(cur);
    const obj = getObject(repo, cur);
    if (!obj) return null;
    if (obj.t === 'commit') return cur;
    if (obj.t !== 'tag') return null;
    const m = /^object ([0-9a-f]{40})/m.exec(obj.buf.toString('utf8'));
    if (!m) return null;
    cur = m[1];
  }
  return null;
}
function frameSideband(data, band) {
  const parts = [];
  const CHUNK = 65500;
  for (let off = 0; off < data.length; off += CHUNK) {
    const slice = data.subarray(off, Math.min(data.length, off + CHUNK));
    parts.push(pkt(Buffer.concat([Buffer.from([band]), slice])));
  }
  return Buffer.concat(parts);
}

function handleInfoRefs(req, res, repo, service, isV2) {
  const isUpload = service === 'git-upload-pack';
  const ct = 'application/x-' + service + '-advertisement';
  if (isV2 && isUpload) {
    const lines = [
      pkt('version 2\n'),
      pkt('agent=makeforge/' + VERSION + '\n'),
      pkt('ls-refs=unborn\n'),
      pkt('fetch=shallow wait-for-done filter\n'),
      pkt('object-format=sha1\n'),
      PKT_FLUSH,
    ];
    res.writeHead(200, { 'Content-Type': ct, 'Cache-Control': 'no-cache' });
    res.end(Buffer.concat(lines));
    return;
  }
  const caps = isUpload ? UPLOAD_CAPS : RECEIVE_CAPS;
  const parts = [pkt('# service=' + service + '\n'), PKT_FLUSH];
  const refs = sortedRefs(repo);
  const hs = headSha(repo);
  if (refs.length === 0) {
    parts.push(pkt(ZERO_SHA + ' capabilities^{}\0' + caps + '\n'));
  } else {
    const headLine = (hs || ZERO_SHA) + ' HEAD\0' + caps +
      (isUpload ? ' symref=HEAD:' + headRef(repo) : '') + '\n';
    parts.push(pkt(headLine));
    for (const [ref, sha] of refs) {
      parts.push(pkt(sha + ' ' + ref + '\n'));
      const peeled = peelToCommit(repo, sha);
      if (peeled && peeled !== sha) parts.push(pkt(peeled + ' ' + ref + '^{}\n'));
    }
  }
  parts.push(PKT_FLUSH);
  res.writeHead(200, { 'Content-Type': ct, 'Cache-Control': 'no-cache' });
  res.end(Buffer.concat(parts));
}

/* v0 upload-pack: wants/haves in one body, pack out (sideband if asked). */
function handleUploadPackV0(repo, body, res) {
  const { lines, rest } = parsePkts(body, 0);
  const wants = [];
  const haves = [];
  let caps = '';
  let deepen = 0;
  let done = false;
  let phase = 'want';
  const all = [...lines];
  // `rest` may hold no more pkt data in v0 requests; wants end at first flush.
  for (const ln of all) {
    if (ln.flush) { phase = 'have'; continue; }
    if (!ln.data) continue;
    const s = ln.data.toString('utf8').replace(/\n$/, '');
    if (s.startsWith('want ')) {
      const sp = s.indexOf(' ', 5);
      if (sp < 0) wants.push(s.slice(5).trim());
      else {
        wants.push(s.slice(5, sp).trim());
        if (!caps) caps = s.slice(sp + 1);
      }
    } else if (s.startsWith('have ')) haves.push(s.slice(5).trim());
    else if (s.startsWith('deepen ')) deepen = parseInt(s.slice(7), 10) || 0;
    else if (s === 'done') done = true;
  }
  void rest; void phase; void done;
  const parts = [];
  const { bytes, shallow } = packFor(repo, wants, haves, deepen);
  if (deepen > 0) for (const sha of shallow) parts.push(pkt('shallow ' + sha + '\n'));
  const common = haves.find((h) => getObject(repo, h));
  parts.push(pkt(common ? 'ACK ' + common + '\n' : 'NAK\n'));
  if (caps.includes('side-band-64k')) {
    parts.push(frameSideband(bytes, 1));
    parts.push(PKT_FLUSH);
  } else {
    parts.push(bytes);
  }
  res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' });
  res.end(Buffer.concat(parts));
}

/* Protocol v2: ls-refs and fetch commands. */
function handleUploadPackV2(repo, body, res) {
  const { lines } = parsePkts(body, 0);
  let idx = 0;
  const first = lines[idx++];
  const cmdLine = first && first.data ? first.data.toString('utf8').replace(/\n$/, '') : '';
  const command = cmdLine.startsWith('command=') ? cmdLine.slice(8) : '';
  const capLines = [];
  while (idx < lines.length && !lines[idx].delim && !lines[idx].flush) {
    if (lines[idx].data) capLines.push(lines[idx].data.toString('utf8').replace(/\n$/, ''));
    idx++;
  }
  if (idx < lines.length && lines[idx].delim) idx++;
  const args = [];
  while (idx < lines.length && !lines[idx].flush) {
    if (lines[idx].data) args.push(lines[idx].data.toString('utf8').replace(/\n$/, ''));
    idx++;
  }
  const allText = capLines.concat(args).join('\n');
  const sideband = allText.includes('side-band-64k');

  if (command === 'ls-refs') {
    const prefixes = [];
    let peel = false, symrefs = false, unborn = false;
    for (const a of args) {
      if (a.startsWith('ref-prefix ')) prefixes.push(a.slice(11));
      else if (a === 'peel') peel = true;
      else if (a === 'symrefs') symrefs = true;
      else if (a === 'unborn') unborn = true;
    }
    const matches = (name) => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
    const parts = [];
    const hs = headSha(repo);
    const headMatches = prefixes.length === 0 || prefixes.some((p) => 'HEAD'.startsWith(p) || p.startsWith('HEAD'));
    if (headMatches) {
      if (hs) {
        parts.push(pkt(hs + ' HEAD' + (symrefs ? ' symref-target:' + headRef(repo) : '') + '\n'));
      } else if (unborn) {
        parts.push(pkt(ZERO_SHA + ' HEAD unborn' + (symrefs ? ' symref-target:' + headRef(repo) : '') + '\n'));
      }
    }
    for (const [ref, sha] of sortedRefs(repo)) {
      if (!matches(ref)) continue;
      let line = sha + ' ' + ref;
      if (peel) {
        const p = peelToCommit(repo, sha);
        if (p && p !== sha) line += ' peeled:' + p;
      }
      parts.push(pkt(line + '\n'));
    }
    parts.push(PKT_FLUSH);
    res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' });
    res.end(Buffer.concat(parts));
    return;
  }

  if (command === 'fetch') {
    const wants = [], haves = [], wantRefs = [], shallowArgs = [];
    let deepen = 0, done = false, waitForDone = false;
    for (const a of args) {
      if (a.startsWith('want ')) wants.push(a.slice(5).trim());
      else if (a.startsWith('have ')) haves.push(a.slice(5).trim());
      else if (a.startsWith('shallow ')) shallowArgs.push(a.slice(8).trim());
      else if (a.startsWith('want-ref ')) wantRefs.push(a.slice(9).trim());
      else if (a.startsWith('deepen ')) deepen = parseInt(a.slice(7), 10) || 0;
      else if (a === 'done') done = true;
      else if (a === 'wait-for-done') waitForDone = true;
    }
    const parts = [];
    const common = haves.filter((h) => getObject(repo, h));
    parts.push(pkt('acknowledgments\n'));
    if (common.length) {
      for (const c of common) parts.push(pkt('ACK ' + c + '\n'));
      if (!done && waitForDone) parts.push(pkt('ready\n'));
    } else {
      parts.push(pkt('NAK\n'));
    }
    if (!done) {
      parts.push(PKT_FLUSH);
      res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' });
      res.end(Buffer.concat(parts));
      return;
    }
    parts.push(PKT_DELIM);
    const { bytes, shallow, unshallow } = packFor(repo, wants, haves, deepen, new Set(shallowArgs));
    if (deepen > 0 || shallow.length || unshallow.length) {
      parts.push(pkt('shallow-info\n'));
      for (const sha of shallow) parts.push(pkt('shallow ' + sha + '\n'));
      for (const sha of unshallow) parts.push(pkt('unshallow ' + sha + '\n'));
      parts.push(PKT_DELIM);
    }
    if (wantRefs.length) {
      parts.push(pkt('wanted-refs\n'));
      for (const wr of wantRefs) {
        const sha = resolveRef(repo, wr);
        if (sha) parts.push(pkt(sha + ' ' + wr + '\n'));
      }
      parts.push(PKT_DELIM);
    }
    parts.push(pkt('packfile\n'));
    // The suite's client always demuxes the packfile section as sideband,
    // whether or not it sent the side-band-64k fetch argument.
    parts.push(frameSideband(bytes, 1));
    parts.push(PKT_FLUSH);
    res.writeHead(200, { 'Content-Type': 'application/x-git-upload-pack-result' });
    res.end(Buffer.concat(parts));
    return;
  }

  res.writeHead(400, { 'Content-Type': 'text/plain' });
  res.end('unknown command');
}

/* receive-pack v0: ref updates + pack, report-status out. */
function handleReceivePack(repo, body, res) {
  const commands = [];
  let caps = '';
  let pos = 0;
  while (pos + 4 <= body.length) {
    const hex = body.toString('ascii', pos, pos + 4);
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) break;
    const len = parseInt(hex, 16);
    if (len === 0) { pos += 4; break; }
    if (len < 4 || pos + len > body.length) break;
    let line = body.toString('utf8', pos + 4, pos + len);
    pos += len;
    const nul = line.indexOf('\0');
    if (nul >= 0) { caps = line.slice(nul + 1); line = line.slice(0, nul); }
    const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (.+)$/.exec(line.replace(/\n$/, ''));
    if (m) commands.push({ oldSha: m[1], newSha: m[2], ref: m[3] });
  }
  const packBytes = body.subarray(pos);
  const wantReport = caps.includes('report-status');
  const sideband = caps.includes('side-band-64k');
  let unpackError = null;
  const hasPack = packBytes.length > 0 && commands.some((c) => c.newSha !== ZERO_SHA);
  if (hasPack) {
    try { receivePack(repo, packBytes); }
    catch (e) { unpackError = e.message || 'unpack error'; }
  }
  const results = [];
  for (const c of commands) {
    if (unpackError) { results.push({ ref: c.ref, ok: false, msg: 'unpacker error' }); continue; }
    const current = repo.refs.get(c.ref) || ZERO_SHA;
    if (!c.ref.startsWith('refs/')) { results.push({ ref: c.ref, ok: false, msg: 'invalid ref' }); continue; }
    if (c.oldSha !== current) { results.push({ ref: c.ref, ok: false, msg: 'stale info' }); continue; }
    if (c.newSha === ZERO_SHA) {
      repo.refs.delete(c.ref);
      results.push({ ref: c.ref, ok: true });
      continue;
    }
    const obj = getObject(repo, c.newSha);
    if (!obj || (obj.t !== 'commit' && obj.t !== 'tag')) {
      results.push({ ref: c.ref, ok: false, msg: 'invalid object' });
      continue;
    }
    if (c.oldSha !== ZERO_SHA && obj.t === 'commit') {
      const target = peelToCommit(repo, c.oldSha) || c.oldSha;
      if (!isAncestor(repo, target, c.newSha)) {
        results.push({ ref: c.ref, ok: false, msg: 'non-fast-forward' });
        continue;
      }
    }
    repo.refs.set(c.ref, c.newSha);
    results.push({ ref: c.ref, ok: true });
  }
  if (results.some((r) => r.ok)) touchRepo(repo);
  if (!wantReport) {
    res.writeHead(200, { 'Content-Type': 'application/x-git-receive-pack-result' });
    res.end(sideband ? PKT_FLUSH : Buffer.alloc(0));
    return;
  }
  const reportParts = [pkt(unpackError ? 'unpack ' + unpackError + '\n' : 'unpack ok\n')];
  for (const r of results) {
    reportParts.push(pkt(r.ok ? 'ok ' + r.ref + '\n' : 'ng ' + r.ref + ' ' + r.msg + '\n'));
  }
  reportParts.push(PKT_FLUSH);
  const report = Buffer.concat(reportParts);
  res.writeHead(200, { 'Content-Type': 'application/x-git-receive-pack-result' });
  if (sideband) res.end(Buffer.concat([frameSideband(report, 1), PKT_FLUSH]));
  else res.end(report);
}

/* ------------------------------------------------------------------ */
/* Shared domain logic                                                 */
/* ------------------------------------------------------------------ */

function userJson(base) {
  return {
    login: OWNER, id: OWNER_ID, node_id: nodeId('User', OWNER),
    avatar_url: '', gravatar_id: '', url: base + '/api/v3/users/' + OWNER,
    html_url: base + '/' + OWNER, type: 'User', site_admin: false,
  };
}
function repoJson(repo, base) {
  const full = OWNER + '/' + repo.name;
  let open = 0;
  for (const it of repo.items.values()) if (it.state === 'open') open++;
  return {
    id: repo.dbId, node_id: nodeId('Repository', repo.dbId),
    name: repo.name, full_name: full,
    owner: userJson(base),
    private: repo.private, description: repo.description, fork: false,
    url: base + '/api/v3/repos/' + full,
    html_url: base + '/' + full,
    clone_url: base + '/' + full + '.git',
    git_url: 'git://' + 'localhost/' + full + '.git',
    ssh_url: 'git@localhost:' + full + '.git',
    homepage: '', size: 0, stargazers_count: 0, watchers_count: 0,
    language: null, topics: [],
    has_issues: true, has_projects: true, has_downloads: true, has_wiki: true, has_pages: false,
    forks_count: 0, open_issues_count: open, watchers: 0,
    archived: false, disabled: false, visibility: repo.private ? 'private' : 'public',
    default_branch: repo.defaultBranch,
    created_at: repo.createdAt, updated_at: repo.updatedAt, pushed_at: repo.updatedAt,
    permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
  };
}
function labelJson(repo, label, base) {
  return {
    id: label.id, node_id: nodeId('Label', repo.dbId + ':' + label.name),
    name: label.name, color: label.color, description: label.description,
    default: false,
    url: base + '/api/v3/repos/' + OWNER + '/' + repo.name + '/labels/' + encodeURIComponent(label.name),
  };
}
function issueJson(repo, item, base) {
  const full = OWNER + '/' + repo.name;
  const out = {
    id: item.dbId, node_id: nodeId(item.kind === 'pull' ? 'PullRequest' : 'Issue', repo.dbId + ':' + item.number),
    number: item.number, title: item.title, body: item.body || '',
    state: item.state,
    user: userJson(base),
    labels: item.labels.map((n) => repo.labels.get(n)).filter(Boolean).map((l) => labelJson(repo, l, base)),
    assignee: null, assignees: [], milestone: null, locked: false,
    comments: item.comments.length,
    created_at: item.createdAt, updated_at: item.updatedAt,
    closed_at: item.closedAt || null,
    url: base + '/api/v3/repos/' + full + '/issues/' + item.number,
    repository_url: base + '/api/v3/repos/' + full,
    labels_url: base + '/api/v3/repos/' + full + '/issues/' + item.number + '/labels{/name}',
    comments_url: base + '/api/v3/repos/' + full + '/issues/' + item.number + '/comments',
    html_url: base + '/' + full + '/issues/' + item.number,
  };
  if (item.kind === 'pull') {
    out.pull_request = {
      url: base + '/api/v3/repos/' + full + '/pulls/' + item.number,
      html_url: base + '/' + full + '/pull/' + item.number,
      diff_url: base + '/' + full + '/pull/' + item.number + '.diff',
      patch_url: base + '/' + full + '/pull/' + item.number + '.patch',
      merged_at: item.mergedAt || null,
    };
    out.html_url = base + '/' + full + '/pull/' + item.number;
  }
  return out;
}
function prJson(repo, item, base) {
  const full = OWNER + '/' + repo.name;
  const headSha = resolveRef(repo, item.headRef) || item.headSha || null;
  const baseSha = resolveRef(repo, item.baseRef) || null;
  const side = (ref, sha) => ({
    label: OWNER + ':' + ref, ref, sha,
    user: userJson(base), repo: repoJson(repo, base),
  });
  return {
    id: item.dbId, node_id: nodeId('PullRequest', repo.dbId + ':' + item.number),
    number: item.number, title: item.title, body: item.body || '',
    state: item.state,
    user: userJson(base),
    labels: item.labels.map((n) => repo.labels.get(n)).filter(Boolean).map((l) => labelJson(repo, l, base)),
    draft: false, locked: false,
    head: side(item.headRef, headSha), base: side(item.baseRef, baseSha),
    merged: !!item.merged, merged_at: item.mergedAt || null,
    merge_commit_sha: item.mergeCommitSha || null,
    merged_by: item.merged ? userJson(base) : null,
    comments: item.comments.length, review_comments: 0, commits: 0, additions: 0, deletions: 0, changed_files: 0,
    created_at: item.createdAt, updated_at: item.updatedAt, closed_at: item.closedAt || null,
    url: base + '/api/v3/repos/' + full + '/pulls/' + item.number,
    html_url: base + '/' + full + '/pull/' + item.number,
    diff_url: base + '/' + full + '/pull/' + item.number + '.diff',
    patch_url: base + '/' + full + '/pull/' + item.number + '.patch',
    _links: {},
  };
}
function commentJson(repo, item, comment, base) {
  const full = OWNER + '/' + repo.name;
  return {
    id: comment.id, node_id: nodeId('IssueComment', comment.id),
    body: comment.body, user: userJson(base),
    created_at: comment.createdAt, updated_at: comment.updatedAt,
    url: base + '/api/v3/repos/' + full + '/issues/comments/' + comment.id,
    html_url: base + '/' + full + '/issues/' + item.number + '#issuecomment-' + comment.id,
    issue_url: base + '/api/v3/repos/' + full + '/issues/' + item.number,
  };
}
function commitJson(repo, sha, base) {
  const full = OWNER + '/' + repo.name;
  const obj = getObject(repo, sha);
  const c = parseCommit(obj.buf);
  const ident = (id) => id ? { name: id.name, email: id.email, date: isoOf(id.ts) } : { name: '', email: '', date: repo.createdAt };
  return {
    sha, node_id: nodeId('Commit', sha),
    commit: {
      author: ident(c.author), committer: ident(c.committer),
      message: c.message, tree: { sha: c.tree, url: base + '/api/v3/repos/' + full + '/git/trees/' + c.tree },
      comment_count: 0,
      verification: { verified: false, reason: 'unsigned', signature: null, payload: null },
    },
    url: base + '/api/v3/repos/' + full + '/commits/' + sha,
    html_url: base + '/' + full + '/commit/' + sha,
    comments_url: base + '/api/v3/repos/' + full + '/commits/' + sha + '/comments',
    author: userJson(base), committer: userJson(base),
    parents: c.parents.map((p) => ({ sha: p, url: base + '/api/v3/repos/' + full + '/commits/' + p, html_url: base + '/' + full + '/commit/' + p })),
  };
}
function commitSummaryJson(repo, sha, base) {
  const full = OWNER + '/' + repo.name;
  const c = parseCommit(getObject(repo, sha).buf);
  const ident = (id) => id ? { name: id.name, email: id.email, date: isoOf(id.ts) } : { name: '', email: '', date: repo.createdAt };
  return {
    sha, node_id: nodeId('Commit', sha),
    url: base + '/api/v3/repos/' + full + '/git/commits/' + sha,
    html_url: base + '/' + full + '/commit/' + sha,
    author: ident(c.author), committer: ident(c.committer),
    message: c.message,
    tree: { sha: c.tree, url: base + '/api/v3/repos/' + full + '/git/trees/' + c.tree },
    parents: c.parents.map((p) => ({ sha: p, url: base + '/api/v3/repos/' + full + '/git/commits/' + p, html_url: base + '/' + full + '/commit/' + p })),
  };
}

/* Three-way tree merge over flattened file maps. */
function mergeTrees(repo, baseTree, ourTree, theirTree) {
  const b = flattenTree(repo, baseTree);
  const o = flattenTree(repo, ourTree);
  const t = flattenTree(repo, theirTree);
  const eq = (x, y) => (x == null && y == null) || (!!x && !!y && x.sha === y.sha && x.mode === y.mode);
  const result = new Map();
  const keys = new Set([...b.keys(), ...o.keys(), ...t.keys()]);
  for (const k of keys) {
    const bv = b.get(k) || null, ov = o.get(k) || null, tv = t.get(k) || null;
    if (eq(ov, tv)) { if (ov) result.set(k, ov); }
    else if (eq(bv, ov)) { if (tv) result.set(k, tv); }
    else if (eq(bv, tv)) { if (ov) result.set(k, ov); }
    else return { conflict: true, treeSha: null };
  }
  return { conflict: false, treeSha: unflattenTree(repo, result) };
}
/* Evaluate a pull request's mergeability and merged tree. */
function evaluateMerge(repo, pr) {
  const baseSha = resolveRef(repo, pr.baseRef);
  const headSha = resolveRef(repo, pr.headRef) || pr.headSha;
  if (!baseSha || !headSha) return { conflict: true, treeSha: null, baseSha, headSha };
  if (isAncestor(repo, headSha, baseSha)) {
    // head already contained in base: merging is a no-op over the base tree
    return { conflict: false, treeSha: commitTreeSha(repo, baseSha), baseSha, headSha, upToDate: true };
  }
  const mb = mergeBase(repo, baseSha, headSha);
  const m = mergeTrees(repo, mb ? commitTreeSha(repo, mb) : null,
    commitTreeSha(repo, baseSha), commitTreeSha(repo, headSha));
  return { ...m, baseSha, headSha };
}
function performMerge(repo, pr, messageOverride) {
  const ev = evaluateMerge(repo, pr);
  if (ev.conflict) return null;
  let sha;
  if (ev.upToDate) {
    sha = ev.baseSha;
  } else {
    sha = buildCommit(repo, {
      tree: ev.treeSha, parents: [ev.baseSha],
      message: messageOverride || (pr.title + ' (#' + pr.number + ')'),
    });
    repo.refs.set('refs/heads/' + pr.baseRef, sha);
  }
  pr.state = 'closed';
  pr.merged = true;
  pr.mergeCommitSha = sha;
  pr.mergedAt = nowIso();
  pr.closedAt = pr.mergedAt;
  pr.updatedAt = pr.mergedAt;
  pr.headSha = ev.headSha;
  touchRepo(repo);
  return sha;
}

/* Line diff between two text blobs: LCS-based op list. */
function diffLines(aText, bText) {
  const a = aText.length ? aText.split('\n') : [];
  const b = bText.length ? bText.split('\n') : [];
  // Trim shared prefix/suffix to keep the DP small.
  let start = 0;
  while (start < a.length && start < b.length && a[start] === b[start]) start++;
  let endA = a.length, endB = b.length;
  while (endA > start && endB > start && a[endA - 1] === b[endB - 1]) { endA--; endB--; }
  const midA = a.slice(start, endA), midB = b.slice(start, endB);
  const n = midA.length, m = midB.length;
  const dp = [];
  for (let i = 0; i <= n; i++) dp.push(new Uint32Array(m + 1));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i][j] = midA[i] === midB[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const ops = [];
  for (let i = 0; i < start; i++) ops.push({ t: ' ', line: a[i] });
  let i = 0, j = 0;
  while (i < n && j < m) {
    if (midA[i] === midB[j]) { ops.push({ t: ' ', line: midA[i] }); i++; j++; }
    else if (dp[i + 1][j] >= dp[i][j + 1]) { ops.push({ t: '-', line: midA[i] }); i++; }
    else { ops.push({ t: '+', line: midB[j] }); j++; }
  }
  while (i < n) ops.push({ t: '-', line: midA[i++] });
  while (j < m) ops.push({ t: '+', line: midB[j++] });
  for (let k = endA; k < a.length; k++) ops.push({ t: ' ', line: a[k] });
  return ops;
}
function prFiles(repo, pr) {
  const baseSha = resolveRef(repo, pr.baseRef);
  const headSha = resolveRef(repo, pr.headRef) || pr.headSha;
  if (!baseSha || !headSha) return [];
  const mb = mergeBase(repo, baseSha, headSha);
  const baseFiles = flattenTree(repo, mb ? commitTreeSha(repo, mb) : null);
  const headFiles = flattenTree(repo, commitTreeSha(repo, headSha));
  const out = [];
  const keys = new Set([...baseFiles.keys(), ...headFiles.keys()]);
  for (const path of [...keys].sort()) {
    const bv = baseFiles.get(path), hv = headFiles.get(path);
    if (bv && hv && bv.sha === hv.sha) continue;
    const status = !bv ? 'added' : !hv ? 'removed' : 'modified';
    const aText = bv ? (getObject(repo, bv.sha) || { buf: Buffer.alloc(0) }).buf.toString('utf8') : '';
    const bText = hv ? (getObject(repo, hv.sha) || { buf: Buffer.alloc(0) }).buf.toString('utf8') : '';
    let additions = 0, deletions = 0, patch = null;
    if (aText.length < 200000 && bText.length < 200000 && (aText + bText).length < 200000) {
      const ops = diffLines(aText, bText);
      for (const op of ops) { if (op.t === '+') additions++; else if (op.t === '-') deletions++; }
      patch = '@@ -1,' + Math.max(1, aText ? aText.split('\n').length : 0) +
        ' +1,' + Math.max(1, bText ? bText.split('\n').length : 0) + ' @@\n' +
        ops.map((op) => op.t + op.line).join('\n');
    }
    out.push({
      sha: hv ? hv.sha : bv.sha, filename: path, status,
      additions, deletions, changes: additions + deletions,
      patch,
      previous_filename: undefined,
    });
  }
  return out;
}

/* Contents helpers */
function wrapBase64(buf) {
  const s = buf.toString('base64');
  const lines = [];
  for (let i = 0; i < s.length; i += 60) lines.push(s.slice(i, i + 60));
  return lines.join('\n') + (s.length ? '\n' : '');
}
function contentFileJson(repo, path, hit, base) {
  const full = OWNER + '/' + repo.name;
  const blob = getObject(repo, hit.sha);
  const name = path.split('/').pop();
  return {
    type: 'file', encoding: 'base64', size: blob ? blob.buf.length : 0,
    name, path, sha: hit.sha, content: blob ? wrapBase64(blob.buf) : '',
    url: base + '/api/v3/repos/' + full + '/contents/' + path,
    git_url: base + '/api/v3/repos/' + full + '/git/blobs/' + hit.sha,
    html_url: base + '/' + full + '/blob/' + repo.defaultBranch + '/' + path,
    download_url: base + '/' + full + '/raw/' + repo.defaultBranch + '/' + path,
    _links: {
      self: base + '/api/v3/repos/' + full + '/contents/' + path,
      git: base + '/api/v3/repos/' + full + '/git/blobs/' + hit.sha,
      html: base + '/' + full + '/blob/' + repo.defaultBranch + '/' + path,
    },
  };
}
function contentDirJson(repo, treeSha, prefix, base) {
  const full = OWNER + '/' + repo.name;
  const obj = getObject(repo, treeSha);
  if (!obj || obj.t !== 'tree') return [];
  return parseTree(obj.buf).map((e) => {
    const kind = entryKind(e.mode);
    const blob = kind === 'blob' ? getObject(repo, e.sha) : null;
    const p = prefix + e.name;
    return {
      type: kind === 'tree' ? 'dir' : 'file',
      size: blob ? blob.buf.length : 0,
      name: e.name, path: p, sha: e.sha,
      url: base + '/api/v3/repos/' + full + '/contents/' + p,
      git_url: base + '/api/v3/repos/' + full + '/git/' + (kind === 'tree' ? 'trees' : 'blobs') + '/' + e.sha,
      html_url: base + '/' + full + '/' + (kind === 'tree' ? 'tree' : 'blob') + '/' + repo.defaultBranch + '/' + p,
      download_url: kind === 'tree' ? null : base + '/' + full + '/raw/' + repo.defaultBranch + '/' + p,
      _links: {
        self: base + '/api/v3/repos/' + full + '/contents/' + p,
        git: base + '/api/v3/repos/' + full + '/git/' + (kind === 'tree' ? 'trees' : 'blobs') + '/' + e.sha,
        html: base + '/' + full + '/' + (kind === 'tree' ? 'tree' : 'blob') + '/' + repo.defaultBranch + '/' + p,
      },
    };
  });
}
/* Write one file (or delete with content=null) on a branch; returns commit sha. */
function writeContents(repo, branch, path, contentBuf, message, identPair) {
  const refName = 'refs/heads/' + branch;
  const tip = repo.refs.get(refName) || null;
  const files = flattenTree(repo, tip ? commitTreeSha(repo, tip) : null);
  if (contentBuf === null) files.delete(path);
  else {
    const existing = files.get(path);
    const sha = storeObject(repo, 'blob', contentBuf);
    files.set(path, { sha, mode: existing ? existing.mode : '100644' });
  }
  const tree = unflattenTree(repo, files);
  const author = identPair || forgeIdent();
  const commit = buildCommit(repo, {
    tree, parents: tip ? [tip] : [],
    message: message || (contentBuf === null ? 'Delete ' + path : 'Update ' + path),
    author, committer: author,
  });
  repo.refs.set(refName, commit);
  touchRepo(repo);
  return commit;
}

/* ------------------------------------------------------------------ */
/* REST v3                                                             */
/* ------------------------------------------------------------------ */

function sendJson(req, res, status, obj, headers) {
  const data = obj === undefined || obj === null ? '' : JSON.stringify(obj);
  res.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'X-GitHub-Request-Id': nextRequestId(),
    ...(headers || {}),
  });
  res.end(data);
}
function sendError(req, res, status, message) {
  sendJson(req, res, status, { message });
}
function pageParams(query) {
  const page = Math.max(1, parseInt(query.get('page') || '1', 10) || 1);
  const per = Math.min(100, Math.max(1, parseInt(query.get('per_page') || '30', 10) || 30));
  return { page, per };
}
function sendList(req, res, url, items) {
  const { page, per } = pageParams(url.searchParams);
  const total = items.length;
  const slice = items.slice((page - 1) * per, page * per);
  const lastPage = Math.max(1, Math.ceil(total / per));
  const links = [];
  const mk = (p) => {
    const u = new URL(url.toString());
    u.searchParams.set('page', String(p));
    u.searchParams.set('per_page', String(per));
    return '<' + u.toString() + '>';
  };
  if (page < lastPage) { links.push(mk(page + 1) + '; rel="next"'); links.push(mk(lastPage) + '; rel="last"'); }
  if (page > 1) { links.push(mk(page - 1) + '; rel="prev"'); links.push(mk(1) + '; rel="first"'); }
  sendJson(req, res, 200, slice, links.length ? { Link: links.join(', ') } : undefined);
}
function repoFromOwnerName(owner, name) {
  if (owner !== OWNER) return null;
  return reposByName.get(name) || null;
}

function handleRest(req, res, url, body, base) {
  const method = req.method;
  const path = url.pathname;
  const q = url.searchParams;

  if (path === '/api/v3' || path === '/api/v3/') {
    if (method !== 'GET') return sendError(req, res, 404, 'Not Found');
    return sendJson(req, res, 200, {
      current_user_url: base + '/api/v3/user',
      repository_url: base + '/api/v3/repos/' + OWNER + '/{repo}',
      user_repositories_url: base + '/api/v3/user/repos',
      organization_repositories_url: base + '/api/v3/orgs/{org}/repos',
      issue_search_url: base + '/api/v3/search/issues?q={query}{&page,per_page,sort,order}',
      repository_search_url: base + '/api/v3/search/repositories?q={query}{&page,per_page,sort,order}',
      emojis_url: base + '/api/v3/emojis',
      meta_url: base + '/api/v3/meta',
    }, { 'X-OAuth-Scopes': 'repo, read:org, user, admin:org' });
  }
  if (path === '/api/v3/meta' && method === 'GET') {
    return sendJson(req, res, 200, {
      verifiable_password_authentication: false,
      ssh_key_fingerprints: { SHA256_RSA: '', SHA256_ECDSA: '', SHA256_ED25519: '' },
      ssh_keys: [], hooks: [], web: [], api: [], git: [], packages: [], pages: [],
      importer: [], actions: [], dependabot: [], code_scanning: [], code_spaces: [],
      installed_version: VERSION,
    });
  }
  if (path === '/api/v3/user' && method === 'GET') return sendJson(req, res, 200, userJson(base));
  if (path === '/api/v3/user/repos') {
    if (method === 'GET') {
      const all = [...reposByName.values()].sort((a, b) => b.dbId - a.dbId);
      return sendList(req, res, url, all.map((r) => repoJson(r, base)));
    }
    if (method === 'POST') {
      const name = body && typeof body.name === 'string' ? body.name : '';
      if (!name || !/^[A-Za-z0-9._-]+$/.test(name)) {
        return sendJson(req, res, 422, { message: 'Repository creation failed.', errors: [{ resource: 'Repository', code: 'custom', field: 'name', message: 'name is not valid' }] });
      }
      if (reposByName.has(name)) {
        return sendJson(req, res, 422, { message: 'Repository creation failed.', errors: [{ resource: 'Repository', code: 'already_exists', field: 'name', message: 'name already exists on this account' }] });
      }
      const repo = makeRepo(name, body.description || '', !!body.private);
      if (body.default_branch && typeof body.default_branch === 'string') repo.defaultBranch = body.default_branch;
      if (body.auto_init) {
        const blob = storeObject(repo, 'blob', Buffer.from('# ' + name + '\n', 'utf8'));
        const tree = buildTree(repo, [{ mode: '100644', name: 'README.md', sha: blob }]);
        const commit = buildCommit(repo, { tree, parents: [], message: 'Initial commit' });
        repo.refs.set(headRef(repo), commit);
        touchRepo(repo);
      }
      return sendJson(req, res, 201, repoJson(repo, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }

  const m = /^\/api\/v3\/repos\/([^/]+)\/([^/]+)(\/.*)?$/.exec(path);
  if (!m) {
    const um = /^\/api\/v3\/users\/([^/]+)$/.exec(path);
    if (um && method === 'GET' && decodeURIComponent(um[1]) === OWNER) return sendJson(req, res, 200, userJson(base));
    return sendError(req, res, 404, 'Not Found');
  }
  const owner = decodeURIComponent(m[1]);
  const repoName = decodeURIComponent(m[2]);
  const rest = m[3] || '';
  const repo = repoFromOwnerName(owner, repoName);
  if (!repo) return sendError(req, res, 404, 'Not Found');

  if (rest === '') {
    if (method === 'GET') return sendJson(req, res, 200, repoJson(repo, base));
    if (method === 'PATCH') {
      if (body && typeof body.description === 'string') repo.description = body.description;
      if (body && typeof body.private === 'boolean') repo.private = body.private;
      if (body && typeof body.default_branch === 'string') repo.defaultBranch = body.default_branch;
      if (body && typeof body.name === 'string' && body.name !== repo.name && !reposByName.has(body.name)) {
        reposByName.delete(repo.name);
        repo.name = body.name;
        reposByName.set(repo.name, repo);
      }
      touchRepo(repo);
      return sendJson(req, res, 200, repoJson(repo, base));
    }
    if (method === 'DELETE') {
      reposByName.delete(repo.name);
      res.writeHead(204, { 'X-GitHub-Request-Id': nextRequestId() });
      return res.end();
    }
    return sendError(req, res, 404, 'Not Found');
  }

  return handleRepoRoute(req, res, url, body, base, repo, rest);
}

function handleRepoRoute(req, res, url, body, base, repo, rest) {
  const method = req.method;
  const q = url.searchParams;
  const full = OWNER + '/' + repo.name;

  if (rest === '/branches' && method === 'GET') {
    const out = [];
    for (const [ref, sha] of sortedRefs(repo)) {
      if (!ref.startsWith('refs/heads/')) continue;
      out.push({ name: ref.slice(11), commit: { sha, url: base + '/api/v3/repos/' + full + '/commits/' + sha }, protected: false });
    }
    return sendList(req, res, url, out);
  }
  if (rest.startsWith('/branches/') && method === 'GET') {
    const branch = decodeURIComponent(rest.slice(10));
    const sha = repo.refs.get('refs/heads/' + branch);
    if (!sha) return sendError(req, res, 404, 'Branch not found');
    const cj = commitJson(repo, sha, base);
    return sendJson(req, res, 200, {
      name: branch, commit: cj, protected: false,
      _links: { self: base + '/api/v3/repos/' + full + '/branches/' + branch, html: base + '/' + full + '/tree/' + branch },
    });
  }
  if (rest === '/commits' && method === 'GET') {
    const from = q.get('sha') ? resolveRef(repo, q.get('sha')) : headSha(repo);
    if (!from) return sendList(req, res, url, []);
    const all = commitsBetween(repo, from, null).map((s) => commitJson(repo, s, base));
    return sendList(req, res, url, all);
  }
  const commitMatch = /^\/commits\/([0-9a-f]{40})$/.exec(rest);
  if (commitMatch && method === 'GET') {
    const obj = getObject(repo, commitMatch[1]);
    if (!obj || obj.t !== 'commit') return sendError(req, res, 404, 'Not Found');
    return sendJson(req, res, 200, commitJson(repo, commitMatch[1], base));
  }
  if (rest === '/git/refs' && method === 'GET') {
    const out = sortedRefs(repo).map(([ref, sha]) => {
      const obj = getObject(repo, sha);
      return { ref, node_id: nodeId('Ref', full + ':' + ref), url: base + '/api/v3/repos/' + full + '/git/' + ref, object: { type: obj ? obj.t : 'commit', sha, url: base + '/api/v3/repos/' + full + '/git/commits/' + sha } };
    });
    return sendJson(req, res, 200, out);
  }
  if (rest === '/git/refs' && method === 'POST') {
    const ref = body && typeof body.ref === 'string' ? body.ref : '';
    const sha = body && typeof body.sha === 'string' ? body.sha : '';
    const obj = getObject(repo, sha);
    if (!ref.startsWith('refs/') || !obj) {
      return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Reference', code: 'custom', field: 'sha', message: 'sha is not a valid object' }] });
    }
    if (repo.refs.has(ref)) {
      return sendJson(req, res, 422, { message: 'Reference already exists', errors: [{ resource: 'Reference', code: 'custom', field: 'ref', message: 'reference already exists' }] });
    }
    repo.refs.set(ref, sha);
    touchRepo(repo);
    return sendJson(req, res, 201, {
      ref, node_id: nodeId('Ref', full + ':' + ref), url: base + '/api/v3/repos/' + full + '/git/' + ref,
      object: { type: obj.t, sha, url: base + '/api/v3/repos/' + full + '/git/commits/' + sha },
    });
  }
  if ((rest.startsWith('/git/ref/') || rest.startsWith('/git/refs/')) && method === 'GET') {
    const ref = decodeURIComponent(rest.replace(/^\/git\/refs?\//, ''));
    const fullRef = ref.startsWith('refs/') ? ref : 'refs/' + ref;
    const sha = repo.refs.get(fullRef);
    if (!sha) return sendError(req, res, 404, 'Not Found');
    const obj = getObject(repo, sha);
    return sendJson(req, res, 200, { ref: fullRef, node_id: nodeId('Ref', full + ':' + fullRef), url: base + '/api/v3/repos/' + full + '/git/' + fullRef, object: { type: obj ? obj.t : 'commit', sha, url: base + '/api/v3/repos/' + full + '/git/commits/' + sha } });
  }
  if ((rest.startsWith('/git/ref/') || rest.startsWith('/git/refs/')) && method === 'PATCH') {
    const ref = decodeURIComponent(rest.replace(/^\/git\/refs?\//, ''));
    const fullRef = ref.startsWith('refs/') ? ref : 'refs/' + ref;
    const current = repo.refs.get(fullRef);
    if (!current) return sendError(req, res, 404, 'Not Found');
    const sha = body && typeof body.sha === 'string' ? body.sha : '';
    const obj = getObject(repo, sha);
    if (!obj) return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Reference', code: 'custom', field: 'sha', message: 'sha is not a valid object' }] });
    if (!(body && body.force) && obj.t === 'commit') {
      const target = peelToCommit(repo, current) || current;
      if (!isAncestor(repo, target, sha)) {
        return sendJson(req, res, 422, { message: 'Update is not a fast-forward', errors: [{ resource: 'Reference', code: 'custom', field: 'sha', message: 'update is not a fast-forward' }] });
      }
    }
    repo.refs.set(fullRef, sha);
    touchRepo(repo);
    return sendJson(req, res, 200, { ref: fullRef, node_id: nodeId('Ref', full + ':' + fullRef), url: base + '/api/v3/repos/' + full + '/git/' + fullRef, object: { type: obj.t, sha, url: base + '/api/v3/repos/' + full + '/git/commits/' + sha } });
  }
  if ((rest.startsWith('/git/ref/') || rest.startsWith('/git/refs/')) && method === 'DELETE') {
    const ref = decodeURIComponent(rest.replace(/^\/git\/refs?\//, ''));
    const fullRef = ref.startsWith('refs/') ? ref : 'refs/' + ref;
    if (!repo.refs.has(fullRef)) return sendError(req, res, 404, 'Not Found');
    repo.refs.delete(fullRef);
    touchRepo(repo);
    res.writeHead(204, { 'X-GitHub-Request-Id': nextRequestId() });
    return res.end();
  }
  const gitCommitMatch = /^\/git\/commits\/([0-9a-f]{40})$/.exec(rest);
  if (gitCommitMatch && method === 'GET') {
    const obj = getObject(repo, gitCommitMatch[1]);
    if (!obj || obj.t !== 'commit') return sendError(req, res, 404, 'Not Found');
    const c = parseCommit(obj.buf);
    const ident = (id) => id ? { name: id.name, email: id.email, date: isoOf(id.ts) } : { name: '', email: '', date: repo.createdAt };
    return sendJson(req, res, 200, {
      sha: gitCommitMatch[1], node_id: nodeId('Commit', gitCommitMatch[1]),
      author: ident(c.author), committer: ident(c.committer), message: c.message,
      tree: { sha: c.tree, url: base + '/api/v3/repos/' + full + '/git/trees/' + c.tree },
      parents: c.parents.map((p) => ({ sha: p, url: base + '/api/v3/repos/' + full + '/git/commits/' + p })),
      url: base + '/api/v3/repos/' + full + '/git/commits/' + gitCommitMatch[1],
      verification: { verified: false, reason: 'unsigned', signature: null, payload: null },
    });
  }
  const gitTreeMatch = /^\/git\/trees\/([0-9a-f]{40})$/.exec(rest);
  if (gitTreeMatch && method === 'GET') {
    const obj = getObject(repo, gitTreeMatch[1]);
    if (!obj || obj.t !== 'tree') return sendError(req, res, 404, 'Not Found');
    let entries;
    if (q.get('recursive') === '1' || q.get('recursive') === 'true') {
      const flat = new Map();
      const walk = (treeSha, prefix) => {
        const o = getObject(repo, treeSha);
        if (!o || o.t !== 'tree') return;
        for (const e of parseTree(o.buf)) {
          const kind = entryKind(e.mode);
          const blob = kind === 'blob' ? getObject(repo, e.sha) : null;
          flat.set(prefix + e.name, { path: prefix + e.name, mode: e.mode, type: kind, sha: e.sha, size: blob ? blob.buf.length : undefined, url: base + '/api/v3/repos/' + full + '/git/' + (kind === 'tree' ? 'trees' : 'blobs') + '/' + e.sha });
          if (kind === 'tree') walk(e.sha, prefix + e.name + '/');
        }
      };
      walk(gitTreeMatch[1], '');
      entries = [...flat.values()];
    } else {
      entries = parseTree(obj.buf).map((e) => {
        const kind = entryKind(e.mode);
        const blob = kind === 'blob' ? getObject(repo, e.sha) : null;
        return { path: e.name, mode: e.mode, type: kind, sha: e.sha, size: blob ? blob.buf.length : undefined, url: base + '/api/v3/repos/' + full + '/git/' + (kind === 'tree' ? 'trees' : 'blobs') + '/' + e.sha };
      });
    }
    return sendJson(req, res, 200, { sha: gitTreeMatch[1], url: base + '/api/v3/repos/' + full + '/git/trees/' + gitTreeMatch[1], tree: entries, truncated: false });
  }
  const gitBlobMatch = /^\/git\/blobs\/([0-9a-f]{40})$/.exec(rest);
  if (gitBlobMatch && method === 'GET') {
    const obj = getObject(repo, gitBlobMatch[1]);
    if (!obj || obj.t !== 'blob') return sendError(req, res, 404, 'Not Found');
    return sendJson(req, res, 200, { sha: gitBlobMatch[1], node_id: nodeId('Blob', gitBlobMatch[1]), size: obj.buf.length, content: wrapBase64(obj.buf), encoding: 'base64', url: base + '/api/v3/repos/' + full + '/git/blobs/' + gitBlobMatch[1] });
  }

  if (rest === '/contents' || rest.startsWith('/contents/')) {
    return handleContents(req, res, url, body, base, repo, rest);
  }
  if (rest === '/labels' || rest.startsWith('/labels/')) {
    return handleLabels(req, res, url, body, base, repo, rest);
  }
  if (rest === '/issues' || rest.startsWith('/issues/')) {
    return handleIssues(req, res, url, body, base, repo, rest);
  }
  if (rest === '/pulls' || rest.startsWith('/pulls/')) {
    return handlePulls(req, res, url, body, base, repo, rest);
  }
  return sendError(req, res, 404, 'Not Found');
}

function handleContents(req, res, url, body, base, repo, rest) {
  const method = req.method;
  const q = url.searchParams;
  const rawPath = rest === '/contents' ? '' : rest.slice('/contents/'.length);
  const path = decodeURIComponent(rawPath).replace(/^\/+|\/+$/g, '');
  const refName = q.get('ref') || (body && body.branch) || repo.defaultBranch;

  if (method === 'GET') {
    const commitSha = resolveRef(repo, refName);
    const treeSha = commitSha ? commitTreeSha(repo, commitSha) : null;
    if (!treeSha) {
      if (path === '') return sendJson(req, res, 200, []);
      return sendError(req, res, 404, 'Not Found');
    }
    if (path === '') return sendJson(req, res, 200, contentDirJson(repo, treeSha, '', base));
    const hit = treeLookup(repo, treeSha, path);
    if (!hit) return sendError(req, res, 404, 'Not Found');
    if (hit.kind === 'tree') return sendJson(req, res, 200, contentDirJson(repo, hit.sha, path + '/', base));
    return sendJson(req, res, 200, contentFileJson(repo, path, hit, base));
  }
  if (method === 'PUT') {
    if (!body || typeof body.content !== 'string') return sendError(req, res, 422, 'content is required');
    const branch = (body && body.branch) || repo.defaultBranch;
    const tip = repo.refs.get('refs/heads/' + branch) || null;
    const files = flattenTree(repo, tip ? commitTreeSha(repo, tip) : null);
    const existing = files.get(path);
    if (existing && body.sha && body.sha !== existing.sha) {
      return sendJson(req, res, 409, { message: path + ' sha does not match' });
    }
    const content = Buffer.from(String(body.content).replace(/\s+/g, ''), 'base64');
    const commit = writeContents(repo, branch, path, content, body.message || 'Update ' + path);
    const newTipTree = commitTreeSha(repo, commit);
    const hit = treeLookup(repo, newTipTree, path);
    return sendJson(req, res, existing ? 200 : 201, {
      content: contentFileJson(repo, path, hit, base),
      commit: commitSummaryJson(repo, commit, base),
    });
  }
  if (method === 'DELETE') {
    const branch = (body && body.branch) || repo.defaultBranch;
    const tip = repo.refs.get('refs/heads/' + branch) || null;
    const files = flattenTree(repo, tip ? commitTreeSha(repo, tip) : null);
    const existing = files.get(path);
    if (!existing) return sendError(req, res, 404, 'Not Found');
    if (body && body.sha && body.sha !== existing.sha) {
      return sendJson(req, res, 409, { message: path + ' sha does not match' });
    }
    const commit = writeContents(repo, branch, path, null, (body && body.message) || 'Delete ' + path);
    return sendJson(req, res, 200, { content: null, commit: commitSummaryJson(repo, commit, base) });
  }
  return sendError(req, res, 404, 'Not Found');
}

function handleLabels(req, res, url, body, base, repo, rest) {
  const method = req.method;
  if (rest === '/labels') {
    if (method === 'GET') {
      const all = [...repo.labels.values()].sort((a, b) => (a.name < b.name ? -1 : 1));
      return sendList(req, res, url, all.map((l) => labelJson(repo, l, base)));
    }
    if (method === 'POST') {
      const name = body && typeof body.name === 'string' ? body.name : '';
      if (!name) return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Label', code: 'missing_field', field: 'name' }] });
      if (repo.labels.has(name)) return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Label', code: 'already_exists', field: 'name' }] });
      const label = {
        id: nextLabelDbId++, name,
        color: (body.color || 'ededed').replace(/^#/, ''),
        description: body.description || '',
      };
      repo.labels.set(name, label);
      touchRepo(repo);
      return sendJson(req, res, 201, labelJson(repo, label, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }
  const name = decodeURIComponent(rest.slice('/labels/'.length));
  const label = repo.labels.get(name);
  if (method === 'GET') {
    if (!label) return sendError(req, res, 404, 'Not Found');
    return sendJson(req, res, 200, labelJson(repo, label, base));
  }
  if (method === 'PATCH') {
    if (!label) return sendError(req, res, 404, 'Not Found');
    if (body && typeof body.new_name === 'string' && body.new_name !== name) {
      repo.labels.delete(name);
      label.name = body.new_name;
      repo.labels.set(label.name, label);
      for (const item of repo.items.values()) {
        item.labels = item.labels.map((n) => (n === name ? label.name : n));
      }
    }
    if (body && typeof body.color === 'string') label.color = body.color.replace(/^#/, '');
    if (body && typeof body.description === 'string') label.description = body.description;
    touchRepo(repo);
    return sendJson(req, res, 200, labelJson(repo, label, base));
  }
  if (method === 'DELETE') {
    if (!label) return sendError(req, res, 404, 'Not Found');
    repo.labels.delete(name);
    touchRepo(repo);
    res.writeHead(204, { 'X-GitHub-Request-Id': nextRequestId() });
    return res.end();
  }
  return sendError(req, res, 404, 'Not Found');
}

function labelNamesFrom(body, repo) {
  if (!body || body.labels === undefined) return null;
  const raw = Array.isArray(body.labels) ? body.labels : [];
  const names = raw.map((l) => (typeof l === 'string' ? l : (l && typeof l.name === 'string' ? l.name : '')));
  for (const n of names) if (!repo.labels.has(n)) return { error: n };
  return { names };
}

function handleIssues(req, res, url, body, base, repo, rest) {
  const method = req.method;
  const q = url.searchParams;
  if (rest === '/issues') {
    if (method === 'GET') {
      const state = q.get('state') || 'open';
      const labelFilter = (q.get('labels') || '').split(',').map((s) => s.trim()).filter(Boolean);
      let items = [...repo.items.values()];
      if (state !== 'all') items = items.filter((i) => i.state === state);
      if (labelFilter.length) items = items.filter((i) => labelFilter.every((n) => i.labels.includes(n)));
      if (q.get('direction') === 'asc') items.sort((a, b) => a.number - b.number);
      else items.sort((a, b) => b.number - a.number);
      return sendList(req, res, url, items.map((i) => issueJson(repo, i, base)));
    }
    if (method === 'POST') {
      if (!body || typeof body.title !== 'string' || body.title.length === 0) {
        return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Issue', code: 'missing_field', field: 'title' }] });
      }
      const ln = labelNamesFrom(body, repo);
      if (ln && ln.error !== undefined) {
        return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Issue', code: 'custom', field: 'labels', message: 'label "' + ln.error + '" does not exist' }] });
      }
      const ts = nowIso();
      const item = {
        kind: 'issue', dbId: nextIssueDbId++, number: repo.nextNumber++,
        title: body.title, body: typeof body.body === 'string' ? body.body : '',
        state: 'open', labels: ln ? ln.names : [], comments: [],
        createdAt: ts, updatedAt: ts, closedAt: null,
      };
      repo.items.set(item.number, item);
      touchRepo(repo);
      return sendJson(req, res, 201, issueJson(repo, item, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }
  const numMatch = /^\/issues\/(\d+)(\/.*)?$/.exec(rest);
  if (!numMatch) return sendError(req, res, 404, 'Not Found');
  const item = repo.items.get(parseInt(numMatch[1], 10));
  if (!item) return sendError(req, res, 404, 'Not Found');
  const sub = numMatch[2] || '';
  if (sub === '') {
    if (method === 'GET') return sendJson(req, res, 200, issueJson(repo, item, base));
    if (method === 'PATCH') {
      if (body) {
        if (typeof body.title === 'string') item.title = body.title;
        if (typeof body.body === 'string') item.body = body.body;
        if (body.state === 'open' || body.state === 'closed') {
          item.state = body.state;
          item.closedAt = body.state === 'closed' ? nowIso() : null;
        }
        const ln = labelNamesFrom(body, repo);
        if (ln && ln.error !== undefined) {
          return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'Issue', code: 'custom', field: 'labels', message: 'label "' + ln.error + '" does not exist' }] });
        }
        if (ln) item.labels = ln.names;
      }
      item.updatedAt = nowIso();
      touchRepo(repo);
      return sendJson(req, res, 200, issueJson(repo, item, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }
  if (sub === '/comments') {
    if (method === 'GET') {
      const all = [...item.comments].sort((a, b) => a.id - b.id);
      return sendList(req, res, url, all.map((c) => commentJson(repo, item, c, base)));
    }
    if (method === 'POST') {
      if (!body || typeof body.body !== 'string') return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'IssueComment', code: 'missing_field', field: 'body' }] });
      const ts = nowIso();
      const comment = { id: nextCommentDbId++, body: body.body, createdAt: ts, updatedAt: ts };
      item.comments.push(comment);
      registerComment(repo, item, comment);
      item.updatedAt = ts;
      touchRepo(repo);
      return sendJson(req, res, 201, commentJson(repo, item, comment, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }
  if (sub === '/labels' && method === 'GET') {
    return sendJson(req, res, 200, item.labels.map((n) => repo.labels.get(n)).filter(Boolean).map((l) => labelJson(repo, l, base)));
  }
  return sendError(req, res, 404, 'Not Found');
}

function handlePulls(req, res, url, body, base, repo, rest) {
  const method = req.method;
  const q = url.searchParams;
  if (rest === '/pulls') {
    if (method === 'GET') {
      const state = q.get('state') || 'open';
      let items = [...repo.items.values()].filter((i) => i.kind === 'pull');
      if (state === 'open') items = items.filter((i) => i.state === 'open');
      else if (state === 'closed') items = items.filter((i) => i.state === 'closed');
      items.sort((a, b) => b.number - a.number);
      return sendList(req, res, url, items.map((i) => prJson(repo, i, base)));
    }
    if (method === 'POST') {
      if (!body || typeof body.title !== 'string' || !body.head || !body.base) {
        return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'PullRequest', code: 'missing_field', field: 'title' }] });
      }
      let headRef = String(body.head).replace(/^refs\/heads\//, '');
      if (headRef.includes(':')) headRef = headRef.split(':').pop();
      const baseRef = String(body.base).replace(/^refs\/heads\//, '');
      const headSha = resolveRef(repo, headRef);
      const baseSha = resolveRef(repo, baseRef);
      if (!baseSha) return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'PullRequest', code: 'custom', field: 'base', message: 'base ref does not exist' }] });
      if (!headSha) return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'PullRequest', code: 'custom', field: 'head', message: 'head ref does not exist' }] });
      if (headRef === baseRef) return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'PullRequest', code: 'custom', message: 'head and base must be different' }] });
      for (const it of repo.items.values()) {
        if (it.kind === 'pull' && it.state === 'open' && it.headRef === headRef && it.baseRef === baseRef) {
          return sendJson(req, res, 422, { message: 'Validation Failed', errors: [{ resource: 'PullRequest', code: 'already_exists', message: 'A pull request already exists for ' + OWNER + ':' + headRef + ' -> ' + baseRef + '.' }] });
        }
      }
      const ts = nowIso();
      const item = {
        kind: 'pull', dbId: nextIssueDbId++, number: repo.nextNumber++,
        title: body.title, body: typeof body.body === 'string' ? body.body : '',
        state: 'open', labels: [], comments: [],
        headRef, baseRef, headSha, merged: false, mergeCommitSha: null, mergedAt: null,
        createdAt: ts, updatedAt: ts, closedAt: null,
      };
      repo.items.set(item.number, item);
      touchRepo(repo);
      return sendJson(req, res, 201, prJson(repo, item, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }
  const numMatch = /^\/pulls\/(\d+)(\/.*)?$/.exec(rest);
  if (!numMatch) return sendError(req, res, 404, 'Not Found');
  const item = repo.items.get(parseInt(numMatch[1], 10));
  if (!item || item.kind !== 'pull') return sendError(req, res, 404, 'Not Found');
  const sub = numMatch[2] || '';
  if (sub === '') {
    if (method === 'GET') {
      const out = prJson(repo, item, base);
      const files = prFiles(repo, item);
      out.commits = commitsBetween(repo, out.head.sha, out.base.sha).length;
      out.changed_files = files.length;
      out.additions = files.reduce((s, f) => s + f.additions, 0);
      out.deletions = files.reduce((s, f) => s + f.deletions, 0);
      const ev = item.state === 'open' ? evaluateMerge(repo, item) : { conflict: false };
      out.mergeable = item.merged ? true : !ev.conflict;
      out.mergeable_state = item.merged ? 'clean' : ev.conflict ? 'dirty' : 'clean';
      return sendJson(req, res, 200, out);
    }
    if (method === 'PATCH') {
      if (body) {
        if (typeof body.title === 'string') item.title = body.title;
        if (typeof body.body === 'string') item.body = body.body;
        if (body.state === 'open' || body.state === 'closed') {
          item.state = body.state;
          item.closedAt = body.state === 'closed' ? nowIso() : null;
        }
        if (typeof body.base === 'string') item.baseRef = body.base.replace(/^refs\/heads\//, '');
      }
      item.updatedAt = nowIso();
      touchRepo(repo);
      return sendJson(req, res, 200, prJson(repo, item, base));
    }
    return sendError(req, res, 404, 'Not Found');
  }
  if (sub === '/files' && method === 'GET') {
    const files = prFiles(repo, item).map((f) => {
      const out = { sha: f.sha, filename: f.filename, status: f.status, additions: f.additions, deletions: f.deletions, changes: f.changes };
      if (f.patch) out.patch = f.patch;
      out.blob_url = base + '/api/v3/repos/' + OWNER + '/' + repo.name + '/git/blobs/' + f.sha;
      out.raw_url = base + '/' + OWNER + '/' + repo.name + '/raw/' + item.headRef + '/' + f.filename;
      out.contents_url = base + '/api/v3/repos/' + OWNER + '/' + repo.name + '/contents/' + f.filename + '?ref=' + item.headRef;
      return out;
    });
    return sendList(req, res, url, files);
  }
  if (sub === '/commits' && method === 'GET') {
    const headSha = resolveRef(repo, item.headRef) || item.headSha;
    const baseSha = resolveRef(repo, item.baseRef);
    const all = commitsBetween(repo, headSha, baseSha).map((s) => commitJson(repo, s, base));
    return sendList(req, res, url, all);
  }
  if (sub === '/merge' && method === 'PUT') {
    if (item.merged) return sendJson(req, res, 405, { message: 'Pull Request has already been merged', documentation_url: '' });
    if (item.state !== 'open') return sendJson(req, res, 405, { message: 'Pull Request is not mergeable', documentation_url: '' });
    if (body && body.sha) {
      const curHead = resolveRef(repo, item.headRef) || item.headSha;
      if (body.sha !== curHead) return sendJson(req, res, 409, { message: 'Head branch was modified. Review and try the merge again.' });
    }
    const title = body && (body.commit_title || body.commit_message)
      ? (body.commit_title ? body.commit_title + (body.commit_message ? '\n\n' + body.commit_message : '') : undefined)
      : undefined;
    const sha = performMerge(repo, item, title);
    if (!sha) return sendJson(req, res, 405, { message: 'Pull Request is not mergeable', documentation_url: '' });
    return sendJson(req, res, 200, { sha, merged: true, message: 'Pull Request successfully merged' });
  }
  return sendError(req, res, 404, 'Not Found');
}

/* ------------------------------------------------------------------ */
/* GraphQL: lexer, parser, executor                                    */
/* ------------------------------------------------------------------ */

function gqlLex(src) {
  const tokens = [];
  let i = 0;
  const n = src.length;
  while (i < n) {
    const c = src[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r' || c === ',' || c === '﻿') { i++; continue; }
    if (c === '#') { while (i < n && src[i] !== '\n') i++; continue; }
    if (src.startsWith('...', i)) { tokens.push({ t: '...' }); i += 3; continue; }
    if ('!$&():=@[]{}|'.includes(c)) { tokens.push({ t: c }); i++; continue; }
    if (c === '"') {
      if (src.startsWith('"""', i)) {
        let j = i + 3;
        let out = '';
        while (j < n && !src.startsWith('"""', j)) {
          if (src[j] === '\\' && src.startsWith('"""', j + 1)) { out += '"""'; j += 4; }
          else { out += src[j]; j++; }
        }
        tokens.push({ t: 'String', v: out });
        i = j + 3;
        continue;
      }
      let j = i + 1;
      let out = '';
      while (j < n && src[j] !== '"') {
        if (src[j] === '\\') {
          const e = src[j + 1];
          if (e === 'u') { out += String.fromCharCode(parseInt(src.slice(j + 2, j + 6), 16)); j += 6; }
          else {
            out += { '"': '"', '\\': '\\', '/': '/', b: '\b', f: '\f', n: '\n', r: '\r', t: '\t' }[e] || e;
            j += 2;
          }
        } else { out += src[j]; j++; }
      }
      tokens.push({ t: 'String', v: out });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c)) {
      const m = /^-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?/.exec(src.slice(i));
      const raw = m[0];
      tokens.push({ t: (raw.includes('.') || /[eE]/.test(raw)) ? 'Float' : 'Int', v: raw });
      i += raw.length;
      continue;
    }
    if (/[_A-Za-z]/.test(c)) {
      const m = /^[_A-Za-z][_0-9A-Za-z]*/.exec(src.slice(i));
      tokens.push({ t: 'Name', v: m[0] });
      i += m[0].length;
      continue;
    }
    throw new Error('GraphQL lex error at ' + i + ': ' + JSON.stringify(c));
  }
  tokens.push({ t: 'EOF' });
  return tokens;
}

function gqlParse(src) {
  const tokens = gqlLex(src);
  let pos = 0;
  const peek = () => tokens[pos];
  const next = () => tokens[pos++];
  const expect = (t) => { const tok = next(); if (tok.t !== t) throw new Error('GraphQL parse: expected ' + t + ' got ' + tok.t); return tok; };
  const expectName = () => { const tok = next(); if (tok.t !== 'Name') throw new Error('GraphQL parse: expected Name'); return tok.v; };

  function parseValue() {
    const tok = peek();
    if (tok.t === '$') { next(); return { kind: 'var', name: expectName() }; }
    if (tok.t === 'Int') { next(); return { kind: 'int', value: parseInt(tok.v, 10) }; }
    if (tok.t === 'Float') { next(); return { kind: 'float', value: parseFloat(tok.v) }; }
    if (tok.t === 'String') { next(); return { kind: 'string', value: tok.v }; }
    if (tok.t === 'Name') {
      next();
      if (tok.v === 'true') return { kind: 'bool', value: true };
      if (tok.v === 'false') return { kind: 'bool', value: false };
      if (tok.v === 'null') return { kind: 'null', value: null };
      return { kind: 'enum', value: tok.v };
    }
    if (tok.t === '[') {
      next();
      const items = [];
      while (peek().t !== ']') items.push(parseValue());
      expect(']');
      return { kind: 'list', value: items };
    }
    if (tok.t === '{') {
      next();
      const obj = {};
      while (peek().t !== '}') {
        const name = expectName();
        expect(':');
        obj[name] = parseValue();
      }
      expect('}');
      return { kind: 'object', value: obj };
    }
    throw new Error('GraphQL parse: unexpected value token ' + tok.t);
  }
  function parseTypeRef() {
    let ref;
    if (peek().t === '[') {
      next();
      const inner = parseTypeRef();
      expect(']');
      ref = '[' + inner + ']';
    } else {
      ref = expectName();
    }
    if (peek().t === '!') { next(); ref += '!'; }
    return ref;
  }
  function parseArguments() {
    const args = {};
    if (peek().t !== '(') return args;
    next();
    while (peek().t !== ')') {
      const name = expectName();
      expect(':');
      args[name] = parseValue();
    }
    expect(')');
    return args;
  }
  function parseDirectives() {
    const dirs = [];
    while (peek().t === '@') {
      next();
      const name = expectName();
      dirs.push({ name, args: parseArguments() });
    }
    return dirs;
  }
  function parseSelectionSet() {
    expect('{');
    const sels = [];
    while (peek().t !== '}') sels.push(parseSelection());
    expect('}');
    return sels;
  }
  function parseSelection() {
    if (peek().t === '...') {
      next();
      if (peek().t === 'Name' && peek().v === 'on') {
        next();
        const typeCondition = expectName();
        const directives = parseDirectives();
        return { kind: 'inline', typeCondition, directives, selectionSet: parseSelectionSet() };
      }
      const name = expectName();
      return { kind: 'spread', name, directives: parseDirectives() };
    }
    let name = expectName();
    let alias = null;
    if (peek().t === ':') { next(); alias = name; name = expectName(); }
    const args = parseArguments();
    const directives = parseDirectives();
    let selectionSet = null;
    if (peek().t === '{') selectionSet = parseSelectionSet();
    return { kind: 'field', name, alias, args, directives, selectionSet };
  }
  function parseVariableDefinitions() {
    const defs = {};
    if (peek().t !== '(') return defs;
    next();
    while (peek().t !== ')') {
      expect('$');
      const name = expectName();
      expect(':');
      const type = parseTypeRef();
      let defaultValue;
      if (peek().t === '=') { next(); defaultValue = parseValue(); }
      parseDirectives();
      defs[name] = { type, defaultValue };
    }
    expect(')');
    return defs;
  }
  const definitions = [];
  while (peek().t !== 'EOF') {
    if (peek().t === '{') {
      definitions.push({ kind: 'operation', operation: 'query', name: null, variableDefinitions: {}, directives: [], selectionSet: parseSelectionSet() });
      continue;
    }
    const kw = expectName();
    if (kw === 'query' || kw === 'mutation' || kw === 'subscription') {
      let name = null;
      if (peek().t === 'Name') name = next().v;
      const variableDefinitions = parseVariableDefinitions();
      const directives = parseDirectives();
      definitions.push({ kind: 'operation', operation: kw, name, variableDefinitions, directives, selectionSet: parseSelectionSet() });
    } else if (kw === 'fragment') {
      const name = expectName();
      const onTok = expectName();
      if (onTok !== 'on') throw new Error('GraphQL parse: fragment missing on');
      const typeCondition = expectName();
      const directives = parseDirectives();
      definitions.push({ kind: 'fragment', name, typeCondition, directives, selectionSet: parseSelectionSet() });
    } else {
      throw new Error('GraphQL parse: unexpected definition ' + kw);
    }
  }
  return definitions;
}

function gqlValue(node, variables) {
  if (!node) return undefined;
  switch (node.kind) {
    case 'var': return variables ? variables[node.name] : undefined;
    case 'int': case 'float': case 'string': case 'bool': case 'enum': return node.value;
    case 'null': return null;
    case 'list': return node.value.map((v) => gqlValue(v, variables));
    case 'object': {
      const out = {};
      for (const [k, v] of Object.entries(node.value)) out[k] = gqlValue(v, variables);
      return out;
    }
  }
  return undefined;
}

/* Type reference strings -> introspection objects */
function gqlTypeRef(str) {
  let i = 0;
  function parse() {
    let ref;
    if (str[i] === '[') {
      i++;
      const inner = parse();
      i++; // ]
      ref = { kind: 'LIST', name: null, ofType: inner };
    } else {
      const m = /^[_A-Za-z][_0-9A-Za-z]*/.exec(str.slice(i));
      const name = m[0];
      i += name.length;
      const def = GQL_SCHEMA[name];
      ref = { kind: def ? def.kind : 'SCALAR', name, ofType: null };
    }
    if (str[i] === '!') { i++; ref = { kind: 'NON_NULL', name: null, ofType: ref }; }
    return ref;
  }
  return parse();
}

/* Connection pagination over an in-memory item list. */
function gqlConn(items, args, edgeType) {
  const total = items.length;
  let start = 0, end = total;
  const decode = (c) => {
    try { const s = b64decode(c); const m = /^cursor:(\d+)$/.exec(s); return m ? parseInt(m[1], 10) : null; } catch { return null; }
  };
  if (args && args.after != null) { const idx = decode(args.after); if (idx != null) start = Math.min(total, idx + 1); }
  if (args && args.before != null) { const idx = decode(args.before); if (idx != null) end = Math.min(end, idx); }
  let slice = items.slice(start, end);
  let hasNext = end < total, hasPrev = start > 0;
  if (args && args.first != null && slice.length > args.first) { slice = slice.slice(0, args.first); hasNext = true; }
  if (args && args.last != null && slice.length > args.last) { slice = slice.slice(slice.length - args.last); hasPrev = true; }
  const edges = slice.map((node, k) => ({ __type: edgeType, node, cursor: b64encode('cursor:' + (start + k)) }));
  return {
    __conn: true,
    totalCount: total,
    nodes: slice,
    edges,
    pageInfo: {
      __type: 'PageInfo',
      hasNextPage: hasNext, hasPreviousPage: hasPrev,
      startCursor: edges.length ? edges[0].cursor : null,
      endCursor: edges.length ? edges[edges.length - 1].cursor : null,
    },
  };
}

/* ------------------------------------------------------------------ */
/* GraphQL: domain wrappers and schema                                 */
/* ------------------------------------------------------------------ */

const commentIndex = new Map(); // comment dbId -> {repo, item, comment}
function registerComment(repo, item, comment) { commentIndex.set(comment.id, { repo, item, comment }); }

const gqlUser = () => ({ __type: 'User' });
const gqlRepo = (repo) => ({ __type: 'Repository', repo });
const gqlIssue = (repo, item) => ({ __type: 'Issue', repo, item });
const gqlPull = (repo, item) => ({ __type: 'PullRequest', repo, item });
const gqlLabel = (repo, label) => ({ __type: 'Label', repo, label });
const gqlComment = (repo, item, comment) => ({ __type: 'IssueComment', repo, item, comment });
const gqlCommit = (repo, sha) => ({ __type: 'Commit', repo, sha });
const gqlRef = (repo, refName) => ({ __type: 'Ref', repo, refName });
const gqlBlob = (repo, sha) => ({ __type: 'Blob', repo, sha });
const gqlTree = (repo, sha) => ({ __type: 'Tree', repo, sha });

function repoByDbId(dbId) {
  for (const r of reposByName.values()) if (r.dbId === dbId) return r;
  return null;
}
function gqlNodeById(id) {
  const p = parseNodeId(id);
  if (!p) return null;
  if (p.kind === 'User') return p.key === OWNER ? gqlUser() : null;
  if (p.kind === 'Repository') { const r = repoByDbId(Number(p.key)); return r ? gqlRepo(r) : null; }
  if (p.kind === 'Issue' || p.kind === 'PullRequest') {
    const [dbId, num] = p.key.split(':');
    const r = repoByDbId(Number(dbId));
    if (!r) return null;
    const item = r.items.get(Number(num));
    if (!item) return null;
    return item.kind === 'pull' ? gqlPull(r, item) : gqlIssue(r, item);
  }
  if (p.kind === 'Commit' || p.kind === 'Blob' || p.kind === 'Tree') {
    const i = p.key.indexOf(':');
    const r = repoByDbId(Number(p.key.slice(0, i)));
    if (!r) return null;
    const sha = p.key.slice(i + 1);
    if (!getObject(r, sha)) return null;
    return p.kind === 'Commit' ? gqlCommit(r, sha) : p.kind === 'Blob' ? gqlBlob(r, sha) : gqlTree(r, sha);
  }
  if (p.kind === 'Ref') {
    const i = p.key.indexOf(':');
    const r = repoByDbId(Number(p.key.slice(0, i)));
    if (!r) return null;
    const refName = p.key.slice(i + 1);
    return r.refs.has(refName) ? gqlRef(r, refName) : null;
  }
  if (p.kind === 'Label') {
    const i = p.key.indexOf(':');
    const r = repoByDbId(Number(p.key.slice(0, i)));
    if (!r) return null;
    const label = r.labels.get(p.key.slice(i + 1));
    return label ? gqlLabel(r, label) : null;
  }
  if (p.kind === 'IssueComment') {
    const rec = commentIndex.get(Number(p.key));
    return rec ? gqlComment(rec.repo, rec.item, rec.comment) : null;
  }
  return null;
}

const GQL_SCHEMA = {};
function defType(name, def) { GQL_SCHEMA[name] = def; }
function defConn(name, nodeType, extraFields) {
  const edgeName = name.replace(/Connection$/, '') + 'Edge';
  defType(name, {
    kind: 'OBJECT',
    fields: {
      totalCount: { type: 'Int', resolve: (s) => s.totalCount },
      nodes: { type: '[' + nodeType + ']', resolve: (s) => s.nodes },
      edges: { type: '[' + edgeName + ']', resolve: (s) => s.edges },
      pageInfo: { type: 'PageInfo', resolve: (s) => s.pageInfo },
      ...(extraFields || {}),
    },
  });
  defType(edgeName, {
    kind: 'OBJECT',
    fields: {
      node: { type: nodeType, resolve: (s) => s.node },
      cursor: { type: 'String!', resolve: (s) => s.cursor },
    },
  });
}

for (const s of ['String', 'Int', 'Float', 'Boolean', 'ID', 'DateTime', 'URI', 'HTML', 'GitObjectID', 'Base64String']) {
  defType(s, { kind: 'SCALAR' });
}
defType('PageInfo', {
  kind: 'OBJECT',
  fields: {
    hasNextPage: { type: 'Boolean!', resolve: (s) => !!s.hasNextPage },
    hasPreviousPage: { type: 'Boolean!', resolve: (s) => !!s.hasPreviousPage },
    startCursor: { type: 'String', resolve: (s) => s.startCursor },
    endCursor: { type: 'String', resolve: (s) => s.endCursor },
  },
});
defType('Node', { kind: 'INTERFACE', possibleTypes: ['Repository', 'Issue', 'PullRequest', 'User', 'Commit', 'Ref', 'Blob', 'Tree', 'Label', 'IssueComment'], fields: { id: { type: 'ID!' } } });
defType('Actor', { kind: 'INTERFACE', possibleTypes: ['User'], fields: { login: { type: 'String!' }, id: { type: 'ID!' }, avatarUrl: { type: 'URI!' }, resourcePath: { type: 'URI!' }, url: { type: 'URI!' } } });
defType('RepositoryOwner', { kind: 'INTERFACE', possibleTypes: ['User'], fields: { id: { type: 'ID!' }, login: { type: 'String!' }, avatarUrl: { type: 'URI!' }, resourcePath: { type: 'URI!' }, url: { type: 'URI!' } } });
defType('GitObject', { kind: 'INTERFACE', possibleTypes: ['Blob', 'Commit', 'Tag', 'Tree'], fields: { id: { type: 'ID!' }, oid: { type: 'GitObjectID!' }, abbreviatedOid: { type: 'String!' }, repository: { type: 'Repository!' } } });
defType('Labelable', { kind: 'INTERFACE', possibleTypes: ['Issue', 'PullRequest'], fields: { id: { type: 'ID!' } } });
defType('SearchResultItem', { kind: 'UNION', possibleTypes: ['Repository', 'Issue', 'PullRequest', 'User'] });
for (const [name, values] of Object.entries({
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  RepositoryOrderField: ['CREATED_AT', 'UPDATED_AT', 'PUSHED_AT', 'NAME', 'STARGAZERS'],
  SearchType: ['ISSUE', 'ISSUE_ADVANCED', 'PULL_REQUEST', 'REPOSITORY', 'USER', 'DISCUSSION'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  IssueClosedStateReason: ['COMPLETED', 'NOT_PLANNED', 'DUPLICATE'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  FileViewChangeType: ['ADDED', 'DELETED', 'MODIFIED', 'RENAMED', 'COPIED'],
  RefOrderField: ['TAG_COMMIT_DATE', 'ALPHABETICAL'],
  LabelOrderField: ['NAME', 'CREATED_AT'],
  PullRequestReviewState: ['PENDING', 'COMMENTED', 'APPROVED', 'CHANGES_REQUESTED', 'DISMISSED'],
})) defType(name, { kind: 'ENUM', enumValues: values });
for (const [name, fields] of Object.entries({
  IssueOrder: { field: 'IssueOrderField', direction: 'OrderDirection' },
  RepositoryOrder: { field: 'RepositoryOrderField', direction: 'OrderDirection' },
  RefOrder: { field: 'RefOrderField', direction: 'OrderDirection' },
  LabelOrder: { field: 'LabelOrderField', direction: 'OrderDirection' },
  CreatePullRequestInput: { clientMutationId: 'String', repositoryId: 'ID!', baseRefName: 'String!', headRefName: 'String!', title: 'String!', body: 'String', draft: 'Boolean', maintainerCanModify: 'Boolean' },
  CreateIssueInput: { clientMutationId: 'String', repositoryId: 'ID!', title: 'String!', body: 'String', labelIds: '[ID!]', assigneeIds: '[ID!]', milestoneId: 'ID', issueTemplate: 'String' },
  CloseIssueInput: { clientMutationId: 'String', issueId: 'ID!', stateReason: 'IssueClosedStateReason' },
  ReopenIssueInput: { clientMutationId: 'String', issueId: 'ID!' },
  MergePullRequestInput: { clientMutationId: 'String', pullRequestId: 'ID!', commitBody: 'String', commitHeadline: 'String', mergeMethod: 'PullRequestMergeMethod', authorEmail: 'String', expectedHeadOid: 'GitObjectID' },
  AddLabelsToLabelableInput: { clientMutationId: 'String', labelableId: 'ID!', labelIds: '[ID!]!' },
  UpdatePullRequestInput: { clientMutationId: 'String', pullRequestId: 'ID!', title: 'String', body: 'String', state: 'PullRequestState', baseRefName: 'String' },
})) {
  defType(name, {
    kind: 'INPUT_OBJECT',
    inputFields: Object.fromEntries(Object.entries(fields).map(([k, v]) => [k, { type: v }])),
  });
}
defConn('IssueConnection', 'Issue');
defConn('PullRequestConnection', 'PullRequest');
defConn('LabelConnection', 'Label');
defConn('RepositoryConnection', 'Repository');
defConn('IssueCommentConnection', 'IssueComment');
defConn('UserConnection', 'User');
defConn('RefConnection', 'Ref');
defConn('CommitConnection', 'Commit');
defConn('PullRequestCommitConnection', 'PullRequestCommit');
defConn('PullRequestFileConnection', 'PullRequestChangedFile');
defConn('PullRequestChangedFileConnection', 'PullRequestChangedFile');
defConn('SearchResultItemConnection', 'SearchResultItem', {
  issueCount: { type: 'Int!', resolve: (s) => s.issueCount || 0 },
  repositoryCount: { type: 'Int!', resolve: (s) => s.repositoryCount || 0 },
  userCount: { type: 'Int!', resolve: (s) => s.userCount || 0 },
  discussionCount: { type: 'Int!', resolve: () => 0 },
  codeCount: { type: 'Int!', resolve: () => 0 },
  wikiCount: { type: 'Int!', resolve: () => 0 },
});

function orderItems(items, orderBy, defaultDir) {
  const dir = (orderBy && orderBy.direction) || defaultDir || 'DESC';
  const sorted = [...items].sort((a, b) => a.number - b.number);
  if (dir === 'DESC') sorted.reverse();
  return sorted;
}
function stateFilter(items, states) {
  if (!states || !states.length) return items;
  const want = new Set(states.map((s) => String(s).toLowerCase()));
  return items.filter((i) => {
    const st = i.kind === 'pull' && i.merged ? 'merged' : i.state;
    return want.has(st) || (want.has('closed') && st === 'merged');
  });
}

defType('User', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: () => nodeId('User', OWNER) },
    databaseId: { type: 'Int', resolve: () => OWNER_ID },
    login: { type: 'String!', resolve: () => OWNER },
    name: { type: 'String', resolve: () => OWNER },
    email: { type: 'String!', resolve: () => '' },
    avatarUrl: { type: 'URI!', resolve: () => '' },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER },
    resourcePath: { type: 'URI!', resolve: () => '/' + OWNER },
    isViewer: { type: 'Boolean!', resolve: () => true },
    isSiteAdmin: { type: 'Boolean!', resolve: () => false },
    bio: { type: 'String', resolve: () => null },
    company: { type: 'String', resolve: () => null },
    location: { type: 'String', resolve: () => null },
    websiteUrl: { type: 'URI', resolve: () => null },
    twitterUsername: { type: 'String', resolve: () => null },
    createdAt: { type: 'DateTime!', resolve: () => isoOf(NOW_BASE) },
    updatedAt: { type: 'DateTime!', resolve: () => isoOf(NOW_BASE) },
    repositories: {
      type: 'RepositoryConnection',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, orderBy: { type: 'RepositoryOrder' } },
      resolve: (s, args) => gqlConn([...reposByName.values()].sort((a, b) => a.dbId - b.dbId).map(gqlRepo), args, 'RepositoryEdge'),
    },
    followers: { type: 'UserConnection', resolve: (s, args) => gqlConn([], args, 'UserEdge') },
    following: { type: 'UserConnection', resolve: (s, args) => gqlConn([], args, 'UserEdge') },
  },
});

defType('Repository', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Repository', s.repo.dbId) },
    databaseId: { type: 'Int', resolve: (s) => s.repo.dbId },
    name: { type: 'String!', resolve: (s) => s.repo.name },
    nameWithOwner: { type: 'String!', resolve: (s) => OWNER + '/' + s.repo.name },
    description: { type: 'String', resolve: (s) => s.repo.description || null },
    owner: { type: 'RepositoryOwner!', resolve: () => gqlUser() },
    isPrivate: { type: 'Boolean!', resolve: (s) => s.repo.private },
    isFork: { type: 'Boolean!', resolve: () => false },
    isArchived: { type: 'Boolean!', resolve: () => false },
    isTemplate: { type: 'Boolean!', resolve: () => false },
    isMirror: { type: 'Boolean!', resolve: () => false },
    isDisabled: { type: 'Boolean!', resolve: () => false },
    isEmpty: { type: 'Boolean!', resolve: (s) => !headSha(s.repo) },
    viewerPermission: { type: 'RepositoryPermission', resolve: () => 'ADMIN' },
    hasIssuesEnabled: { type: 'Boolean!', resolve: () => true },
    hasProjectsEnabled: { type: 'Boolean!', resolve: () => true },
    hasWikiEnabled: { type: 'Boolean!', resolve: () => true },
    hasDiscussionsEnabled: { type: 'Boolean!', resolve: () => false },
    defaultBranchRef: { type: 'Ref', resolve: (s) => (headSha(s.repo) ? gqlRef(s.repo, headRef(s.repo)) : null) },
    createdAt: { type: 'DateTime!', resolve: (s) => s.repo.createdAt },
    updatedAt: { type: 'DateTime!', resolve: (s) => s.repo.updatedAt },
    pushedAt: { type: 'DateTime', resolve: (s) => s.repo.updatedAt },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name },
    sshUrl: { type: 'URI!', resolve: (s) => 'git@localhost:' + OWNER + '/' + s.repo.name + '.git' },
    homepageUrl: { type: 'URI', resolve: () => null },
    stargazerCount: { type: 'Int!', resolve: () => 0 },
    forkCount: { type: 'Int!', resolve: () => 0 },
    diskUsage: { type: 'Int', resolve: () => 0 },
    primaryLanguage: { type: 'Language', resolve: () => null },
    licenseInfo: { type: 'License', resolve: () => null },
    ref: {
      type: 'Ref',
      args: { qualifiedName: { type: 'String!' } },
      resolve: (s, args) => {
        let name = String(args.qualifiedName || '');
        if (!name.startsWith('refs/')) name = 'refs/heads/' + name.replace(/^heads\//, '');
        return s.repo.refs.has(name) ? gqlRef(s.repo, name) : null;
      },
    },
    refs: {
      type: 'RefConnection',
      args: { refPrefix: { type: 'String!' }, first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, orderBy: { type: 'RefOrder' }, direction: { type: 'OrderDirection' } },
      resolve: (s, args) => {
        const prefix = args.refPrefix || 'refs/';
        const names = sortedRefs(s.repo).map(([r]) => r).filter((r) => r.startsWith(prefix));
        if (args.direction === 'DESC') names.reverse();
        return gqlConn(names.map((n) => gqlRef(s.repo, n)), args, 'RefEdge');
      },
    },
    object: {
      type: 'GitObject',
      args: { expression: { type: 'String!' }, oid: { type: 'GitObjectID' } },
      resolve: (s, args) => {
        const repo = s.repo;
        if (args.oid) {
          const o = getObject(repo, args.oid);
          if (!o) return null;
          return o.t === 'commit' ? gqlCommit(repo, args.oid) : o.t === 'tree' ? gqlTree(repo, args.oid) : o.t === 'blob' ? gqlBlob(repo, args.oid) : null;
        }
        const expr = String(args.expression || '');
        const colon = expr.indexOf(':');
        const rev = colon >= 0 ? expr.slice(0, colon) : expr;
        const path = colon >= 0 ? expr.slice(colon + 1) : '';
        const commitSha = resolveRef(repo, rev || repo.defaultBranch);
        if (!commitSha) return null;
        if (!path) return gqlCommit(repo, commitSha);
        const hit = treeLookup(repo, commitTreeSha(repo, commitSha), path);
        if (!hit) return null;
        return hit.kind === 'tree' ? gqlTree(repo, hit.sha) : gqlBlob(repo, hit.sha);
      },
    },
    issue: {
      type: 'Issue',
      args: { number: { type: 'Int!' } },
      resolve: (s, args) => {
        const item = s.repo.items.get(args.number);
        return item && item.kind === 'issue' ? gqlIssue(s.repo, item) : null;
      },
    },
    issues: {
      type: 'IssueConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, states: { type: '[IssueState!]' }, labels: { type: '[String!]' }, orderBy: { type: 'IssueOrder', default: undefined }, filterBy: { type: 'IssueFilters' } },
      resolve: (s, args) => {
        let items = [...s.repo.items.values()].filter((i) => i.kind === 'issue');
        items = stateFilter(items, args.states);
        if (args.labels && args.labels.length) items = items.filter((i) => args.labels.every((n) => i.labels.includes(n)));
        items = orderItems(items, args.orderBy, 'DESC');
        return gqlConn(items.map((i) => gqlIssue(s.repo, i)), args, 'IssueEdge');
      },
    },
    pullRequest: {
      type: 'PullRequest',
      args: { number: { type: 'Int!' } },
      resolve: (s, args) => {
        const item = s.repo.items.get(args.number);
        return item && item.kind === 'pull' ? gqlPull(s.repo, item) : null;
      },
    },
    pullRequests: {
      type: 'PullRequestConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, states: { type: '[PullRequestState!]' }, labels: { type: '[String!]' }, orderBy: { type: 'IssueOrder' }, headRefName: { type: 'String' }, baseRefName: { type: 'String' } },
      resolve: (s, args) => {
        let items = [...s.repo.items.values()].filter((i) => i.kind === 'pull');
        items = stateFilter(items, args.states);
        if (args.headRefName) items = items.filter((i) => i.headRef === args.headRefName);
        if (args.baseRefName) items = items.filter((i) => i.baseRef === args.baseRefName);
        if (args.labels && args.labels.length) items = items.filter((i) => args.labels.every((n) => i.labels.includes(n)));
        items = orderItems(items, args.orderBy, 'DESC');
        return gqlConn(items.map((i) => gqlPull(s.repo, i)), args, 'PullRequestEdge');
      },
    },
    labels: {
      type: 'LabelConnection',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, orderBy: { type: 'LabelOrder' }, query: { type: 'String' } },
      resolve: (s, args) => {
        let labels = [...s.repo.labels.values()].sort((a, b) => (a.name < b.name ? -1 : 1));
        if (args.query) labels = labels.filter((l) => l.name.includes(args.query));
        if (args.orderBy && args.orderBy.direction === 'DESC') labels.reverse();
        return gqlConn(labels.map((l) => gqlLabel(s.repo, l)), args, 'LabelEdge');
      },
    },
  },
});
defType('Language', { kind: 'OBJECT', fields: { id: { type: 'ID!' }, name: { type: 'String!' }, color: { type: 'String' } } });
defType('License', { kind: 'OBJECT', fields: { id: { type: 'ID!' }, name: { type: 'String!' }, nickname: { type: 'String' }, spdxId: { type: 'String' }, url: { type: 'URI' }, body: { type: 'String!' } } });
defType('IssueFilters', { kind: 'INPUT_OBJECT', inputFields: { assignee: { type: 'String' }, createdBy: { type: 'String' }, labels: { type: '[String!]' }, mentioned: { type: 'String' }, milestone: { type: 'String' }, since: { type: 'DateTime' }, states: { type: '[IssueState!]' }, type: { type: 'IssueType' } } });
defType('IssueType', { kind: 'ENUM', enumValues: ['ISSUE', 'PULL_REQUEST'] });

/* ------------------------------------------------------------------ */
/* GraphQL: object types                                               */
/* ------------------------------------------------------------------ */

defType('GitActor', {
  kind: 'OBJECT',
  fields: {
    name: { type: 'String!' },
    email: { type: 'String!' },
    date: { type: 'DateTime!' },
    avatarUrl: { type: 'URI!' },
    user: { type: 'User', resolve: () => null },
  },
});
function gqlActor(ident) {
  if (!ident) return null;
  return { __type: 'GitActor', name: ident.name, email: ident.email, date: isoOf(ident.ts), avatarUrl: '' };
}
defType('Label', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Label', s.repo.dbId + ':' + s.label.name) },
    name: { type: 'String!', resolve: (s) => s.label.name },
    color: { type: 'String!', resolve: (s) => s.label.color },
    description: { type: 'String', resolve: (s) => s.label.description || null },
    isDefault: { type: 'Boolean!', resolve: () => false },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/api/v3/repos/' + OWNER + '/' + s.repo.name + '/labels/' + encodeURIComponent(s.label.name) },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/labels/' + encodeURIComponent(s.label.name) },
    createdAt: { type: 'DateTime!', resolve: (s) => s.repo.createdAt },
    updatedAt: { type: 'DateTime!', resolve: (s) => s.repo.updatedAt },
  },
});
defType('IssueComment', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('IssueComment', s.comment.id) },
    databaseId: { type: 'Int', resolve: (s) => s.comment.id },
    body: { type: 'String!', resolve: (s) => s.comment.body },
    bodyText: { type: 'String!', resolve: (s) => s.comment.body },
    author: { type: 'Actor', resolve: () => gqlUser() },
    createdAt: { type: 'DateTime!', resolve: (s) => s.comment.createdAt },
    updatedAt: { type: 'DateTime!', resolve: (s) => s.comment.updatedAt },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/issues/' + s.item.number + '#issuecomment-' + s.comment.id },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/issues/' + s.item.number + '#issuecomment-' + s.comment.id },
    isMinimized: { type: 'Boolean!', resolve: () => false },
    minimizedReason: { type: 'String', resolve: () => null },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    issue: { type: 'Issue!', resolve: (s) => (s.item.kind === 'pull' ? gqlPull(s.repo, s.item) : gqlIssue(s.repo, s.item)) },
  },
});
defType('Issue', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Issue', s.repo.dbId + ':' + s.item.number) },
    databaseId: { type: 'Int', resolve: (s) => s.item.dbId },
    number: { type: 'Int!', resolve: (s) => s.item.number },
    title: { type: 'String!', resolve: (s) => s.item.title },
    titleHTML: { type: 'String!', resolve: (s) => s.item.title },
    body: { type: 'String!', resolve: (s) => s.item.body || '' },
    bodyText: { type: 'String!', resolve: (s) => s.item.body || '' },
    bodyHTML: { type: 'HTML!', resolve: (s) => s.item.body || '' },
    state: { type: 'IssueState!', resolve: (s) => s.item.state.toUpperCase() },
    stateReason: { type: 'String', resolve: () => null },
    closed: { type: 'Boolean!', resolve: (s) => s.item.state === 'closed' },
    closedAt: { type: 'DateTime', resolve: (s) => s.item.closedAt },
    createdAt: { type: 'DateTime!', resolve: (s) => s.item.createdAt },
    updatedAt: { type: 'DateTime!', resolve: (s) => s.item.updatedAt },
    author: { type: 'Actor', resolve: () => gqlUser() },
    editor: { type: 'Actor', resolve: () => null },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/issues/' + s.item.number },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/issues/' + s.item.number },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    locked: { type: 'Boolean!', resolve: () => false },
    activeLockReason: { type: 'String', resolve: () => null },
    milestone: { type: 'Milestone', resolve: () => null },
    labels: {
      type: 'LabelConnection',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, orderBy: { type: 'LabelOrder' } },
      resolve: (s, args) => gqlConn(s.item.labels.map((n) => s.repo.labels.get(n)).filter(Boolean).map((l) => gqlLabel(s.repo, l)), args, 'LabelEdge'),
    },
    comments: {
      type: 'IssueCommentConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, orderBy: { type: 'IssueCommentOrder' } },
      resolve: (s, args) => gqlConn([...s.item.comments].sort((a, b) => a.id - b.id).map((c) => gqlComment(s.repo, s.item, c)), args, 'IssueCommentEdge'),
    },
    assignees: {
      type: 'UserConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => gqlConn([], args, 'UserEdge'),
    },
    participants: {
      type: 'UserConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => gqlConn([gqlUser()], args, 'UserEdge'),
    },
  },
});
defType('Milestone', { kind: 'OBJECT', fields: { id: { type: 'ID!' }, number: { type: 'Int!' }, title: { type: 'String!' }, state: { type: 'String!' }, closed: { type: 'Boolean!' } } });
defType('IssueCommentOrder', { kind: 'INPUT_OBJECT', inputFields: { field: { type: 'IssueCommentOrderField' }, direction: { type: 'OrderDirection' } } });
defType('IssueCommentOrderField', { kind: 'ENUM', enumValues: ['UPDATED_AT'] });

defType('PullRequestChangedFile', {
  kind: 'OBJECT',
  fields: {
    path: { type: 'String!', resolve: (s) => s.path },
    additions: { type: 'Int!', resolve: (s) => s.additions },
    deletions: { type: 'Int!', resolve: (s) => s.deletions },
    changeType: { type: 'FileViewChangeType!', resolve: (s) => s.changeType },
    viewerViewedState: { type: 'String!', resolve: () => 'UNVIEWED' },
  },
});
defType('PullRequestCommit', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('PullRequestCommit', s.repo.dbId + ':' + s.sha) },
    commit: { type: 'Commit!', resolve: (s) => gqlCommit(s.repo, s.sha) },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/pull/' + (s.number || 0) + '/commits/' + s.sha },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/commit/' + s.sha },
  },
});
defType('PullRequest', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('PullRequest', s.repo.dbId + ':' + s.item.number) },
    databaseId: { type: 'Int', resolve: (s) => s.item.dbId },
    number: { type: 'Int!', resolve: (s) => s.item.number },
    title: { type: 'String!', resolve: (s) => s.item.title },
    body: { type: 'String!', resolve: (s) => s.item.body || '' },
    bodyText: { type: 'String!', resolve: (s) => s.item.body || '' },
    state: { type: 'PullRequestState!', resolve: (s) => (s.item.merged ? 'MERGED' : s.item.state.toUpperCase()) },
    merged: { type: 'Boolean!', resolve: (s) => !!s.item.merged },
    mergedAt: { type: 'DateTime', resolve: (s) => s.item.mergedAt },
    mergedBy: { type: 'Actor', resolve: (s) => (s.item.merged ? gqlUser() : null) },
    mergeable: { type: 'MergeableState!', resolve: (s) => (s.item.state !== 'open' ? 'UNKNOWN' : evaluateMerge(s.repo, s.item).conflict ? 'CONFLICTING' : 'MERGEABLE') },
    isDraft: { type: 'Boolean!', resolve: () => false },
    closed: { type: 'Boolean!', resolve: (s) => s.item.state !== 'open' },
    closedAt: { type: 'DateTime', resolve: (s) => s.item.closedAt },
    createdAt: { type: 'DateTime!', resolve: (s) => s.item.createdAt },
    updatedAt: { type: 'DateTime!', resolve: (s) => s.item.updatedAt },
    author: { type: 'Actor', resolve: () => gqlUser() },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/pull/' + s.item.number },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/pull/' + s.item.number },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    headRefName: { type: 'String!', resolve: (s) => s.item.headRef },
    baseRefName: { type: 'String!', resolve: (s) => s.item.baseRef },
    headRefOid: { type: 'GitObjectID!', resolve: (s) => resolveRef(s.repo, s.item.headRef) || s.item.headSha || ZERO_SHA },
    baseRefOid: { type: 'GitObjectID!', resolve: (s) => resolveRef(s.repo, s.item.baseRef) || ZERO_SHA },
    headRef: { type: 'Ref', resolve: (s) => (s.repo.refs.has('refs/heads/' + s.item.headRef) ? gqlRef(s.repo, 'refs/heads/' + s.item.headRef) : null) },
    baseRef: { type: 'Ref', resolve: (s) => (s.repo.refs.has('refs/heads/' + s.item.baseRef) ? gqlRef(s.repo, 'refs/heads/' + s.item.baseRef) : null) },
    headRepository: { type: 'Repository', resolve: (s) => gqlRepo(s.repo) },
    baseRepository: { type: 'Repository', resolve: (s) => gqlRepo(s.repo) },
    isCrossRepository: { type: 'Boolean!', resolve: () => false },
    mergeCommit: { type: 'Commit', resolve: (s) => (s.item.mergeCommitSha ? gqlCommit(s.repo, s.item.mergeCommitSha) : null) },
    potentialMergeCommit: { type: 'Commit', resolve: () => null },
    maintainerCanModify: { type: 'Boolean!', resolve: () => false },
    locked: { type: 'Boolean!', resolve: () => false },
    activeLockReason: { type: 'String', resolve: () => null },
    reviewDecision: { type: 'String', resolve: () => null },
    additions: { type: 'Int!', resolve: (s) => prFiles(s.repo, s.item).reduce((n, f) => n + f.additions, 0) },
    deletions: { type: 'Int!', resolve: (s) => prFiles(s.repo, s.item).reduce((n, f) => n + f.deletions, 0) },
    changedFiles: { type: 'Int!', resolve: (s) => prFiles(s.repo, s.item).length },
    labels: {
      type: 'LabelConnection',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, orderBy: { type: 'LabelOrder' } },
      resolve: (s, args) => gqlConn(s.item.labels.map((n) => s.repo.labels.get(n)).filter(Boolean).map((l) => gqlLabel(s.repo, l)), args, 'LabelEdge'),
    },
    comments: {
      type: 'IssueCommentConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => gqlConn([...s.item.comments].sort((a, b) => a.id - b.id).map((c) => gqlComment(s.repo, s.item, c)), args, 'IssueCommentEdge'),
    },
    commits: {
      type: 'PullRequestCommitConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => {
        const headSha = resolveRef(s.repo, s.item.headRef) || s.item.headSha;
        const baseSha = resolveRef(s.repo, s.item.baseRef);
        const shas = commitsBetween(s.repo, headSha, baseSha);
        return gqlConn(shas.map((sha) => ({ __type: 'PullRequestCommit', repo: s.repo, sha, number: s.item.number })), args, 'PullRequestCommitEdge');
      },
    },
    files: {
      type: 'PullRequestChangedFileConnection',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => {
        const files = prFiles(s.repo, s.item).map((f) => ({
          __type: 'PullRequestChangedFile',
          path: f.filename,
          additions: f.additions,
          deletions: f.deletions,
          changeType: f.status === 'added' ? 'ADDED' : f.status === 'removed' ? 'DELETED' : 'MODIFIED',
        }));
        return gqlConn(files, args, 'PullRequestChangedFileEdge');
      },
    },
  },
});

function commitStats(repo, sha) {
  if (!repo._statsCache) repo._statsCache = new Map();
  if (repo._statsCache.has(sha)) return repo._statsCache.get(sha);
  const obj = getObject(repo, sha);
  const c = parseCommit(obj.buf);
  const mine = flattenTree(repo, c.tree);
  const base = c.parents.length ? flattenTree(repo, commitTreeSha(repo, c.parents[0])) : new Map();
  let additions = 0, deletions = 0, changed = 0;
  const keys = new Set([...base.keys(), ...mine.keys()]);
  for (const k of keys) {
    const bv = base.get(k), mv = mine.get(k);
    if (bv && mv && bv.sha === mv.sha) continue;
    changed++;
    const aText = bv ? (getObject(repo, bv.sha) || { buf: Buffer.alloc(0) }).buf.toString('utf8') : '';
    const bText = mv ? (getObject(repo, mv.sha) || { buf: Buffer.alloc(0) }).buf.toString('utf8') : '';
    if (aText.length < 200000 && bText.length < 200000) {
      for (const op of diffLines(aText, bText)) { if (op.t === '+') additions++; else if (op.t === '-') deletions++; }
    }
  }
  const out = { additions, deletions, changedFiles: changed };
  repo._statsCache.set(sha, out);
  return out;
}
defType('Commit', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Commit', s.repo.dbId + ':' + s.sha) },
    oid: { type: 'GitObjectID!', resolve: (s) => s.sha },
    abbreviatedOid: { type: 'String!', resolve: (s) => s.sha.slice(0, 7) },
    message: { type: 'String!', resolve: (s) => parseCommit(getObject(s.repo, s.sha).buf).message },
    messageHeadline: { type: 'String!', resolve: (s) => (parseCommit(getObject(s.repo, s.sha).buf).message.split('\n')[0] || '') },
    messageBody: { type: 'String!', resolve: (s) => { const m = parseCommit(getObject(s.repo, s.sha).buf).message; const i = m.indexOf('\n\n'); return i >= 0 ? m.slice(i + 2) : ''; } },
    committedDate: { type: 'DateTime!', resolve: (s) => { const c = parseCommit(getObject(s.repo, s.sha).buf); return isoOf((c.committer || c.author).ts); } },
    authoredDate: { type: 'DateTime!', resolve: (s) => { const c = parseCommit(getObject(s.repo, s.sha).buf); return isoOf((c.author || c.committer).ts); } },
    author: { type: 'GitActor', resolve: (s) => gqlActor(parseCommit(getObject(s.repo, s.sha).buf).author) },
    committer: { type: 'GitActor', resolve: (s) => gqlActor(parseCommit(getObject(s.repo, s.sha).buf).committer) },
    tree: { type: 'Tree!', resolve: (s) => gqlTree(s.repo, parseCommit(getObject(s.repo, s.sha).buf).tree) },
    treeOid: { type: 'GitObjectID!', resolve: (s) => parseCommit(getObject(s.repo, s.sha).buf).tree },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/commit/' + s.sha },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/commit/' + s.sha },
    additions: { type: 'Int!', resolve: (s) => commitStats(s.repo, s.sha).additions },
    deletions: { type: 'Int!', resolve: (s) => commitStats(s.repo, s.sha).deletions },
    changedFiles: { type: 'Int!', resolve: (s) => commitStats(s.repo, s.sha).changedFiles },
    changedFilesIfAvailable: { type: 'Int', resolve: (s) => commitStats(s.repo, s.sha).changedFiles },
    parents: {
      type: 'CommitConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => gqlConn(parseCommit(getObject(s.repo, s.sha).buf).parents.map((p) => gqlCommit(s.repo, p)), args, 'CommitEdge'),
    },
    signature: { type: 'GitSignature', resolve: () => null },
  },
});
defType('GitSignature', { kind: 'INTERFACE', possibleTypes: [], fields: { isValid: { type: 'Boolean!' }, payload: { type: 'String!' }, signature: { type: 'String!' }, state: { type: 'String!' }, signer: { type: 'User' } } });
defType('Ref', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Ref', s.repo.dbId + ':' + s.refName) },
    name: { type: 'String!', resolve: (s) => s.refName.replace(/^refs\/(heads|tags)\//, '') },
    prefix: { type: 'String!', resolve: (s) => s.refName.slice(0, s.refName.length - s.refName.replace(/^refs\/(heads|tags)\//, '').length) },
    qualifiedName: { type: 'String!', resolve: (s) => s.refName },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    target: {
      type: 'GitObject',
      resolve: (s) => {
        const sha = s.repo.refs.get(s.refName);
        const o = sha ? getObject(s.repo, sha) : null;
        if (!o) return null;
        return o.t === 'commit' ? gqlCommit(s.repo, sha) : o.t === 'tree' ? gqlTree(s.repo, sha) : o.t === 'blob' ? gqlBlob(s.repo, sha) : { __type: 'Tag', repo: s.repo, sha, name: s.refName.replace(/^refs\/tags\//, '') };
      },
    },
    associatedPullRequests: {
      type: 'PullRequestConnection!',
      args: { first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' }, states: { type: '[PullRequestState!]' }, orderBy: { type: 'IssueOrder' } },
      resolve: (s, args) => {
        const short = s.refName.replace(/^refs\/heads\//, '');
        let items = [...s.repo.items.values()].filter((i) => i.kind === 'pull' && i.headRef === short);
        items = stateFilter(items, args.states);
        items = orderItems(items, args.orderBy, 'DESC');
        return gqlConn(items.map((i) => gqlPull(s.repo, i)), args, 'PullRequestEdge');
      },
    },
  },
});
defType('Tag', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Tag', s.repo.dbId + ':' + s.sha) },
    oid: { type: 'GitObjectID!', resolve: (s) => s.sha },
    abbreviatedOid: { type: 'String!', resolve: (s) => s.sha.slice(0, 7) },
    name: { type: 'String!', resolve: (s) => s.name || '' },
    message: { type: 'String', resolve: (s) => { const t = getObject(s.repo, s.sha).buf.toString('utf8'); const i = t.indexOf('\n\n'); return i >= 0 ? t.slice(i + 2) : ''; } },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    target: {
      type: 'GitObject',
      resolve: (s) => {
        const m = /^object ([0-9a-f]{40})/m.exec(getObject(s.repo, s.sha).buf.toString('utf8'));
        if (!m) return null;
        const o = getObject(s.repo, m[1]);
        if (!o) return null;
        return o.t === 'commit' ? gqlCommit(s.repo, m[1]) : o.t === 'tree' ? gqlTree(s.repo, m[1]) : gqlBlob(s.repo, m[1]);
      },
    },
    tagger: { type: 'GitActor', resolve: (s) => { const m = /^tagger (.*)$/m.exec(getObject(s.repo, s.sha).buf.toString('utf8')); return m ? gqlActor(parseIdent(m[1])) : null; } },
  },
});
defType('Blob', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Blob', s.repo.dbId + ':' + s.sha) },
    oid: { type: 'GitObjectID!', resolve: (s) => s.sha },
    abbreviatedOid: { type: 'String!', resolve: (s) => s.sha.slice(0, 7) },
    byteSize: { type: 'Int!', resolve: (s) => getObject(s.repo, s.sha).buf.length },
    isTruncated: { type: 'Boolean!', resolve: () => false },
    isBinary: { type: 'Boolean!', resolve: (s) => getObject(s.repo, s.sha).buf.subarray(0, 8000).includes(0) },
    text: { type: 'String', resolve: (s) => getObject(s.repo, s.sha).buf.toString('utf8') },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/blob/' + s.sha },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/blob/' + s.sha },
    commitResourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/commit/' + s.sha },
    commitUrl: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/commit/' + s.sha },
  },
});
defType('TreeEntry', {
  kind: 'OBJECT',
  fields: {
    name: { type: 'String!', resolve: (s) => s.entry.name },
    path: { type: 'String!', resolve: (s) => s.entry.name },
    type: { type: 'String!', resolve: (s) => entryKind(s.entry.mode) },
    mode: { type: 'Int!', resolve: (s) => parseInt(s.entry.mode, 10) },
    extension: { type: 'String', resolve: (s) => { const i = s.entry.name.lastIndexOf('.'); return i > 0 ? s.entry.name.slice(i) : null; } },
    isGenerated: { type: 'Boolean!', resolve: () => false },
    size: { type: 'Int', resolve: (s) => { const o = getObject(s.repo, s.entry.sha); return o && o.t === 'blob' ? o.buf.length : null; } },
    oid: { type: 'GitObjectID!', resolve: (s) => s.entry.sha },
    object: {
      type: 'GitObject',
      resolve: (s) => {
        const o = getObject(s.repo, s.entry.sha);
        if (!o) return null;
        return o.t === 'tree' ? gqlTree(s.repo, s.entry.sha) : o.t === 'commit' ? gqlCommit(s.repo, s.entry.sha) : gqlBlob(s.repo, s.entry.sha);
      },
    },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
  },
});
defType('Tree', {
  kind: 'OBJECT',
  fields: {
    id: { type: 'ID!', resolve: (s) => nodeId('Tree', s.repo.dbId + ':' + s.sha) },
    oid: { type: 'GitObjectID!', resolve: (s) => s.sha },
    abbreviatedOid: { type: 'String!', resolve: (s) => s.sha.slice(0, 7) },
    repository: { type: 'Repository!', resolve: (s) => gqlRepo(s.repo) },
    entries: { type: '[TreeEntry!]!', resolve: (s) => parseTree(getObject(s.repo, s.sha).buf).map((entry) => ({ __type: 'TreeEntry', repo: s.repo, entry })) },
    resourcePath: { type: 'URI!', resolve: (s) => '/' + OWNER + '/' + s.repo.name + '/tree/' + s.sha },
    url: { type: 'URI!', resolve: (s, a, ctx) => ctx.base + '/' + OWNER + '/' + s.repo.name + '/tree/' + s.sha },
  },
});

/* ------------------------------------------------------------------ */
/* GraphQL: Query, Mutation, introspection, executor                   */
/* ------------------------------------------------------------------ */

function gqlSearch(args) {
  const tokens = String(args.query || '').split(/\s+/).filter(Boolean);
  let repoFilter = null;
  const terms = [];
  for (const t of tokens) {
    const ci = t.indexOf(':');
    if (ci > 0) {
      const k = t.slice(0, ci), v = t.slice(ci + 1);
      if (k === 'repo') { repoFilter = v.split('/').pop(); continue; }
      if (['type', 'is', 'state', 'label', 'author', 'in', 'sort', 'archived', 'fork', 'language', 'user', 'org', 'milestone', 'review', 'created', 'updated', 'comments', 'interactions', 'reactions'].includes(k)) continue;
    }
    terms.push(t.toLowerCase());
  }
  const matchText = (text) => terms.every((term) => String(text).toLowerCase().includes(term));
  const allRepos = [...reposByName.values()].filter((r) => !repoFilter || r.name === repoFilter);
  const issues = [], pulls = [], repoMatches = [];
  for (const r of allRepos) {
    if (matchText(r.name + ' ' + (r.description || ''))) repoMatches.push(gqlRepo(r));
    for (const item of r.items.values()) {
      if (!matchText(item.title + ' ' + (item.body || ''))) continue;
      if (item.kind === 'issue') issues.push(gqlIssue(r, item));
      else pulls.push(gqlPull(r, item));
    }
  }
  const type = args.type || 'ISSUE';
  let items = [];
  if (type === 'ISSUE' || type === 'ISSUE_ADVANCED') items = issues;
  else if (type === 'PULL_REQUEST') items = pulls;
  else if (type === 'REPOSITORY') items = repoMatches;
  else if (type === 'USER') items = (terms.length === 0 || matchText(OWNER)) ? [gqlUser()] : [];
  const conn = gqlConn(items, args, 'SearchResultItemEdge');
  conn.__type = 'SearchResultItemConnection';
  conn.issueCount = issues.length;
  conn.repositoryCount = repoMatches.length;
  conn.userCount = (terms.length === 0 || matchText(OWNER)) ? 1 : 0;
  return conn;
}

defType('RateLimit', {
  kind: 'OBJECT',
  fields: {
    limit: { type: 'Int!' },
    cost: { type: 'Int!' },
    remaining: { type: 'Int!' },
    used: { type: 'Int!' },
    resetAt: { type: 'DateTime!' },
    nodeCount: { type: 'Int!' },
  },
});
defType('Query', {
  kind: 'OBJECT',
  fields: {
    repository: {
      type: 'Repository',
      args: { owner: { type: 'String!' }, name: { type: 'String!' }, followRenames: { type: 'Boolean' } },
      resolve: (s, args) => {
        if (args.owner !== OWNER) return null;
        const r = reposByName.get(args.name);
        return r ? gqlRepo(r) : null;
      },
    },
    repositoryOwner: {
      type: 'RepositoryOwner',
      args: { login: { type: 'String!' } },
      resolve: (s, args) => (args.login === OWNER ? gqlUser() : null),
    },
    user: {
      type: 'User',
      args: { login: { type: 'String!' } },
      resolve: (s, args) => (args.login === OWNER ? gqlUser() : null),
    },
    organization: {
      type: 'Organization',
      args: { login: { type: 'String!' } },
      resolve: () => null,
    },
    viewer: { type: 'User!', resolve: () => gqlUser() },
    node: {
      type: 'Node',
      args: { id: { type: 'ID!' } },
      resolve: (s, args) => gqlNodeById(args.id),
    },
    nodes: {
      type: '[Node]!',
      args: { ids: { type: '[ID!]!' } },
      resolve: (s, args) => (args.ids || []).map((id) => gqlNodeById(id)),
    },
    search: {
      type: 'SearchResultItemConnection!',
      args: { query: { type: 'String!' }, type: { type: 'SearchType!' }, first: { type: 'Int' }, after: { type: 'String' }, last: { type: 'Int' }, before: { type: 'String' } },
      resolve: (s, args) => gqlSearch(args),
    },
    rateLimit: {
      type: 'RateLimit',
      args: { dryRun: { type: 'Boolean' } },
      resolve: () => ({ __type: 'RateLimit', limit: 5000, cost: 1, remaining: 4999, used: 1, resetAt: isoOf(NOW_BASE + 3600), nodeCount: 0 }),
    },
  },
});
defType('Organization', { kind: 'OBJECT', fields: { id: { type: 'ID!' }, login: { type: 'String!' }, name: { type: 'String' } } });

function normalizeBranchName(ref) {
  let r = String(ref || '').replace(/^refs\/heads\//, '');
  if (r.includes(':')) r = r.split(':').pop();
  return r;
}
function createPullItem(repo, { title, body, headRef, baseRef }) {
  const headSha = resolveRef(repo, headRef);
  const ts = nowIso();
  const item = {
    kind: 'pull', dbId: nextIssueDbId++, number: repo.nextNumber++,
    title, body: body || '', state: 'open', labels: [], comments: [],
    headRef, baseRef, headSha, merged: false, mergeCommitSha: null, mergedAt: null,
    createdAt: ts, updatedAt: ts, closedAt: null,
  };
  repo.items.set(item.number, item);
  touchRepo(repo);
  return item;
}
defType('AddCommentPayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, commentEdge: { type: 'IssueCommentEdge' }, subject: { type: 'Node' } } });
defType('CreatePullRequestPayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, pullRequest: { type: 'PullRequest' } } });
defType('CreateIssuePayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, issue: { type: 'Issue' } } });
defType('CloseIssuePayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, issue: { type: 'Issue' } } });
defType('ReopenIssuePayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, issue: { type: 'Issue' } } });
defType('MergePullRequestPayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, pullRequest: { type: 'PullRequest' } } });
defType('AddLabelsToLabelablePayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, labelable: { type: 'Labelable' } } });
defType('UpdatePullRequestPayload', { kind: 'OBJECT', fields: { clientMutationId: { type: 'String' }, pullRequest: { type: 'PullRequest' } } });
defType('Mutation', {
  kind: 'OBJECT',
  fields: {
    createPullRequest: {
      type: 'CreatePullRequestPayload',
      args: { input: { type: 'CreatePullRequestInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.repositoryId);
        if (!target || target.__type !== 'Repository') throw new Error('Repository not found');
        const repo = target.repo;
        const headRef = normalizeBranchName(input.headRefName);
        const baseRef = normalizeBranchName(input.baseRefName);
        if (!resolveRef(repo, baseRef)) throw new Error('Base ref does not exist');
        if (!resolveRef(repo, headRef)) throw new Error('Head ref does not exist');
        const item = createPullItem(repo, { title: input.title || '', body: input.body || '', headRef, baseRef });
        return { __type: 'CreatePullRequestPayload', clientMutationId: input.clientMutationId ?? null, pullRequest: gqlPull(repo, item) };
      },
    },
    createIssue: {
      type: 'CreateIssuePayload',
      args: { input: { type: 'CreateIssueInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.repositoryId);
        if (!target || target.__type !== 'Repository') throw new Error('Repository not found');
        const repo = target.repo;
        const labels = [];
        for (const lid of input.labelIds || []) {
          const ln = gqlNodeById(lid);
          if (!ln || ln.__type !== 'Label') throw new Error('Label not found');
          labels.push(ln.label.name);
        }
        const ts = nowIso();
        const item = {
          kind: 'issue', dbId: nextIssueDbId++, number: repo.nextNumber++,
          title: input.title || '', body: input.body || '', state: 'open',
          labels, comments: [], createdAt: ts, updatedAt: ts, closedAt: null,
        };
        repo.items.set(item.number, item);
        touchRepo(repo);
        return { __type: 'CreateIssuePayload', clientMutationId: input.clientMutationId ?? null, issue: gqlIssue(repo, item) };
      },
    },
    closeIssue: {
      type: 'CloseIssuePayload',
      args: { input: { type: 'CloseIssueInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.issueId);
        if (!target || (target.__type !== 'Issue' && target.__type !== 'PullRequest')) throw new Error('Issue not found');
        target.item.state = 'closed';
        target.item.closedAt = nowIso();
        target.item.updatedAt = target.item.closedAt;
        touchRepo(target.repo);
        return { __type: 'CloseIssuePayload', clientMutationId: input.clientMutationId ?? null, issue: gqlIssue(target.repo, target.item) };
      },
    },
    reopenIssue: {
      type: 'ReopenIssuePayload',
      args: { input: { type: 'ReopenIssueInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.issueId);
        if (!target || (target.__type !== 'Issue' && target.__type !== 'PullRequest')) throw new Error('Issue not found');
        target.item.state = 'open';
        target.item.closedAt = null;
        target.item.updatedAt = nowIso();
        touchRepo(target.repo);
        return { __type: 'ReopenIssuePayload', clientMutationId: input.clientMutationId ?? null, issue: gqlIssue(target.repo, target.item) };
      },
    },
    mergePullRequest: {
      type: 'MergePullRequestPayload',
      args: { input: { type: 'MergePullRequestInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.pullRequestId);
        if (!target || target.__type !== 'PullRequest') throw new Error('Pull request not found');
        const pr = target.item;
        if (pr.merged || pr.state !== 'open') throw new Error('Pull Request is not mergeable');
        const message = input.commitHeadline ? input.commitHeadline + (input.commitBody ? '\n\n' + input.commitBody : '') : undefined;
        const sha = performMerge(target.repo, pr, message);
        if (!sha) throw new Error('Pull Request is not mergeable');
        return { __type: 'MergePullRequestPayload', clientMutationId: input.clientMutationId ?? null, pullRequest: gqlPull(target.repo, pr) };
      },
    },
    addLabelsToLabelable: {
      type: 'AddLabelsToLabelablePayload',
      args: { input: { type: 'AddLabelsToLabelableInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.labelableId);
        if (!target || (target.__type !== 'Issue' && target.__type !== 'PullRequest')) throw new Error('Labelable not found');
        for (const lid of input.labelIds || []) {
          const ln = gqlNodeById(lid);
          if (!ln || ln.__type !== 'Label') throw new Error('Label not found');
          if (!target.item.labels.includes(ln.label.name)) target.item.labels.push(ln.label.name);
        }
        target.item.updatedAt = nowIso();
        touchRepo(target.repo);
        return { __type: 'AddLabelsToLabelablePayload', clientMutationId: input.clientMutationId ?? null, labelable: target };
      },
    },
    updatePullRequest: {
      type: 'UpdatePullRequestPayload',
      args: { input: { type: 'UpdatePullRequestInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.pullRequestId);
        if (!target || target.__type !== 'PullRequest') throw new Error('Pull request not found');
        const pr = target.item;
        if (typeof input.title === 'string') pr.title = input.title;
        if (typeof input.body === 'string') pr.body = input.body;
        if (input.state === 'OPEN') { pr.state = 'open'; pr.closedAt = null; }
        if (input.state === 'CLOSED') { pr.state = 'closed'; pr.closedAt = nowIso(); }
        if (typeof input.baseRefName === 'string') pr.baseRef = normalizeBranchName(input.baseRefName);
        pr.updatedAt = nowIso();
        touchRepo(target.repo);
        return { __type: 'UpdatePullRequestPayload', clientMutationId: input.clientMutationId ?? null, pullRequest: gqlPull(target.repo, pr) };
      },
    },
    addComment: {
      type: 'AddCommentPayload',
      args: { input: { type: 'AddCommentInput!' } },
      resolve: (s, args) => {
        const input = args.input || {};
        const target = gqlNodeById(input.subjectId);
        if (!target || (target.__type !== 'Issue' && target.__type !== 'PullRequest')) throw new Error('Subject not found');
        const ts = nowIso();
        const comment = { id: nextCommentDbId++, body: typeof input.body === 'string' ? input.body : '', createdAt: ts, updatedAt: ts };
        target.item.comments.push(comment);
        target.item.updatedAt = ts;
        registerComment(target.repo, target.item, comment);
        touchRepo(target.repo);
        return {
          __type: 'AddCommentPayload',
          clientMutationId: input.clientMutationId ?? null,
          commentEdge: { __type: 'IssueCommentEdge', node: gqlComment(target.repo, target.item, comment), cursor: b64encode('cursor:0') },
          subject: target,
        };
      },
    },
  },
});

/* Introspection */
defType('__TypeKind', { kind: 'ENUM', enumValues: ['SCALAR', 'OBJECT', 'INTERFACE', 'UNION', 'ENUM', 'INPUT_OBJECT', 'LIST', 'NON_NULL'] });
defType('__DirectiveLocation', { kind: 'ENUM', enumValues: ['QUERY', 'MUTATION', 'SUBSCRIPTION', 'FIELD', 'FRAGMENT_DEFINITION', 'FRAGMENT_SPREAD', 'INLINE_FRAGMENT', 'VARIABLE_DEFINITION', 'SCHEMA', 'SCALAR', 'OBJECT', 'FIELD_DEFINITION', 'ARGUMENT_DEFINITION', 'INTERFACE', 'UNION', 'ENUM', 'ENUM_VALUE', 'INPUT_OBJECT', 'INPUT_FIELD_DEFINITION'] });
function gqlLiteral(v) {
  if (v === undefined) return null;
  if (v === null) return 'null';
  if (typeof v === 'string') return JSON.stringify(v);
  if (typeof v === 'number' || typeof v === 'boolean') return String(v);
  if (Array.isArray(v)) return '[' + v.map(gqlLiteral).join(', ') + ']';
  if (typeof v === 'object') return '{' + Object.entries(v).map(([k, x]) => k + ': ' + gqlLiteral(x)).join(', ') + '}';
  return String(v);
}
function gqlTypeObject(name) {
  const def = GQL_SCHEMA[name];
  if (!def) return null;
  return { __type: '__Type', name, def };
}
function gqlRefTypeObject(ref) { return { __type: '__Type', ref }; }
defType('__Type', {
  kind: 'OBJECT',
  fields: {
    kind: { type: '__TypeKind!', resolve: (s) => (s.ref ? s.ref.kind : s.def.kind) },
    name: { type: 'String', resolve: (s) => (s.ref ? s.ref.name : s.name) },
    description: { type: 'String', resolve: () => null },
    specifiedByURL: { type: 'String', resolve: () => null },
    isOneOf: { type: 'Boolean', resolve: () => false },
    fields: {
      type: '[__Field!]',
      args: { includeDeprecated: { type: 'Boolean', default: false } },
      resolve: (s, args) => {
        if (s.ref || !s.def || !s.def.fields) return null;
        return Object.entries(s.def.fields)
          .filter(([, f]) => args.includeDeprecated || !f.deprecated)
          .map(([n, f]) => ({ __type: '__Field', name: n, def: f }));
      },
    },
    inputFields: {
      type: '[__InputValue!]',
      args: { includeDeprecated: { type: 'Boolean', default: false } },
      resolve: (s) => {
        if (s.ref || !s.def || !s.def.inputFields) return null;
        return Object.entries(s.def.inputFields).map(([n, f]) => ({ __type: '__InputValue', name: n, def: f }));
      },
    },
    enumValues: {
      type: '[__EnumValue!]',
      args: { includeDeprecated: { type: 'Boolean', default: false } },
      resolve: (s) => {
        if (s.ref || !s.def || !s.def.enumValues) return null;
        return s.def.enumValues.map((n) => ({ __type: '__EnumValue', name: n }));
      },
    },
    possibleTypes: {
      type: '[__Type!]',
      resolve: (s) => {
        if (s.ref || !s.def || !s.def.possibleTypes) return null;
        return s.def.possibleTypes.map((n) => gqlTypeObject(n)).filter(Boolean);
      },
    },
    ofType: { type: '__Type', resolve: (s) => (s.ref && s.ref.ofType ? gqlRefTypeObject(s.ref.ofType) : null) },
    interfaces: { type: '[__Type!]!', resolve: () => [] },
  },
});
defType('__Field', {
  kind: 'OBJECT',
  fields: {
    name: { type: 'String!', resolve: (s) => s.name },
    description: { type: 'String', resolve: () => null },
    args: {
      type: '[__InputValue!]!',
      args: { includeDeprecated: { type: 'Boolean', default: false } },
      resolve: (s) => Object.entries(s.def.args || {}).map(([n, f]) => ({ __type: '__InputValue', name: n, def: f })),
    },
    type: { type: '__Type!', resolve: (s) => gqlRefTypeObject(gqlTypeRef(s.def.type)) },
    isDeprecated: { type: 'Boolean!', resolve: (s) => !!s.def.deprecated },
    deprecationReason: { type: 'String', resolve: () => null },
  },
});
defType('__InputValue', {
  kind: 'OBJECT',
  fields: {
    name: { type: 'String!', resolve: (s) => s.name },
    description: { type: 'String', resolve: () => null },
    type: { type: '__Type!', resolve: (s) => gqlRefTypeObject(gqlTypeRef(s.def.type)) },
    defaultValue: { type: 'String', resolve: (s) => gqlLiteral(s.def.default) },
    isDeprecated: { type: 'Boolean!', resolve: () => false },
    deprecationReason: { type: 'String', resolve: () => null },
  },
});
defType('__EnumValue', {
  kind: 'OBJECT',
  fields: {
    name: { type: 'String!', resolve: (s) => s.name },
    description: { type: 'String', resolve: () => null },
    isDeprecated: { type: 'Boolean!', resolve: () => false },
    deprecationReason: { type: 'String', resolve: () => null },
  },
});
const GQL_DIRECTIVES = [
  { name: 'include', locations: ['FIELD', 'FRAGMENT_SPREAD', 'INLINE_FRAGMENT'], args: { if: { type: 'Boolean!' } }, isRepeatable: false },
  { name: 'skip', locations: ['FIELD', 'FRAGMENT_SPREAD', 'INLINE_FRAGMENT'], args: { if: { type: 'Boolean!' } }, isRepeatable: false },
  { name: 'deprecated', locations: ['FIELD_DEFINITION', 'ARGUMENT_DEFINITION', 'INPUT_FIELD_DEFINITION', 'ENUM_VALUE'], args: { reason: { type: 'String', default: 'No longer supported' } }, isRepeatable: false },
  { name: 'specifiedBy', locations: ['SCALAR'], args: { url: { type: 'String!' } }, isRepeatable: false },
  { name: 'oneOf', locations: ['INPUT_OBJECT'], args: {}, isRepeatable: false },
];
defType('__Directive', {
  kind: 'OBJECT',
  fields: {
    name: { type: 'String!', resolve: (s) => s.name },
    description: { type: 'String', resolve: () => null },
    locations: { type: '[__DirectiveLocation!]!', resolve: (s) => s.locations },
    args: { type: '[__InputValue!]!', resolve: (s) => Object.entries(s.args || {}).map(([n, f]) => ({ __type: '__InputValue', name: n, def: f })) },
    isRepeatable: { type: 'Boolean!', resolve: (s) => !!s.isRepeatable },
  },
});
defType('__Schema', {
  kind: 'OBJECT',
  fields: {
    description: { type: 'String', resolve: () => null },
    types: { type: '[__Type!]!', resolve: () => Object.keys(GQL_SCHEMA).map((n) => gqlTypeObject(n)).filter(Boolean) },
    queryType: { type: '__Type!', resolve: () => gqlTypeObject('Query') },
    mutationType: { type: '__Type', resolve: () => gqlTypeObject('Mutation') },
    subscriptionType: { type: '__Type', resolve: () => null },
    directives: { type: '[__Directive!]!', resolve: () => GQL_DIRECTIVES.map((d) => ({ __type: '__Directive', ...d })) },
  },
});

/* Executor */
function gqlDirectivesPass(directives, variables) {
  for (const d of directives || []) {
    const args = {};
    for (const [k, v] of Object.entries(d.args || {})) args[k] = gqlValue(v, variables);
    if (d.name === 'skip' && args.if === true) return false;
    if (d.name === 'include' && args.if === false) return false;
  }
  return true;
}
function gqlTypeMatches(runtimeType, condition) {
  if (!condition) return true;
  if (runtimeType === condition) return true;
  const def = GQL_SCHEMA[condition];
  if (def && (def.kind === 'INTERFACE' || def.kind === 'UNION')) return (def.possibleTypes || []).includes(runtimeType);
  return false;
}
function gqlCollectFields(source, selectionSet, fragments, variables) {
  const map = new Map();
  const runtimeType = source && source.__type;
  const visit = (sels, stack) => {
    for (const sel of sels || []) {
      if (!gqlDirectivesPass(sel.directives, variables)) continue;
      if (sel.kind === 'field') {
        const key = sel.alias || sel.name;
        if (!map.has(key)) map.set(key, []);
        map.get(key).push(sel);
      } else if (sel.kind === 'spread') {
        if (stack.has(sel.name)) continue;
        const frag = fragments[sel.name];
        if (!frag) continue;
        if (!gqlTypeMatches(runtimeType, frag.typeCondition)) continue;
        visit(frag.selectionSet, new Set([...stack, sel.name]));
      } else if (sel.kind === 'inline') {
        if (sel.typeCondition && !gqlTypeMatches(runtimeType, sel.typeCondition)) continue;
        visit(sel.selectionSet, stack);
      }
    }
  };
  visit(selectionSet, new Set());
  return map;
}
function gqlCoerceArgs(node, variables, fieldDef) {
  const out = {};
  if (fieldDef && fieldDef.args) {
    for (const [k, d] of Object.entries(fieldDef.args)) if (d.default !== undefined) out[k] = d.default;
  }
  for (const [k, v] of Object.entries(node.args || {})) out[k] = gqlValue(v, variables);
  return out;
}
function gqlExecSelectionSet(typeName, source, selectionSet, fragments, variables, ctx, errors, path) {
  const fields = gqlCollectFields(source, selectionSet, fragments, variables);
  const out = {};
  for (const [respKey, nodes] of fields) {
    out[respKey] = gqlResolveField(typeName, source, nodes, fragments, variables, ctx, errors, [...path, respKey]);
  }
  return out;
}
function gqlResolveField(typeName, source, nodes, fragments, variables, ctx, errors, path) {
  const node = nodes[0];
  const fname = node.name;
  if (fname === '__typename') return (source && source.__type) || typeName;
  if (typeName === 'Query' && fname === '__type') {
    const args = gqlCoerceArgs(node, variables, null);
    const value = args.name ? gqlTypeObject(args.name) : null;
    const merged = { selectionSet: nodes.flatMap((n) => n.selectionSet || []) };
    return gqlCompleteRef(gqlTypeRef('__Type'), value, merged, fragments, variables, ctx, errors, path);
  }
  if (typeName === 'Query' && fname === '__schema') {
    const merged = { selectionSet: nodes.flatMap((n) => n.selectionSet || []) };
    return gqlCompleteRef(gqlTypeRef('__Schema'), { __type: '__Schema' }, merged, fragments, variables, ctx, errors, path);
  }
  const typeDef = GQL_SCHEMA[typeName];
  const fieldDef = typeDef && typeDef.fields ? typeDef.fields[fname] : undefined;
  if (!fieldDef) {
    errors.push({ message: "Field '" + fname + "' doesn't exist on type '" + typeName + "'", path });
    return null;
  }
  const args = gqlCoerceArgs(node, variables, fieldDef);
  let value;
  try {
    value = fieldDef.resolve ? fieldDef.resolve(source, args, ctx) : (source ? source[fname] : undefined);
  } catch (e) {
    errors.push({ message: String((e && e.message) || e), path });
    return null;
  }
  const merged = { selectionSet: nodes.flatMap((n) => n.selectionSet || []) };
  return gqlCompleteRef(gqlTypeRef(fieldDef.type), value, merged, fragments, variables, ctx, errors, path);
}
function gqlCompleteRef(ref, value, node, fragments, variables, ctx, errors, path) {
  if (ref.kind === 'NON_NULL') {
    const v = gqlCompleteRef(ref.ofType, value, node, fragments, variables, ctx, errors, path);
    if (v === null || v === undefined) errors.push({ message: 'Cannot return null for non-nullable field', path });
    return v == null ? null : v;
  }
  if (value === null || value === undefined) return null;
  if (ref.kind === 'LIST') {
    const arr = Array.isArray(value) ? value : [value];
    return arr.map((v, i) => gqlCompleteRef(ref.ofType, v, node, fragments, variables, ctx, errors, [...path, i]));
  }
  const def = GQL_SCHEMA[ref.name];
  if (!def || def.kind === 'SCALAR') {
    if (ref.name === 'ID') return String(value);
    if (ref.name === 'Int') return typeof value === 'number' ? Math.trunc(value) : value;
    if (ref.name === 'Float') return typeof value === 'number' ? value : value;
    if (ref.name === 'Boolean') return !!value;
    return value;
  }
  if (def.kind === 'ENUM') return value;
  const runtimeType = value.__type || ref.name;
  if (!node.selectionSet || node.selectionSet.length === 0) return {};
  return gqlExecSelectionSet(runtimeType, value, node.selectionSet, fragments, variables, ctx, errors, path);
}
function gqlHandleOne(b, ctx) {
  if (!b || typeof b.query !== 'string') return { errors: [{ message: 'Must provide query string' }] };
  let defs;
  try { defs = gqlParse(b.query); }
  catch (e) { return { errors: [{ message: String((e && e.message) || e) }] }; }
  const fragments = {};
  const ops = [];
  for (const d of defs) {
    if (d.kind === 'fragment') fragments[d.name] = d;
    else ops.push(d);
  }
  let selected = ops;
  if (b.operationName) selected = ops.filter((o) => o.name === b.operationName);
  if (!selected.length) return { errors: [{ message: 'Operation not found' }] };
  const results = selected.map((op) => {
    const vars = { ...(b.variables || {}) };
    for (const [vn, vd] of Object.entries(op.variableDefinitions || {})) {
      if (vars[vn] === undefined && vd.defaultValue) vars[vn] = gqlValue(vd.defaultValue, vars);
    }
    const errors = [];
    const rootType = op.operation === 'mutation' ? 'Mutation' : 'Query';
    const data = gqlExecSelectionSet(rootType, { __type: rootType }, op.selectionSet, fragments, vars, ctx, errors, []);
    const out = { data };
    if (errors.length) out.errors = errors;
    return out;
  });
  return results.length === 1 ? results[0] : results;
}
function gqlHandle(bodyObj, ctx) {
  if (Array.isArray(bodyObj)) return bodyObj.map((b) => gqlHandleOne(b, ctx));
  return gqlHandleOne(bodyObj, ctx);
}

/* ------------------------------------------------------------------ */
/* MCP (JSON-RPC 2.0 over streamable HTTP)                             */
/* ------------------------------------------------------------------ */

const MCP_PROTOCOL_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The name of the new repository.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by its owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        full_name: { type: 'string', description: 'The full name of the repository, as owner/repo.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create a new issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        title: { type: 'string', description: 'The title of the issue.' },
        body: { type: 'string', description: 'The body of the issue.' },
        labels: { type: 'array', items: { type: 'string' }, description: 'Labels to apply to the issue.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository, newest first.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        title: { type: 'string', description: 'The title of the pull request.' },
        body: { type: 'string', description: 'The body of the pull request.' },
        head: { type: 'string', description: 'The name of the branch to merge from.' },
        base: { type: 'string', description: 'The name of the branch to merge into.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by squashing its changes onto its base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        pull_number: { type: 'number', description: 'The number of the pull request to merge.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpToolResult(obj) {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], isError: false };
}
function mcpToolError(message) {
  return { content: [{ type: 'text', text: String(message) }], isError: true };
}
function mcpRepoFromArgs(args) {
  let owner = args.owner;
  let name = args.repo;
  if ((owner === undefined || name === undefined) && typeof args.full_name === 'string') {
    const parts = args.full_name.split('/');
    if (parts.length === 2) {
      if (owner === undefined) owner = parts[0];
      if (name === undefined) name = parts[1];
    }
  }
  if (owner === undefined || name === undefined) return null;
  return repoFromOwnerName(String(owner), String(name));
}

function mcpCallTool(name, args, base) {
  if (name === 'create_repo') {
    const repoName = String(args.name);
    if (!/^[A-Za-z0-9._-]+$/.test(repoName)) return mcpToolError('name is not valid');
    if (reposByName.has(repoName)) return mcpToolError('name already exists on this account');
    const repo = makeRepo(repoName, typeof args.description === 'string' ? args.description : '', !!args.private);
    return mcpToolResult(repoJson(repo, base));
  }
  if (name === 'get_repo') {
    const repo = mcpRepoFromArgs(args);
    if (!repo) return mcpToolError('repository not found');
    return mcpToolResult(repoJson(repo, base));
  }
  if (name === 'create_issue') {
    const repo = mcpRepoFromArgs(args);
    if (!repo) return mcpToolError('repository not found');
    if (typeof args.title !== 'string' || args.title.length === 0) return mcpToolError('title is required');
    let labelNames = [];
    if (args.labels !== undefined) {
      const ln = labelNamesFrom({ labels: args.labels }, repo);
      if (ln && ln.error !== undefined) return mcpToolError('label "' + ln.error + '" does not exist');
      if (ln) labelNames = ln.names;
    }
    const ts = nowIso();
    const item = {
      kind: 'issue', dbId: nextIssueDbId++, number: repo.nextNumber++,
      title: args.title, body: typeof args.body === 'string' ? args.body : '',
      state: 'open', labels: labelNames, comments: [],
      createdAt: ts, updatedAt: ts, closedAt: null,
    };
    repo.items.set(item.number, item);
    touchRepo(repo);
    return mcpToolResult(issueJson(repo, item, base));
  }
  if (name === 'list_issues') {
    const repo = mcpRepoFromArgs(args);
    if (!repo) return mcpToolError('repository not found');
    const state = typeof args.state === 'string' ? args.state : 'open';
    let items = [...repo.items.values()].filter((i) => i.kind === 'issue');
    if (state !== 'all') items = items.filter((i) => i.state === state);
    items.sort((a, b) => b.number - a.number);
    return mcpToolResult(items.map((i) => issueJson(repo, i, base)));
  }
  if (name === 'create_pull_request') {
    const repo = mcpRepoFromArgs(args);
    if (!repo) return mcpToolError('repository not found');
    const headRef = normalizeBranchName(args.head);
    const baseRef = normalizeBranchName(args.base);
    if (!resolveRef(repo, baseRef)) return mcpToolError('base ref does not exist');
    if (!resolveRef(repo, headRef)) return mcpToolError('head ref does not exist');
    if (headRef === baseRef) return mcpToolError('head and base must be different');
    for (const it of repo.items.values()) {
      if (it.kind === 'pull' && it.state === 'open' && it.headRef === headRef && it.baseRef === baseRef) {
        return mcpToolError('a pull request already exists for ' + headRef + ' -> ' + baseRef);
      }
    }
    const item = createPullItem(repo, {
      title: String(args.title), body: typeof args.body === 'string' ? args.body : '', headRef, baseRef,
    });
    return mcpToolResult(prJson(repo, item, base));
  }
  if (name === 'merge_pull_request') {
    const repo = mcpRepoFromArgs(args);
    if (!repo) return mcpToolError('repository not found');
    const item = repo.items.get(Math.trunc(Number(args.pull_number)));
    if (!item || item.kind !== 'pull') return mcpToolError('pull request not found');
    if (item.merged) return mcpToolError('Pull Request has already been merged');
    if (item.state !== 'open') return mcpToolError('Pull Request is not mergeable');
    const sha = performMerge(repo, item);
    if (!sha) return mcpToolError('Pull Request is not mergeable');
    return mcpToolResult({ sha, merged: true, message: 'Pull Request successfully merged' });
  }
  return mcpToolError('unknown tool: ' + name);
}

function mcpRpcError(id, code, message) {
  return { jsonrpc: '2.0', id, error: { code, message } };
}

/* One JSON-RPC message in, one response object out (null = notification). */
function mcpHandleOne(msg, base) {
  if (!msg || typeof msg !== 'object') return mcpRpcError(null, -32600, 'Invalid Request');
  const isNotification = msg.id === undefined || msg.id === null;
  const id = isNotification ? null : msg.id;
  const method = typeof msg.method === 'string' ? msg.method : '';
  const params = msg.params && typeof msg.params === 'object' ? msg.params : {};
  if (method === 'server/discover') {
    return {
      jsonrpc: '2.0', id,
      result: {
        protocolVersion: '2026-07-28',
        supportedVersions: MCP_PROTOCOL_VERSIONS,
        capabilities: { tools: { listChanged: false } },
        serverInfo: { name: 'makeforge', version: VERSION },
      },
    };
  }
  if (method === 'initialize') {
    const want = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
    const version = MCP_PROTOCOL_VERSIONS.includes(want) ? want : '2025-11-25';
    return {
      jsonrpc: '2.0', id,
      result: {
        protocolVersion: version,
        capabilities: { tools: { listChanged: false } },
        serverInfo: { name: 'makeforge', version: VERSION },
      },
    };
  }
  if (method === 'ping') return { jsonrpc: '2.0', id, result: {} };
  if (method === 'tools/list') return { jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } };
  if (method === 'tools/call') {
    const rawName = typeof params.name === 'string' ? params.name : '';
    const tool = MCP_TOOLS.find((t) => t.name === rawName)
      || MCP_TOOLS.find((t) => rawName.toLowerCase().endsWith(t.name.toLowerCase()));
    if (!tool) return mcpRpcError(id, -32602, 'unknown tool: ' + rawName);
    const args = params.arguments && typeof params.arguments === 'object' ? params.arguments : {};
    for (const reqName of tool.inputSchema.required || []) {
      if (args[reqName] === undefined || args[reqName] === null || args[reqName] === '') {
        return mcpRpcError(id, -32602, 'missing required argument: ' + reqName);
      }
    }
    try {
      return { jsonrpc: '2.0', id, result: mcpCallTool(tool.name, args, base) };
    } catch (e) {
      return { jsonrpc: '2.0', id, result: mcpToolError((e && e.message) || String(e)) };
    }
  }
  if (isNotification) return null;
  return mcpRpcError(id, -32601, 'method not found: ' + method);
}

function handleMcp(req, res, raw, base) {
  if (req.method !== 'POST') {
    res.writeHead(405, { 'Content-Type': 'application/json; charset=utf-8', 'X-GitHub-Request-Id': nextRequestId() });
    res.end(JSON.stringify({ message: 'Method Not Allowed' }));
    return;
  }
  if (!req.headers.authorization) {
    res.writeHead(401, { 'Content-Type': 'application/json; charset=utf-8', 'X-GitHub-Request-Id': nextRequestId() });
    res.end(JSON.stringify({ message: 'Unauthorized' }));
    return;
  }
  let parsed;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch (e) {
    res.writeHead(400, { 'Content-Type': 'application/json; charset=utf-8' });
    res.end(JSON.stringify(mcpRpcError(null, -32700, 'Parse error')));
    return;
  }
  if (Array.isArray(parsed)) {
    const out = [];
    for (const msg of parsed) {
      const r = mcpHandleOne(msg, base);
      if (r) out.push(r);
    }
    res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8' });
    res.end(JSON.stringify(out));
    return;
  }
  const result = mcpHandleOne(parsed, base);
  if (result === null) {
    res.writeHead(202, { 'Content-Type': 'application/json; charset=utf-8' });
    res.end('');
    return;
  }
  res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8' });
  res.end(JSON.stringify(result));
}

/* ------------------------------------------------------------------ */
/* HTTP routing                                                        */
/* ------------------------------------------------------------------ */

function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    req.on('data', (c) => chunks.push(c));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function isAuthed(req) {
  if (!TOKEN) return true;
  return req.headers.authorization === 'Bearer ' + TOKEN;
}

async function handleRequest(req, res) {
  const base = 'http://' + (req.headers.host || 'localhost');
  let url;
  try {
    url = new URL(req.url, base);
  } catch (e) {
    return sendError(req, res, 400, 'Bad Request');
  }
  const path = url.pathname;
  const raw = await readBody(req);

  if (path === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8' });
    res.end('{"ok":true}');
    return;
  }

  if (path === '/mcp') return handleMcp(req, res, raw, base);

  if (path === '/api/graphql') {
    if (req.method !== 'POST') return sendError(req, res, 404, 'Not Found');
    if (!isAuthed(req)) return sendError(req, res, 401, 'Bad credentials');
    let bodyObj;
    try {
      bodyObj = JSON.parse(raw.toString('utf8'));
    } catch (e) {
      return sendError(req, res, 400, 'Invalid JSON');
    }
    return sendJson(req, res, 200, gqlHandle(bodyObj, { base }));
  }

  if (path === '/api/v3' || path.startsWith('/api/v3/')) {
    if (!isAuthed(req)) return sendError(req, res, 401, 'Bad credentials');
    let bodyObj = {};
    if (raw.length) {
      try {
        bodyObj = JSON.parse(raw.toString('utf8'));
      } catch (e) {
        return sendError(req, res, 400, 'Problems parsing JSON');
      }
      if (bodyObj === null || bodyObj === undefined) bodyObj = {};
    }
    return handleRest(req, res, url, bodyObj, base);
  }

  const gm = /^\/([^/]+)\/([^/]+)\.git(\/.*)?$/.exec(path);
  if (gm) {
    const owner = decodeURIComponent(gm[1]);
    const repoName = decodeURIComponent(gm[2]);
    const sub = gm[3] || '';
    const repo = repoFromOwnerName(owner, repoName);
    if (sub === '/info/refs' && req.method === 'GET') {
      const service = url.searchParams.get('service');
      if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
        return sendError(req, res, 400, 'Bad Request');
      }
      if (!repo) return sendError(req, res, 404, 'Not Found');
      const proto = req.headers['git-protocol'] || '';
      return handleInfoRefs(req, res, repo, service, proto.includes('version=2'));
    }
    if (sub === '/git-upload-pack' && req.method === 'POST') {
      if (!repo) return sendError(req, res, 404, 'Not Found');
      const proto = req.headers['git-protocol'] || '';
      const looksV2 = proto.includes('version=2')
        || (raw.length > 12 && raw.toString('utf8', 4, 12) === 'command=');
      if (looksV2) return handleUploadPackV2(repo, raw, res);
      return handleUploadPackV0(repo, raw, res);
    }
    if (sub === '/git-receive-pack' && req.method === 'POST') {
      if (!repo) return sendError(req, res, 404, 'Not Found');
      return handleReceivePack(repo, raw, res);
    }
    return sendError(req, res, 404, 'Not Found');
  }

  return sendError(req, res, 404, 'Not Found');
}

/* ------------------------------------------------------------------ */
/* Boot: bind, register with the suite, long-poll /done, exit          */
/* ------------------------------------------------------------------ */

function envRequest(method, pathName, payload) {
  return new Promise((resolve, reject) => {
    const u = new URL(ENV_URL + pathName);
    const lib = u.protocol === 'https:' ? require('node:https') : http;
    const data = payload ? Buffer.from(JSON.stringify(payload), 'utf8') : null;
    const r = lib.request({
      method,
      hostname: u.hostname,
      port: u.port || (u.protocol === 'https:' ? 443 : 80),
      path: u.pathname,
      headers: data ? { 'Content-Type': 'application/json', 'Content-Length': data.length } : {},
    }, (resp) => {
      const chunks = [];
      resp.on('data', (c) => chunks.push(c));
      resp.on('end', () => resolve({ status: resp.statusCode, body: Buffer.concat(chunks).toString('utf8') }));
    });
    r.on('error', reject);
    if (data) r.write(data);
    r.end();
  });
}

function sleep(ms) { return new Promise((r) => setTimeout(r, ms)); }

const server = http.createServer((req, res) => {
  handleRequest(req, res).catch(() => {
    try {
      if (!res.headersSent) sendError(req, res, 500, 'Internal Server Error');
      else res.end();
    } catch (e) { /* the socket is gone; nothing to answer on */ }
  });
});
server.keepAliveTimeout = 30000;
server.headersTimeout = 60000;

async function boot() {
  await new Promise((resolve) => server.listen(0, resolve));
  const address = server.address();
  const port = address && typeof address === 'object' ? address.port : 0;
  if (!ENV_URL) {
    console.error('makeforge: listening on port ' + port + ' (MAKEFUN_ENV_URL unset; serving without the suite)');
    return;
  }
  for (;;) {
    try {
      const r = await envRequest('POST', '/register', { port });
      if (r.status >= 200 && r.status < 300) break;
      if (r.status === 409) break; // the first register wins; ours already landed
    } catch (e) { /* the suite is still coming up; retry */ }
    await sleep(100);
  }
  for (;;) {
    let done = false;
    try {
      const r = await envRequest('GET', '/done');
      if (r.status === 200) {
        const j = JSON.parse(r.body);
        done = !!(j && j.done);
      }
    } catch (e) { /* transient; keep polling */ }
    if (done) break;
    await sleep(100);
  }
  server.close();
  process.exit(0);
}

boot();

