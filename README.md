# git-forge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/hikambanjir-netizen/git-forge/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/hikambanjir-netizen/git-forge/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone GitHub-compatible git forge in a single Node process, built on the Node 22 standard library alone — no npm dependencies, no git binary. It keeps its own in-memory object store and speaks four surfaces at once:

- **Git smart HTTP** — protocol v0 and v2 (`ls-refs` with symrefs/peel/ref-prefix, `fetch` with shallow, deepen, thin-pack and OFS deltas, `receive-pack` with report-status), including pack parsing/building, delta application and annotated tags.
- **REST API v3** — repositories, contents, git database (blobs, trees, commits, refs), issues, labels, pull requests (including merges), search and pagination with `Link` headers.
- **GraphQL API v4** — a hand-rolled parser and executor with connections, node IDs, mutations (create/close/reopen issues, pull requests, `addComment`, labels) and full introspection.
- **MCP** — `server/discover`, `initialize`, `ping`, `tools/list` and `tools/call` over the same store.

On boot it binds an ephemeral port, registers it with the harness environment (`POST $MAKEFUN_ENV_URL/register`), serves until the environment reports done, and exits 0. API surfaces require `Authorization: Bearer $MAKEFUN_SHOP_TOKEN`.

## Run it

```sh
MAKEFUN_ENV_URL=http://127.0.0.1:PORT MAKEFUN_SHOP_TOKEN=<token> node main.ts
```

---

<sub>Entered on [make.fun](https://make.fun/?ref=dfkzjsa3&utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
