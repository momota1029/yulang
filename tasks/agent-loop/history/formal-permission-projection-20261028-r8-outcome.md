# Formal Permission Projection r8 outcome

Sprint lane: `FORMAL-PERMISSION-PROJECTION-20261028/r8`
Baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`
Disposition: **review accepted conditional local source evidence with exact obstruction; no forest premise or parent gate closed.**

## Frozen records

- Original contract: `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8.md` — SHA-256 `99835a8d22b3b61c90500706245fd5e28aeee238905cca1eb217d8c2f274cd46`.
- First source STOP (stale outcome pin): `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8.md` — SHA-256 `e9926aaf56c8ea35b1227b7c27693f7c14eb872a46b8b6826ca6cda46951a4c8`.
- Amendment 01: `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-01.md` — SHA-256 `3c2782ff6e375b4f22278ead3d7f5834b4d2d291f83ab6b9b7b68624c2b040d1`.
- Amendment source handoff: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r2.md` — SHA-256 `19bffa5c2fdfdd38d8205dc1368b61b475811acaf2d00073cccbda0f6fecb8c9`.
- Independent review: `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r2.md` — SHA-256 `6ff6c8e8a9c343c93aaf673903b69acce4633f0df52a035844b1af6f9870f99a`.
- Corrected r7 outcome dependency: `tasks/agent-loop/history/formal-permission-projection-20261028-r7-outcome.md` — SHA-256 `7fab9c3f7bbe4c6072702b30973e44c705122aa244877addd1ff4d2a9a65eef8`.

The first contract had a stale SHA because the primary removed trailing Markdown hard-break spaces from the new r7 outcome after recording its earlier hash, updated `current.json`, but omitted refreshing the contract pin. The first researcher stopped correctly before semantic analysis; its full 200-second grant remains charged. Amendment 01 recorded the cause, preserved the old contract/stop note, corrected the pin and authorized a fresh distinct output path and a separate 470-second reservation.

## Accepted scope and exact obstruction

A fresh non-author `compiler_referee` accepted the amended source note with no BLOCKING, major or minor findings. All amendment, stop-note, r7 and nine admitted source/policy hashes matched.

The source note inventories local production writes to the ValueRow and EffectRow forests: default empty state, self-parent births, root links, path compression, reverse journal restoration, and truncation. It derives valid conditional lemmas: births preserve a closed finite forest; lookup is terminating and idempotent under that invariant (including missing-entry fallback, which does not prove row validity); linking distinct in-range self-roots preserves the forest if they remain roots at the write; compression preserves roots; and complete, correctly ordered inverse replay can restore a closed checkpoint prefix before truncation. These are conditional local facts, not universal reachable-state preservation.

The first missing direct callee body on the visible bound-copy path is `candidate_opposite_count` at `candidate_intrusion.rs:639`. Its declaration owner/signature are unresolved within the admitted union and no new owner was opened or searched. The prospective inverse entry at `:624–630` precedes intervening helpers, so root stability and journal ordering cannot be inferred from the enclosing mutable receiver.

Exact remaining equation: if distinct, in-range same-kind roots `r,s` are selected at `candidate_intrusion.rs:613–619`, then immediately before `:679/:691` both entries still exist and satisfy `F(r)=r` and `F(s)=s`, and every effective intervening forest mutation has its correctly ordered inverse entry for the associated checkpoint. The reviewer confirmed this boundary and noted that source declaration ownership and transitive journal/resource helpers remain open.

No r7 premise is removed. B's transitive construction/parameter/domain/store/export association, D's successful capture/export, global/reachable forest and lifetime preservation, r1 Lean, original parent A/B, source/native, full inference/executor, and production gates all remain OPEN. No reachable counterexample or successful wrong-image export was established.

## Checks, resources and integration

Only static source reads and SHA authentication were performed. No tests, probes, builds, Cargo, Lean/Lake, Git or compiler edits were made by either worker/reviewer. `python3 tools/agent_sprint.py check` passed after current-state synchronization; this is static consistency evidence only.

First r8 source grant: full 200 seconds charged for the dependency mismatch stop. Amendment source grant: 159 seconds observed, but full 200 seconds charged; CPU/RSS UNKNOWN. Review grant: full 120 seconds charged; exact runtime/CPU/RSS UNKNOWN. Prior sprint charges remain intact. Conservative reserved/charged bound through amendment is 5,440 of 7,200 seconds, leaving 1,760 seconds unless an earlier omitted grant is discovered.

Relevant commits pushed to `origin/yulang3`: `42debe702` (r7 outcome and r8 admission), `6f568c4c7` (stale-pin adjudication, r8 amendment and stop record), `f06c6594e` (amendment worker launch), `2ef6d8cc2` (r8-r2 source handoff and review launch). Quarantined/foreign runtime files and pending Lean artifacts were not staged or changed.

Next action: consult the dispatcher for the minimum exact helper declaration owner and an admissible bounded source packet. No source authority is granted by this outcome.
