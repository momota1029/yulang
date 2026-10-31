# R85 admission and dispatcher adjudication

Admitted by Luna under the standing ongoing `research/simple-sub-intrusion` authorization. Fixed parent goal and scope remain unchanged.

- Baseline branch/commit: `yulang3` / `c4e594fc64d72dba30a73c64fcbf258eaebdfc32`.
- Contract: `tasks/agent-loop/sprints/native-root-premises-20261031-r85.md`, SHA-256 `d12c5cf57d89b043677cb43f4122898ab17f5cb843c9e9dd648d3731a4ab3420`.
- Input manifest: `tasks/agent-loop/sprints/native-root-premises-20261031-r85-inputs.json`, SHA-256 `db94797269f3c50840a3d89235b75007452e02a9400442c67ac2fe755aadc549`.
- Dispatcher result: recommend R85 to derive or falsify, from the native producer, the exact source premises used by accepted R84. The concrete challenge is native uniqueness by occurrence+typed pair versus R57/R84 state/relation-ID and route selectors under `RelationKey` interning and separate Origin insertion. Method: constructor induction over relation interning and Origin/drain publication, preserving all competing records; falsifier must be producer-reachable.
- Fixed resources: 4,800 seconds (source 1,000; proof 1,800; review 1,000; primary 1,000 incl. 500 closeout), Astra 0; at most two exact authorized Lean stdin calls of <=120 sec each and <=240 sec total under `-j1 -M1024`.
- Authority: source lane is read-only; proof lane writes only the assigned Lean module and proof handoff; source/proof lanes run in parallel; no Rust edits, tests, builds, caches, scratch, environments or worktrees.
- Original A/B, authenticated source/native extraction, full ancestry, whole-language and production gates remain OPEN.
