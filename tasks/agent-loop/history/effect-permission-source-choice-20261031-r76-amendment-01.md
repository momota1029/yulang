# R76 amendment 01 — complete the Lean import pins

This amendment corrects an incomplete source manifest before any R76 Lean audit. The R1 source set omitted `ProviderEntryArrivalR48.lean` and the transitive R66 import path `ReachedSlotSearchR58.lean`, `ReachedSlotCompletenessR59.lean`, `NativeLocalDecodeR60.lean`, and `BoundedAncestryR61.lean`; R1 also predates the frozen R76 module. No Lean audit was executed under R1.

R2 supersedes R1 as the active input manifest and pins all six files by SHA-256. The primary independently reconstructed the exact 15-module depth-first flattened stdin in memory: 444,759 bytes, SHA-256 `378bda8a94ad50d74f5e1a576813d80d98192f4aa69747e5948e7e14f8ebbf5d`. This matched the proof handoff proposal. The exact traversal, removed import-line rule, footer, theorem/axiom query list, pinned Lean executable, command, environment, timeout and no-output policy are retained in the proof handoff.

Amendment 01 does not change the fixed outcome, leases, semantics, success gate, execution cap or closure boundary. It authorizes no audit by itself. Audit 1 remains `FROZEN_NOT_AUTHORIZED` until the primary commits R2, this amendment, and a current-state receipt that binds all bytes/command/output policy and explicitly authorizes this single bounded invocation. Each later audit still requires a separate prior current-state receipt.

- Contract: `tasks/agent-loop/sprints/effect-permission-source-choice-20261031-r76.md`, SHA-256 `87325ab223af0e98a6ca8c78162ead6ba1d72403b318342d155ee5dd55069936`.
- R1 manifest: `tasks/agent-loop/sprints/effect-permission-source-choice-20261031-r76-inputs-r1.json`, SHA-256 `33a8769ab21ded37b85e436b90fe67f12ab8561eb2ffd0e90fe754acc23bb0dd`.
- R2 manifest: `tasks/agent-loop/sprints/effect-permission-source-choice-20261031-r76-inputs-r2.json`, SHA-256 `6c386e096fea70fa22a3b73fa237d08ee57f263aff994ac35eb54106575a909d`.
- Frozen R76 Lean module SHA-256: `5233c0784281ba4483db402a7f732b1bb71b766579cc16a77987bf53ebb45ac8`.
