# R61 admission — bounded ancestry reader

Status: ADMITTED under the continuing authorized Yulang research goal. Primary: `/root` (Luna); dispatcher: `/root/next_action_selector`.

## R60 gate and dispatcher decision

R60 closed `CLOSED_BOUNDED_PASS_RESEARCH_ONLY` at pushed closeout `b423819c5`. Its concrete same-input `rows`, `views`, and physical readers prove both `LocalDecode` fields and apply R59 candidate completeness to the existing consumer. Fresh independent review returned BOUNDED PASS, report SHA `8d80bf7049829d0d713d2a67d072cf2cf8be9f415538100d847ab7e815f08d5d`.

At the required sprint boundary, the dispatcher recommended R61 to model the existing relation-ancestry visitor and derive successful ancestry evidence from ordered native dependency records. It explicitly warns that identical calls can encounter different allocation outcomes; this sprint claims successful-call refinement only, not arbitrary failure-trace equivalence.

## Live roster, previous writers, and exact new leases

The primary synchronized the live collaboration roster. The R60 Rust author `/root/r52_rust`, Lean author `/root/r52_proof`, and independent reviewer `/root/r37_inventory_review` were all STOPPED before R61 dispatch; R60 source/model/review artifacts are frozen and pushed. No R60 writer overlaps the R61 assignments. R61 reuses those three existing registered agents; it starts no nested team.

Primary grants these disjoint R61 outputs:

- Rust author `/root/r52_rust`, Luna/high: `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_receiver.rs`, `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-rust.md`.
- Lean author `/root/r52_proof`, Sol/high: `notes/theory/lean/YulangClosure/BoundedAncestryR61.lean`, `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-proof.md`.
- Independent read-only reviewer `/root/r37_inventory_review`, Sol/low, after both author STOP receipts: `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-review.md`.
- Primary retains `tasks/agent-loop/current.json` and this admission record.

No other source path is leased. The current state preserves all 32 pending questions, all prior UNKNOWN observations, and all 12 quarantined paths. The three authors/reviewer are reused existing slots; no capacity override or path-lease release is applied.

## Immutable pins

- Contract: `tasks/agent-loop/sprints/effect-permission-bounded-ancestry-20261031-r61.md`, SHA `2fe85fdd723af0c484b3860b4f86a4e696856241f3b78142d2ed115ca5506b1d`.
- Baseline: R60 closeout `b423819c5`.
- R60 model: `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- R60 receiver: `0b25ddde51ee77cfdc558ad4384ce827e9f48880bd598f1640f5323a102672de`.
- R60 review: returned report SHA `8d80bf7049829d0d713d2a67d072cf2cf8be9f415538100d847ab7e815f08d5d`.
- Context: `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`.
- Source: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- R57 native model: `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.

Both authors must rehash their exact dependency cones before writing. A changed pin or source/model counterexample stops only the dependent lane and returns to the primary for adjudication.

## Fixed scope and resources

Prove that successful `require_relation_ancestry` visitation follows directed retained edges, includes both Replay parents, respects the visitor work counter and guard/error order, and yields the successful ancestry policy used by R60. Invalid parents/indices, oversized inventories, cycles, reversed edges, allocation/work failure, and exhaustion must not create evidence. Keep general allocation-failure trace equivalence, Internal-root extraction, outer Rust-to-Run, exact source correspondence, and parent theorem closure OPEN.

Budget: 6,000 seconds total (Rust 1,000; Lean 2,600; review 1,200; primary 1,200 including up to 500 closeout; Astra 0). Existing checkout only, pinned Lean 4.35 stdin audits. No new worktree/environment, builds/tests, Cargo, formatter, cache, scratch, target, or persistent process.
