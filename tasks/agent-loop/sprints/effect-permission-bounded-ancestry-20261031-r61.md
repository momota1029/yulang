# Sprint EFFECT-PERMISSION-BOUNDED-ANCESTRY/20261031-R61

Status: admitted, bounded research and private reader/helper implementation only. No production or whole-language closure.
Branch: `yulang3`; baseline: `b423819c5` (R60 reviewed closeout pushed).
Goal: Yulang inference/executor soundness, effects, principality, termination; unchanged Simple-sub source domain and A/B claims.

## Fixed outcome

Construct a sealed borrowed ordered dependency reader from the same native relation/dependency records used by the R60 owner projection. Model the existing `require_relation_ancestry` visitor, and prove that successful visitation establishes directed retained ancestry and supplies the ancestry policy consumed by R60's successful-search/consumer theorem.

Keep the successful-call refinement separate from the exact general resource/failure trace simulation. Identical ancestry queries may allocate differently across calls, so do not claim a single pure `ancestry descendant ancestor` function reproduces arbitrary allocation failures.

Preserve the visitor's source order and semantics: every Replay parent, LIFO worklist, visited suppression, relation direction, independent work counter, invalid index behavior, oversized-inventory guard, allocation/work failure and exhaustion. Allocation/work failure and exhaustion never produce ancestry evidence.

Falsifiers: reversed edge, omitted Replay parent, invalid parent/index, cycles, oversized reflexive query, duplicate/reordered dependency record, allocation failure and work exhaustion. Each must fail closed or preserve the exact existing error path.

## Pinned inputs

- R60 reviewed closeout: `b423819c5`.
- R60 reviewer-returned report SHA: `8d80bf7049829d0d713d2a67d072cf2cf8be9f415538100d847ab7e815f08d5d`.
- Primary's bounded review placement file SHA: `e360556fbb37cc98f53ad0b82bd0daaafa7454bac275401a8c3c097dd155541f`. This file is a summary/placement, not the byte-identical reviewer-returned report; the original report SHA above remains authenticated in the R60 outcome and R60 current-state receipt.
- R60 accepted Lean module: `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- R60 receiver: `0b25ddde51ee77cfdc558ad4384ce827e9f48880bd598f1640f5323a102672de`.
- R60 Rust handoff: `744014a3ec186e16e82cca0ba3497f53a08d2eb5bd5f60fe7f41ae8461b46730`.
- Context: `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`.
- Source: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- R57 native model: `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.

Rehash all transitive Lean and Rust dependencies before writing. A mismatch stops the dependent lane; preserve dirty inputs and do not substitute a clean checkout.

## Exact leases and budget

- Rust, `/root/r52_rust`, Luna/high: `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_receiver.rs`, and `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-rust.md`. Read-only other dependency/source files. Implement a private borrowed reader and, only if needed, share a pure parent-selection helper without changing control flow, allocation order, or propagation behavior.
- Lean, `/root/r52_proof`, Sol/high: `notes/theory/lean/YulangClosure/BoundedAncestryR61.lean` and `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-proof.md`. Construct successful visitor ancestry evidence, apply the R60 policy, preserve exact full theorem types and axiom audits. Keep Internal-root extraction, actual Rust-to-Run, and complete resource/failure simulation OPEN.
- Fresh independent reviewer, `/root/r37_inventory_review`, Sol/low: `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-review.md`; read-only after both authors STOP.
- Primary owns current state, exact lease transfer, adjudication, and Git.

Budget: 6,000 seconds total: Rust 1,000; Lean 2,600; review 1,200; primary 1,200 including up to 500 closeout; Astra 0. Existing checkout only, pinned Lean 4.35 stdin audits only. No new worktree/environment, build/test, Cargo, formatter, cache, scratch, target, or persistent process.

## Stop and boundary

Stop on any counterexample, required producer/source policy change, changed dependency pin, or exhausted lane budget. Preserve R60 reader behavior and R49/R57 consumer inputs. This packet does not prove pointer/Nat owner interpretation, full source-to-Run/resource correspondence, complete Context/R50 extraction, runtime, original parent A/B, soundness, principality, termination, complete hygiene, or production.
