# R136 outcome — Rust adapter checkpoint and Lean constructor law

Sprint contract:
`tasks/agent-loop/sprints/effect-permission-adapter-and-constructor-20261101-r136.md`
(SHA-256 `99138f4ed08a48ab010b51b2e3f2cc17d2f5e1c228af20bd8fddbef40d12734b`).
Baseline was `abbe733b952138b5d576c30936692dd262f3e92f`.

## Rust checkpoint

Fresh compiler-referee review by `/root/r136_rust_review` passed the exact one-line repair. The extractor
requires `&BranchTermArena`; the old call supplied `&ConstraintStore`, while
`ConstraintStore.terms` owns the required arena. The target is exactly 508,261
bytes, SHA-256
`e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`.
The frozen author handoff and independent review are in the R136 inbox/history
records.

Commit `685b97bd1` (`research: repair native adapter arena argument`) contains
only that source line plus the R136 contract, admission, source handoff,
review and current-state record. The pre-push `git fetch origin yulang3`
confirmed origin at the baseline; outbound range contained only this commit.
Normal push succeeded: `abbe733b9..685b97bd1 HEAD -> yulang3`. No force push.

This is an uncompiled source checkpoint. No Cargo/build/test was run; R111's
private Rust compile/resource gate remains unmet and unspent. The adapter still
has no permission consumer and the patch proves no runtime reachability,
source/native correspondence, or effect-hygiene result.

## Lean constructor result

The frozen artifact is
`notes/theory/lean/YulangClosure/FormalPermissionConstructorR136.lean`
(10,356 bytes, SHA-256
`3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f`); its
handoff is
`tasks/agent-loop/inbox/formal-permission-constructor-r136-proof.md`
(14,946 bytes, SHA-256
`c93d2aadb82300dc4aa0ce085cef29537d2a418a2874407179f3888cd842950e`). A
fresh independent Lean review by `/root/r136_lean_review` passed; receipt:
`tasks/agent-loop/history/formal-permission-constructor-r136-review.md`.

`inventory_exact` proves that the recursive ordered output equals the
independent traversal of all Function ports followed by their exact emission
rule. `inventory_membership` characterizes every emitted permission as the
record for a negative, nonempty, concrete-only port at its retained structural
path. `record_identity` proves complete metadata/path/member preservation.
The separate boundary theorems establish that nested negative ports reject a
concrete-plus-symbolic-tail row while the modeled outer entry retains its
concrete members. This is a constructor projection over an explicit supported
tree, not an authenticated source instance.

Pinned Lean 4.35.0 direct check and final named-module build both exited 0.
Eight theorem types and full transitive axiom audits are in the frozen
handoff; independent review found no discrepancy. Axioms reported:

| Theorem | Transitive axioms |
| --- | --- |
| `inventory_exact` | `propext` |
| `element_inventory_exact` | `propext` |
| `emit_exact` | `propext`, `Quot.sound` |
| `inventory_membership` | `propext`, `Quot.sound` |
| `constructor_inventory` | `propext`, `Quot.sound` |
| `record_identity` | none |
| `mixed_row_boundary` | `propext`, `Classical.choice`, `Quot.sound` |
| `entry_mixed_retained` | `propext`, `Quot.sound` |

Producer verification took 24.528 seconds total; peak sampled process-group RSS
was 1,029,435,392 bytes under the 1,073,741,824-byte cap. The independent
review check took 4.850 seconds with peak 889,626,624 bytes. The first build
exposed a namespace collision; an explicit `PortStep` alias fixed it. That
failure and correction are retained in the handoff. No `sorry`, project
axioms, native-evaluation assumptions, or checker bypass were used.

## Parent application and remaining owner

The constructor theorem reduces the abstract permission-inventory equality
for the represented tree to computation and makes the emitted record/path
law explicit. It does not establish the actual HIR-to-tree decoder or that a
successful Rust construction equals this Lean inventory. The next decisive
premise is therefore authentic HIR/source identity decoding plus equality to
successful native constructor output, including failure/rollback behavior.
After that, actual arrival, capture/export, copy/use correlation,
symbolic-tail connectivity, checking and Catch subtraction remain with their
source and consumer owners.

Original `SourceProblem.InferenceSoundness`, Oracle effect-hygiene H, A/B,
Rust-to-Lean simulation and production gates remain OPEN. R135's receiver
checkpoint remains separate; it does not consume the nested `FormalPermission`
record. The large pre-existing dirty solver diffs, quarantined runtime paths,
and untracked pending R103/module-supplier artifacts were not staged or
committed.

Sprint status: **CLOSED_CONDITIONAL_CHECKPOINTS; parent goal continues**.
