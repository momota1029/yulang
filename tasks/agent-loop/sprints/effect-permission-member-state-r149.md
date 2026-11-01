# R149: effect member state construction and R118 decoder repair

## Objective and gate

Continue the user's existing whole-Yulang soundness and Effect-hygiene goal. Preserve the original H and A/B claims, quantifiers, semantics, source domain, and production boundary. This sprint must produce a reviewed, source-owned member/state construction contract and repair the R118 proof terms so R119 can be checked. A successful proof module does not close the source/native bridge or parent theorem.

R148's accepted result is the starting point: the actual operation producer is `View`/`Support → AnnotationMember`, but no authenticated incoming input/protection state is associated with each member; FreshUse remaps transformer/demand coordinates without transporting that state to a protection-sensitive consumer. `Contribution` alone is not a demonstrated carrier for the actual operation producer.

## Exact inputs

Use baseline commit `87dfe33bcd4c572d740dc33b454114b6018a4376` and these immutable blobs only. Do not read dirty working-tree Rust:

```text
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49 crates/yu-solver/src/candidate_source.rs
102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01 crates/yu-solver/src/candidate_effect.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905 crates/yu-solver/src/candidate_context.rs
e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814 crates/yu-solver/src/candidate_scheme.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03 crates/yu-solver/src/candidate_scope.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61 crates/yu-solver/src/candidate_extrusion.rs
2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean
f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f notes/theory/lean/YulangClosure/PermissionMemberWitnessR119.lean
1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5 notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean
fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679 notes/design/2026-10-15-compose-scoped-effect-release.md
```

Also authenticate the R148 outcome/review and R147/R148 source/proof handoffs before using their conclusions. Never use the current dirty versions as source evidence.

## Lanes and outputs

1. **Source contract lane**, researcher, maximum 600 seconds. Identify the exact source-owned creation operation that can associate each real `AnnotationMember` with its incoming contribution/input/protection state. Trace the association through all relevant producers, same successful FreshUse scope/tag maps, and the reached consumer/Catch decision. State the inventory bounds, attribution, collision behavior, rollback behavior, and preservation of independent protections. Return an implementation-ready field/update/read contract and a falsifier. Do not edit Rust or run Cargo/tests. Sole output: `tasks/agent-loop/inbox/effect-permission-member-state-construction-r149-source.md`.

2. **Lean repair lane**, registered `lean_prover`, maximum 600 seconds. Edit only `notes/theory/lean/YulangClosure/NativePermissionDecoderR118.lean` and write only `tasks/agent-loop/inbox/effect-permission-decoder-repair-r149-proof.md`. Repair the two reported proof-term failures without changing definitions, theorem types, assumptions, axioms, or imports. Build only the R118/R119 dependency cone using pinned Lean 4.35.0 and the existing `.lake`. For R118 and `PermissionMemberWitnessR119.selected_retained_member`, report fully qualified theorem type and complete `#print axioms`; do not accept `sorryAx` or default-build success as closure.

3. After both author lanes STOP and hashes freeze, a fresh `compiler_referee` reviews source contract, proof edits, theorem types and complete axiom receipts within 300 seconds. Sole output: `tasks/agent-loop/history/effect-permission-member-state-decoder-20261102-r149-review.md`.

## Resources, limits, falsifiers

Total cap 1,680 seconds; no Astra, no nested child teams, no new environment/worktree/checkout, no Rust edits, no Rust build/tests, no cache deletion. Reuse the existing Lean 4.35.0 installation and `.lake`. At most two targeted build attempts and 240 seconds total build time. New regular cache data may grow by at most 16 MiB; record before/after sizes and output hashes. If the bound would be exceeded, stop before another build.

Concrete falsifiers include: no source-owned premise for initial state; contradictory states assigned to one member; a sibling route/provider borrowed by identity collision; dropping inherited or external protections; or using different FreshUse maps for state and transformer. Abstract examples alone are not source counterexamples.

No Rust implementation lease is granted by R149. The next implementation packet must use the independently reviewed construction contract and exact clean source paths. Do not inspect or release quarantined runtime paths. Keep source/native, semantic, original A/B, full hygiene, soundness, and production gates OPEN unless their original obligations are actually discharged.
