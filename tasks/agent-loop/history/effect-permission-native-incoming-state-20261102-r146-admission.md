# R146 admission

- Sprint: `EFFECT-PERMISSION-NATIVE-INCOMING-STATE/20261102-R146`
- Baseline: `3560df97dab02744da10e897c73c1cf94118f4ee` (pushed; HEAD = upstream at admission)
- Dispatcher: R145 end dispatch recommended R146 to identify the actual native incoming-state consumer and the allocator/support invariant across producers, replay, prior copies, and failure handling. R146 start dispatch further identified `shadow_apply.rs` as a research-only empty-state observer, not the real Catch/effect consumer, and required candidate_intrusion/lib rollback paths in the allocator audit. This is a new source boundary, not a repeat of local map inspection.
- Narrow input amendment: the proof lane's immutable locator found `candidate_apply_effect` in `candidate_extrusion.rs`, called by the already admitted context executor. The dispatcher authorized inspecting that actual handoff plus only the reached effect/Catch operations in `candidate_effect.rs`. An earlier dispatcher response named `candidate_effect_kernel.rs` and `candidate_receiver.rs`; baseline inspection established that the kernel path is absent, and the dispatcher corrected the recommendation: use `candidate_extrusion.rs` and `candidate_effect.rs`; receiver is not needed without a demonstrated path. **Boundary deviation:** before this amendment, the proof lane had read `candidate_effect.rs` ranges 1–185, 260–330, 1180–1278, and 1380–1410, plus source-wide baseline grep hits in that file; a baseline-wide locator exposed the function-name line `candidate_extrusion.rs:1147`. The proof lane reported the deviation before freezing and withheld all substantive conclusions. After the amendment it read `candidate_extrusion.rs` lines 1140–1172 and `candidate_effect.rs` lines 1437–1546 and 1274–1291; it also read allowed `candidate_source.rs` lines 1604–1654. It did not read `candidate_receiver.rs`. The full read inventory is frozen in the proof deviation receipt. No time, output lease, execution, or source-edit authority was added; elapsed time was not instrumented.
- Fixed goal and restrictions: `tasks/agent-loop/sprints/effect-permission-native-incoming-state-r146.md`.
- Frozen source SHA-256 at baseline:
  - `candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
  - `candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
  - `candidate_scheme.rs` (immutable `git show HEAD:` only): `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`
  - `candidate_scope.rs`: `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`
  - `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
  - `candidate_effect.rs`: `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`
  - `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
  - `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
  - compose construction: `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e`
- Source and proof output ownership is exact in `current.json`; review is admitted after both handoffs freeze.
- The proof lane is source/proof analysis only; it will not add an unchecked Lean file or assume a native `State` model. Fresh independent review output: `tasks/agent-loop/history/effect-permission-native-state-support-20261102-r146-review.md`.
- User authorization: ongoing Yulang soundness goal and explicit request to analyze Rust and push coherent reviewed work. No production edit or executable validation is admitted.
