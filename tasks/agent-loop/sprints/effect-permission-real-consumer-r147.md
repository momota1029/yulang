# R147 — actual effect consumer and scope protection path

Status: ADMITTED by Luna under the standing ongoing Yulang soundness authorization.

## Original goal and success evidence

Keep the original Simple-sub A/B claims, quantifiers, source domain, accepted semantics, and production gate unchanged. Determine whether the committed Rust path from `candidate_context_execute_relation` through `candidate_apply_effect` reaches a real effect decision or Catch subtraction that consumes scope/input/protection data corresponding to `NativeScopeTransformer.State`; if so, identify the exact transport and premises needed for the same FreshUse map. If no such consumer bridge exists, name the precise missing source boundary without calling absence a counterexample.

Success means an independently reviewed source trace with exact constructors, arguments, state updates and reachable consumer, plus a precise remaining source/native premise and owner. This packet authorizes no Rust edit or executable check.

## Baseline and exact immutable inputs

Baseline: `3560df97dab02744da10e897c73c1cf94118f4ee` (pushed). All Rust reads use only these baseline blobs; do not inspect working-tree Rust.

- `crates/yu-solver/src/candidate_source.rs` — `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/candidate_context.rs` — `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `crates/yu-solver/src/candidate_scheme.rs` — `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814`
- `crates/yu-solver/src/candidate_scope.rs` — `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`
- `crates/yu-solver/src/candidate_intrusion.rs` — `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `crates/yu-solver/src/shadow_apply.rs` — `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278`
- `crates/yu-solver/src/lib.rs` — `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `crates/yu-solver/src/candidate_extrusion.rs` — `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `crates/yu-solver/src/candidate_effect.rs` — `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`
- `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` — `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- `notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean` — `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- `notes/design/2026-10-15-compose-scoped-effect-release.md` — `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679`
- R146 source handoff — `9c940ab56ccd182299833fe93b41701619d600b62c15f3af21b9b94659b694ef` (unreviewed until R147 review).
- R145 conditional proof and source handoffs — `da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea` and `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba`; the Lean candidate remains unchecked and conditional.

The R146 proof deviation receipt is procedural only. Its withheld source observations and conclusions are excluded from R147 inputs and may not be relied upon.

## Lanes and exact output leases

1. Luna/high source lane, maximum 600 seconds: independently rederive the allocator/support invariant and reconstruct `candidate_context_execute_relation → candidate_apply_effect → reached effect/Catch operations`, including protection/state argument flow. Output only `tasks/agent-loop/inbox/effect-permission-real-consumer-r147-source.md`.
2. Registered prover lane, maximum 480 seconds: from the admitted immutable sources and governing compose-release claim, relate the actual operations to transformer evaluation and incoming state. Identify exact conditions, a reachable falsifier, or the first missing source/native bridge. Do not assume a Rust state matches Lean `State`; do not create a new unchecked Lean file. Output only `tasks/agent-loop/inbox/effect-permission-real-consumer-r147-proof.md`.
3. Fresh independent reviewer, maximum 300 seconds after both lanes stop: verify source hashes first, then independently inspect admitted baseline code and the frozen R146/R147 handoffs. Review the R146 allocator trace and R147 consumer correspondence. Any input boundary deviation means no verdict. Output `tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-review.md`.

The primary owns adjudication, R147 outcome, compact state, explicit staging and normal push. Workers may not inspect quarantined working-tree changes, edit Rust or Lean, spawn descendants, expand inputs, or run build/test/compiler commands. Any further source owner requires return to Luna.

## Resources, exclusions and stop

Total cap 1,560 seconds, including up to 1,380 seconds of assignments and 180 seconds for integration. This is a new explicit R147 budget, not a reset of R146. No Astra, Rust/Cargo/Lean/Lake execution, builds, tests, scratch/cache, environment, checkout or worktree. Do not clean, stage, stash or alter any pre-existing worktree paths.

Concrete falsifiers: a reachable allocation cut violation, mixed FreshUse maps, dropped or untransported protection used by a real effect/Catch decision, or a required release condition not preserved. Empty-state `shadow_apply` observations, local tests, and lack of a consumer alone cannot prove/refute the original theorem.

The original A/B claims, semantic approval, full source/native theorem, and production readiness remain OPEN unless their governing contracts are fully discharged.
