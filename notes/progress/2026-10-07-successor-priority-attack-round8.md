# Successor priority attack round 8

Baseline: `b1d37c03b979b842f169f74a407162b1d3d27dad`, fetched and confirmed as both local HEAD and `origin/research/simple-sub-intrusion` before work. The canonical DAG validated at 90 nodes / 196 edges: CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43, OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1. This round changed no semantic status.

## Priority-A and recursive/world/principality attacks

The O0 producer-chain audit found no current source, HIR, Core, solver, Function constructor, or shadow evidence producer for an original typed signature-local `q_c : EffPosition_sig,orig(U_c;B,X,xi,Delta_c)`. The retained Apply identities and eight structural endpoint labels are not typed positions. `Gen-Call-0` emits only under a well-formed realization and consumes a supplied typed call certificate. The exact next O0 leaf is independent original signature-position formation, with `OC-CallEff` remaining a separate occurrence-incidence rule. This narrows the source location but proves neither rule; O0 remains OPEN.

A bounded separation shows that satisfied decorated `WF_Dec`/`VIncl`, receipt and entry facts cannot establish original-family inhabitation unless their independent interpretation already contains that bridge. This is not an Authority-consistent countermodel or a source counterexample. No second complete source semantics or user decision follows.

For CALL_TYPE, checked membership at `F_c` conditionally follows for each exact retained `CalRet` witness only from independently justified `A_f` membership, same-witness `VIncl`, and the common Function/CallableMem interpretation. The source producer for returned `A_f` membership at every such witness remains absent. Separately, actual-provider whole-carrier inclusion from `F_c` to `U` remains an independent universal eliminator; neither pointwise membership nor argument-specific checking proves it. CALL_TYPE remains CONDITIONAL-CLOSED.

Other attacks confirm the existing narrow frontiers without promoting them: ORIGINAL_ASSOC still requires original slot/owner birth and complete-family uniform witness assembly; INIT_WORLD still lacks import-resolution input before its open semantic root; REC_DESC still lacks same-witness Name/Return membership or a valid two-closure introduction; ALL_VIEW still lacks independently grounded whole decorated result inclusion and actual resolver acceptance. The restricted successful-production Q/R capture identity theorem does not establish use-time source correspondence or activation liveness. Reports for these additional fronts are producer analyses, not new reviewed closures.

## Shadow implementation slice

Added `SolvedModule::shadow_pending_application_closed_schemes`, a default-off borrowed projection from each rooted pending Apply row to its exact enclosing root and that root's current finalized scheme in the same solve. Rootless rows are omitted; independent solves retain distinct row/scheme identity. It performs no inference, allocation, query accounting, SCC operand join, or premise discharge. `ApplicationTypingRuleUnresolved` is unchanged. The projection says only which current definition owns the row; it does not show the scheme types the Apply or is its successor/generalized scheme.

One independent compiler-referee review passed with no blocking, major, or minor findings. The reviewer inspected the delta, direct collector/finalizer/query dependencies, surrounding integration test, and governing captured-function/root-ownership rules. The producer ran:

```text
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-f5 --test shadow_captured_source_retention shadow_local_bind_joins_pending_structural_projection_without_discharge -- --exact
CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo check -p yu-solver
rustfmt --edition 2024 --check crates/yu-solver/src/shadow_f5.rs crates/yu-solver/tests/shadow_captured_source_retention.rs
git diff --check
```

The focused test passed (1); check, formatting and diff checks passed. No performance samples or broad suite were run. The canonical ledger was regenerated/validated and retains all counts and edges. `HIR_WIRING` remains IMPLEMENTATION-ONLY; all semantic gates remain unchanged.

## Next attack

Continue at the owning dependent Function-signature formation phase for O0. Require original position-family introduction at `Delta_c`, independent of `OC-CallEff`, successful comparison, solved shape and execution. Once that rule is genuinely justified, attack its separate typed occurrence incidence, then return to P2 and the actual-provider CALL_TYPE eliminators. Production cutover remains blocked by open soundness, principality, source adequacy, admission and pipeline correspondence obligations.
