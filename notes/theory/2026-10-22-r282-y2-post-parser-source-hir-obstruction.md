# R282 — post-parser source/HIR obstruction evidence

Status: checkpointed primary-only source evidence; provisional and unreviewed.

## Exact unchanged inputs

The temporary CLI inputs match Authoritative R149 exactly: Types is 142 bytes with SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`; Console is 92 bytes with SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`. The Yulang2 samples were not edited.

## Observed routes

- Types parses and lowers. Candidate inference fails with `Collection(ComponentIdentityExhausted)`. With the repository's scoped collection diagnostic enabled, the exact rejecting branch is `crates/yu-solver/src/candidate_source.rs:1539`, `LocalSourceForm::FieldTail { .. } => Err(unavailable())`. The source carrier retains the `pair.say` member and exact source range; the solver explicitly requires authentic imported role/field resolution before member typing.
- Console parses/lowerings reach candidate preflight, which rejects unresolved or ambiguous `LocalSourceResolution::Name` at `candidate_source.rs:500`. The playground currently calls `lower_module_with_local_source` with `SemanticImports::empty`; no source-backed standard-library module resolver supplies `println` or `say` identities there. This is a current implementation obstruction, not a claim that Yulang2 rejects the source.
- Exact pinned `std::core::fmt` now has zero syntax diagnostics. Running it through the playground reaches HIR lowering and fails `StructuralProjection`. The local-source block walk only accepts statement/block-separator children; declaration-local `WhereClause` nodes are not consumed. Search of `yu-hir`, `yu-solver`, and `yu-types` finds no WhereClause consumer. This correlates R281 syntax success with a concrete next carrier gap; the exact failing child is not exposed by the public error enum, so that final causal attribution remains provisional.

## Parent application and remaining premises

The first remaining implementation seams are (1) declaration-local constraint transport from the new CST into a source-owned HIR carrier, (2) module-qualified authentic role/implementation resolution and prerequisite discharge, (3) authenticated `SemanticImports` and full pinned module publication, and (4) the sample's FieldTail member consumer. Console also requires identity-bound host request continuation; Types/Console need the original schedule/output checks. R149 source/native soundness, principality, initializer composition/order, and production remain OPEN.

No repository code changed in R282. No sample output was produced. The converted unified design and proof companion remain governing; contravariant `[io]` is the open row `[io,'e]`.
