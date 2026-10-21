# R292 — Authenticated imported identities in HIR

Status: implemented source-only route validation and opt-in HIR bindings; parent
R149 remains open. Solo result, not independently reviewed.

## Construction

`resolve_public_export` now validates every concrete module segment against a
direct public `ModDeclaration` in the indexed parent. A parser `Missing` node
on a valid external `ModDeclaration` is discharged only by the exact indexed
child module; `Error` tokens and `Invalid` nodes remain recovery failures.
Virtual enum and act member namespaces continue to use their containing source
module. Private ancestors, ambiguity, recovery, and cycles are covered by the
source export tests.

`SemanticImports::with_implicit_prelude` scans identifiers in one exact parsed
consumer and resolves matching names from the supplied source export indexes.
The resulting environment is bound to the parse root and consumer module
identity. HIR namespace construction keeps local declarations first, then
adds imported source identities only when no local name exists. Ambiguous
exports remain ambiguous. An imported identity contains the exporting module,
name, exact source key, byte range and syntax kind; it is never represented as
a local `DefId` or local definition ordinal.

HIR and local-source name forms both retain imported identities. The legacy
single-HIR solver collector classifies imported bindings as unsupported, and
the candidate-source preflight rejects them until a multi-HIR type/scheme owner
exists. The runtime likewise does not fabricate a local module cell for an
imported name.

## Evidence

- `yu-hir` library tests pass (147 tests).
- `yu-playground` library tests pass (32 tests).
- The unchanged 92-byte Console source retains the pinned `std::io::console::println`
  identity through its implicit-prelude route. Its `say:` expression still has
  an unsupported local-source carrier; a supported standalone `say` use retains
  the same export identity.
- A local `say` binding shadows the imported prelude name in the consumer HIR.
- `cargo check -p yu-hir` passes. `git diff --check` passes.
- `yu-solver` library tests did not complete. The parallel run aborted with a
  stack overflow. The serial rerun reported failures in
  `f5c_normalization::tests::transferred_member_outputs_have_a_simultaneous_index_peak`
  and `tests::candidate_unit_tests::unit_diagnostic_buckets_keep_kind_and_distance_order_and_replay`,
  then remained in `tests::f4_bounded_cycle_scale_matrix_is_linear` for over
  eleven minutes of CPU time. It was stopped at the sprint resource boundary.

These checks establish source identity correspondence and fail-closed seams,
not imported type/scheme selection, role conformance, method selection,
execution, exact output, source/native correspondence or R149 closure. The
candidate solver still assumes one HIR's local definition owners. R149 remains
open for both unchanged Yulang2 samples and the original proof obligations.
