# R297 — authenticated imported role identity for `where`

Status: bounded source-to-candidate identity bridge complete; R149 remains OPEN.

## Result

Implicit-prelude import collection now includes the role head appearing in declaration `where` clauses, even though it is not an `IdentifierExpression`. The new role-index-aware constructor resolves the public export route, then asks `resolve_source_export_owner` to match the export to one exact provider role declaration. It retains that declaration's `SourceRoleId` under the consumer spelling. The existing constructor continues to retain export routes without manufacturing a role identity.

Candidate where-prerequisite registration now reads that exact imported role identity from the HIR import environment and stores it with the existing subject row and source keys. The identity is cloned through the already implemented provider graph and FreshUse carrier. This does not solve the obligation or select an implementation. Public candidate preflight still rejects nonempty `where` clauses.

## Evidence

- `cargo check -p yu-hir` — passed.
- `cargo check -p yu-hir --features shadow` — passed.
- `cargo check -p yu-solver --features shadow-apply-candidate` — passed.
- `cargo check -p yu-playground` — passed.
- `cargo test -p yu-playground --lib pinned_public_export_route_retains_source_owned_edges_and_names` — passed; verifies absent identity without provider role indexes and exact imported `Display` identity with them.
- `cargo test -p yu-solver --lib --features shadow-apply-candidate candidate_scheme::authentic_demand_capture_tests::declaration_where_subject_uses_provider_row_and_same_freshuse_image -- --exact` — passed; verifies the authenticated imported role identity reaches the retained declaration obligation and the existing subject/FreshUse row bridge still holds.
- `cargo test -p yu-solver --lib --features shadow-apply-candidate candidate_source::where_clause_source_tests::candidate_preflight_does_not_drop_retained_declaration_prerequisites -- --exact` — passed; preflight remains fail-closed.
- `git diff --check` — passed.

Compiler warnings shown during checks are existing unused/private-interface warnings; no new warning remains for the intentionally retained role identity field.

## Remaining work

Role obligation discharge still needs the provider's implementation index, type-directed selection rules, method evidence, and a consumer sharing the same inference world and FreshUse row. The normal Playground `prepare` path still does not construct that provider world. R149 unchanged samples, runtime behavior, source/native correspondence, and proof closure remain OPEN. No independent review ran under the user's solo-work instruction.
