# R239 — Parent instance mapped-bound admission

Status: partial constructor-level source/native result; unreviewed. R71, R72, and the parent remain OPEN.

## Fixed obligation

The parent is `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7 (SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`). Its direct-Name template has original admitted constraints `e_t<=e_n<=e_R` and `e_n<=e_t`. For one authentic FreshUse instance map `mu`, the parent implication additionally requires the mapped bounds `mu(e_t)<=mu(e_n)<=mu(e_R)` and `mu(e_n)<=mu(e_t)` to be actually admitted, together with actual Apply argument/output and next-provider joins. This does not assert that a solver RelationId is itself a `mu` image.

R238 established that a raw `Work::Bound` transfers exactly the fibers at its physical raw key; equality canonicalization does not reverse-attach children to stale raw keys. It did not establish whether a parent-required mapped bound uses that route. R71/R72 and the parent remain OPEN.

## Source-labelled original constraints

For a registered Computation formal, the source planner emits `Action::FormalNameEffect` only when a Name resolves to that registered Computation parameter. Executing it calls `candidate_formal_effect_equal`, which emits both directed constraints at the Name occurrence's adjacent slots. The Lambda constructor separately emits `body_effect<=return_effect` at slot 4; it deliberately omits slot 3 for a Computation formal. These are the constructor counterparts of the original `e_t<=e_n`, `e_n<=e_t`, and `e_n<=e_R` constraints. The source action carries the HIR occurrence, and `candidate_context_seed` looks up the corresponding checking reference for each `ConstraintOccurrenceId` when constructing the source set on its relation.

## Conditional FreshUse admission chain

For a relation that is already attached to a captured raw bound key, `Capture::bound` walks that exact key's relation bucket and stores a `Graph::Bound` with its source `BoundKey`, `RelationId`, and an immutable evidence snapshot. A provider use creates one `FreshUse` containing the row, term, context, scope, evidence and relation remaps. For each captured `Graph::Bound`, `begin_candidate_fresh_bound` maps the endpoints from that same `FreshUse`; if the bound has a relation, it constructs a FreshUse child with an exact witness and the mapped scoped payload. It imports the captured evidence and begins physical bound restoration.

The scoped admission path requires that the child relation match the exact mapped pair and that a `FreshUse` dependency name the captured key, target key, parent relation, child relation and use instance. The restoration inserts the target bound and records an emitted physical slot with constructor readback. `fresh_use_fiber_emission` can authenticate one captured snapshot -> mapped admission/relation -> physical emission/readback chain. Function dispatch derives its child relations from the currently processing parent and retains the parent source set. This establishes a conditional constructor fact for every captured bound that reaches successful restoration.

The evidence coverage remains explicitly partial: a FreshUse admission carries `ReplayUseAntecedentsNotRetained`. The diagnostic `CandidateGraphFreshUse` and Apply observations also keep `GeneralizationAndFreshUseCorrespondence`, source typing/admission and other semantic premises in their unresolved list. These are diagnostic boundaries, not an assertion that ordinary inference lacks its source constraints.

## Parent application and first missing premise

R239 supplies the lower-level map-and-admit route once a needed original bound has entered the provider's captured graph. It does not establish that the three parent inequalities are all present in the exact provider graph as independently source-identified bounds, that the FreshUse map realizing them is the parent's authentic `mu_i`, or that every later forwarding Apply argument/output joins that same instance and the next provider's own map. The first unresolved edge is therefore source-to-native instance correspondence and complete per-use bound selection, before R71/R72's canonical-child route. No evidence currently makes the parent-required bounds depend on that route.

Do not identify `RelationId`, `BoundKey`, a checking event, or endpoint equality alone with `mu_i`. A future source-qualified join must map each original source constraint through its HIR formal/use, captured graph bound and authentic FreshUse instance, then match successful admission/emission and the actual Apply comparison. The `ReplayUseAntecedentsNotRetained` coverage gap and observer's unresolved correspondence are exact falsifiers for any stronger claim.

The fixed contract is `tasks/agent-loop/sprints/simple-sub-parent-instance-admission-20261021-r239.md` (SHA-256 `d638d4c2445d575619cf4e56033ab7b1c01a972637cd5dc1f10e65419250e8cf`). Its exact code pins remain unchanged. No implementation change, test, build, sample execution, semantic change, or production claim is included.
