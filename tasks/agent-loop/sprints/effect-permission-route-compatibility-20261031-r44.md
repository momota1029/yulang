# EFFECT-PERMISSION-ROUTE-COMPATIBILITY / R44

Status: candidate bounded source/proof sprint. Existing checkout only; no new environment, worktree, cache, target, scratch, Cargo, Lake, formatter, build, or tests.

## Parent and outcome

Parent: the unchanged annotation permission/inflow/subtraction obligation in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2. R43 proves a conditional permission-to-FreshRoute binding; it does not prove that the bounded receiving experiment owns such a route.

R44 determines whether the exact receiver `DefinitionUseId` can satisfy R43’s FreshRoute premise without changing inference. Success is either (a) source-established same-use FreshRoute construction satisfying every constructor prerequisite, or (b) a precise `NO_SAFE_CONSUMER_SLICE` obstruction. Current evidence favors (b): `candidate_receiver::execute_receiving_assembly` calls `route_internal`; this creates an Internal receipt for original terms. FreshRoute is published only by `instantiate_candidate_graph` on the Incoming path. `route` admits each use once. Do not claim equality of use IDs makes the two route kinds equivalent.

No semantic change, rerouting, second admission, synthetic/foreign FreshRoute, consumer edit, subtraction, or production behavior is authorized. Quarantined runtime files remain out of scope.

## Frozen inputs

Branch `yulang3`; baseline `b2c4906821b9e0c3b01cb18321b1b7340a8f3c5f`.

- R43 Lean `UseScopedPermissionR43.lean`: `83ede0609353cec9dfde8258fa86f0f7c72aadef647dbe0819fe326776e46f8d`.
- R43 independent review: `fcad39e4126b1d2d826cc1b32c03e359b43fa5ad7bc5a6864119b266a0e5bc6b`.
- R43 Rust handoff: `c04110859cafa42cffa0d52982f6c9f52fbdd474512fa1054f37bc72f19aa9ee`.
- `candidate_receiver.rs`: `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3`.
- `candidate_scheme.rs` R43 frozen dirty snapshot: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`.
- `candidate_effect.rs` R43 frozen dirty snapshot: `73ad01324356672f1e45e56ea18d6f5bf0ded8628cce56e884960eb29bd5786d`.
- `lib.rs`: `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce`.
- R38 residual model: `notes/theory/lean/YulangClosure/EffectPermissionResidualR38.lean` `e5657e0b8affaaa0ffef6543c8e329957a1519a04a194392dbd245064a623642`; source characterization handoff `tasks/agent-loop/inbox/effect-permission-residual-join-r38-rust.md` `768098b3cbb313ee6b317abf05a922bb85f3af18bf327b4d412a5ba80f168e4f` revision 2. Preserve its boundary between metadata authentication, actual provider arrival, selected Catch and residual folding.

Primary rehashes every pin before worker launch. These source snapshots contain admitted or reviewed dirty bytes; workers may not normalize them or touch other changes.

## Exact lanes

### Source correspondence — read-only, ≤700 seconds

Owner: `/root/r40_join_preflight`. Read only the receiver initialization, `route_internal_inner`, `route`, `route_candidate_graph`, `instantiate_candidate_graph`, FreshRoute publication and direct owner definitions in the pinned files. Write only `tasks/agent-loop/inbox/effect-permission-route-compatibility-r44-source.md`.

Report either an already-existing same-use FreshRoute and all established constructor prerequisites, or `NO_SAFE_CONSUMER_SLICE` with the first missing capture/graph prerequisite and the exact Internal-versus-Incoming difference. Track the full DefinitionUseId, source owner, relay provider root, original terms, captured/fresh terms, retained context and residual endpoint. Explicitly reject a second route admission and equal-ID/equal-term shortcuts. No compiler-source writes.

### Lean proof — ≤700 seconds

Owner: `/root/r43_proof`. Write only `notes/theory/lean/YulangClosure/RouteCompatibilityR44.lean` and `tasks/agent-loop/inbox/effect-permission-route-compatibility-r44-proof.md`.

Use pinned Lean 4.35.0, stdin only, one CPU, `-M1024`, ≤120 seconds per invocation. No Lake/Lake env, builds, tests, extraction file, scratch, cache, olean, target, worktree or environment.

Formalize Internal versus Incoming route constructors and the one-admission invariant. Prove that an Internal-use receipt alone cannot discharge R43’s same-use FreshRoute/native-incidence premise. A positive compatibility theorem is allowed only with explicit constructor premises that the source handoff independently establishes. State the conditional consumer theorem so suppression requires the R43 binding, an actual arrived terminal whose provider/declaration/family match, and the selected Catch; preserve unmatched endpoints. Apply the result to the original parent without claiming Rust execution or source extraction from hashes.

### Independent review — ≤400 seconds

Fresh non-author reviewer: `/root/r40_read2_review`; assigned only after both authors STOP and output hashes freeze. Write only `tasks/agent-loop/inbox/effect-permission-route-compatibility-r44-review.md`.

Check actual source constructors, full DefinitionUseId/owner/provider distinction, one-admission invariant, Lean theorem types and complete axiom audit, and that no equivalence is assumed from equal IDs, rows, terms or route ownership. No builds/tests/checker rerun.

## Budget, leases and closeout

Total 2,600 seconds: source 700, Lean 700, review 400, primary 800 including ≤500 closeout; Astra 0. At most two producers plus review/integration. Same single checkout; worktree count stays one. Keep all 32 pending records and every UNKNOWN/quarantined identity/path unchanged.

No tests, builds, Cargo, Lake, cache, target, formatter, scratch, worktree, environment, ordinary inference edits or expected-output changes. Static checker is only workflow evidence, not math or live execution. Fresh Rust compilation and runtime behavior remain unobserved.

Falsifier: any accepted argument uses an Internal receipt to satisfy FreshRoute without source-established construction, admits the same use twice, borrows another use’s FreshRoute, or suppresses without all permission/arrival/selection premises. Freeze `NO_SAFE_CONSUMER_SLICE` if source construction is absent. A positive route replacement or Internal-route permission adapter requires a separate primary implementation contract.
