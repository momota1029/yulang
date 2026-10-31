# R116 Rust/source handoff — suppression permission membership

Sprint-ID / contract revision and SHA-256: `EFFECT-PERMISSION-SUPPRESSION-PERMISSION/20261102-R116`, revision 1, contract SHA-256 `1dee9e909ba3050f80146eb0657ecc0d2e563ea15cd4c516b0f6ae7ba602d5f6`.

Assignment-ID / handoff revision: `R116-SOURCE`, revision 1.

Parent gate / original theorem and scope locator: the original inference soundness and effect-hygiene obligations remain OPEN. This bounded result concerns only membership of the selected provider operation member in the retained permission for a successful private `Suppress` decision. It does not claim that all incoming effect members belong to the concrete annotation.

Baseline / direct dependency hashes: immutable baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; exact Rust blob SHA-256 values from the R116 contract:

- `crates/yu-solver/src/candidate_receiver.rs`: `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`.
- `crates/yu-solver/src/candidate_effect.rs`: `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`.
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- `crates/yu-solver/src/lib.rs`: `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.
- Reused R115 Rust handoff: `tasks/agent-loop/inbox/effect-permission-rust-consumer-path-r115.md`, SHA-256 `4996881f23dd0982b11aea64d37d0771cc1151864be6154f9d898b35ff4d3700`.

Role / actual worker ID / current session / launch or resume receipt: Luna/high source lane, `/root/r116_rust_source`; separate runtime/session telemetry was unavailable to this worker.

Requested model and effort / observed model and effort: Luna/high / UNKNOWN.

Exact leased paths / authors and contributing descendants: only this handoff, authored by `/root/r116_rust_source`; no descendants.

Outcome class: source-native-evidence, bounded static source trace; no source edit or implementation promotion.

## Constructor chain and membership result

**Result: every endpoint that can receive `Suppress` in this admitted envelope has a provider operation family in the same retained formal permission's `concrete` vector.** The proof is by joining the existing source constructors and identity checks; membership is not assumed.

1. `assemble` selects the two admitted definitions and resolves the caller's provider operation from its `LocalSource`. On the relay side it selects the lambda parameter's annotated effect row and requires exactly one `row.concrete` member, no row variables, and an `Int` value annotation. It then selects Catch arm ordinal 0, whose resolved operation is `handled`; that arm must have the same unit-operation shape and `handled.id.family == row.concrete[0]`. It also requires the parameter itself as Catch scrutinee, exactly two arms, a unit payload, wildcard continuation, and the prescribed arm bodies. `SelectedCatchArmEvidence` retains the actual Catch occurrence, arm source/range, operation source, declaration and operation ID.

2. The provider operation ID is captured from the resolved caller-side operation. `source_operation_match` authenticates the provider ID against that declaration and authenticates the selected arm against the same assembled Catch, ordinal 0, and its retained declaration/ID. It returns `Match` only when `selected_arm.operation_identity == provider_identity`. Since `SourceOperationId` equality implies equality of its `family` projection, a matching provider has `provider_identity.family == handled.id.family == row.concrete[0]`. A known different operation yields `KnownUnmatched`; it cannot enter the suppression branch. Spelling equality is not used.

3. The source collector constructs `Action::FormalEntry` from the actual lambda parameter annotation: it clones `parameter.annotation`, uses the lambda expression occurrence, and selects the registration indexed by that parameter's `HirParameterId`. The action executor passes those values to `candidate_formal_entry_annotation`. That constructor checks computation-formal role, registration owner against annotation owner, exact registered parameter recipe, source-owner mapping at the action occurrence, scope, and that the registered Lambda expression at the source owner/index has the same occurrence and registered parameter. It rejects an existing formal domain and duplicate permission for the registration. For a nonempty row it copies `row.concrete` in order into `FormalEntryPermission`, together with the registration, formal/parameter, Lambda occurrence, source owner, scope, annotation and source-row positions, and entry-effect ordinal. The optional row-variable equality targets that same entry port; concrete permission contributes no inflow constraint.

4. The `lib.rs` Internal-incidence query joins the exact `DefinitionUse` and its target/receiving definition owners, the unique Internal route and slot-0 fact, then the unique computation registration and Lambda recipe at the use's target root component. It verifies the original source Lambda occurrence/formal, the unique `LambdaArgumentEffectOrigin` for that registration and Lambda, and the negative effect argument term's ordinal equals that origin's entry-effect row. It calls `internal_formal_entry_permission` with this same registration, Lambda occurrence, target root and entry ordinal. That lookup returns only the unique retained record for the registration and checks formal/parameter recipe, source owner/target root, scope, occurrence, entry port and nonempty concrete vector. Thus the permission used by the certificate is the retained copy produced for this source Lambda, not another formal selected by a row image or provider value.

5. The provider endpoint scan requires an operation-origin view with the exact provider occurrence and declaration pointer. It selects a member only when that member equals the provider operation family and the view tail is closed. The certificate additionally requires one matching provider endpoint and lower paths from both the retained permission's entry-effect row and original Catch slot-51 lower fact to that exact endpoint. In `complete_residual_plan`, `Suppress` is created only in the `SourceOperationMatch::Match` arm for that provider-origin member and only after the certificate returns the same endpoint, view pointer and Catch fact. Therefore the member family is `row.concrete[0]`, and the retained permission vector copied from that same source row contains it.

This establishes a selected-member permission fact for successful suppression. It does **not** assert that every member reaching the open Catch input is annotated: other terminal endpoints, including an additional `write` inflow, remain `Forward` unless independently matching the selected provider operation and certificate.

## Parent/source/native correspondence and reused evidence

- R39's reviewed bounded contribution supplies source-owned retention of the concrete formal-entry permission, preserving its identity and ordered row while leaving input inflow open. It did not establish provider arrival or suppression.
- R45's bounded owner-incidence construction supplies the exact Internal-use → target definition → registered Lambda → negative entry-effect row → retained permission join. R62's reviewed policy preserves the source-drain/root validation order on the first physical entry edge. R54's same-owner finite projection remains conditional on its still-open semantic extraction premise.
- R115 precisely identified the earlier missing comparison between provider member and retained permission. The current trace closes that bounded comparison from source constructors: singleton Catch permission row, selected-arm family check, operation-ID equality, and producer copy into the retained permission. It does not close R115's broader Rust-to-inventory/Native extraction, original A/B, source/native theorem, general consumer or production gates.
- Existing baseline tests include exact `signal` suppression and a same-spelling `write::ping` case that expects `write` to be forwarded while `signal` is absent from the result. These are inspected source evidence only; no test was run. The Rust experiment is private and feature-gated; this does not authorize cutover.

## Diff, checks, budget and boundary

Source diff: none. I read only the four exact Rust blobs pinned above, issuing read-only `git show d177c46ec61fcadd70a3d587c2f8934f6bc91f46:<exact pinned path>` queries; their observed SHA-256 values matched the contract. No dirty worktree Rust source was read. The R115 and R39/R45/R54/R62 handoffs/outcomes cited above were used only for their bounded claims.

Checks: static source-constructor and identity-chain inspection only. No compiler, Cargo, build, tests, Lean, Lake, checker, formatter, scratch, cache, worktree, mount, environment experiment, or Git mutation was used. No source file changed. No new disposable scratch path was created. Only this leased handoff was written.

Budget: finite source-lane cap 480 seconds; exact elapsed/resource telemetry unavailable, so actual spent/remaining time is UNKNOWN. No descendants or generated outputs exist.

Unresolved premises: source-to-constraints/native faithful extraction; the original parent theorem and its full quantifiers; whole-language soundness, complete effect hygiene, principality, termination, source/native correspondence and production remain OPEN. R114 App/Lambda admission transport remains OPEN. This source result is not independent review and cannot authorize source promotion.

Mutual TODO: `R116-SOURCE-TO-NATIVE-PERMISSION-1`; original parent is the unchanged inference-soundness/effect-hygiene obligation; first missing evidence is construction of the same source-row/selected-arm/provider-member/retained-permission identities in the original semantic `Context`/`Inputs` and their native consumer; source owner is the source constraint and residual-consumer bridge; required inputs are the R39 retained permission, R45 owner incidence, this selected-member derivation, and authenticated source/native extraction; proposed output is a source-to-native theorem for the same selected endpoint; falsifier is any successful source-reachable suppression whose selected provider family differs from the same formal row's concrete permission. This requests evidence only and does not extend this lease.

Worker state: STOPPED for this assignment; writes stopped after this frozen handoff. No descendants, generated outputs, or disposable scratch paths remain. Pending fresh independent review and Luna adjudication/integration.
