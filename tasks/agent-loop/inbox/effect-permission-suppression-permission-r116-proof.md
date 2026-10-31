# R116 proof handoff — selected suppression permission

Sprint `EFFECT-PERMISSION-SUPPRESSION-PERMISSION/20261102-R116`, contract revision 1, SHA-256 `1dee9e909ba3050f80146eb0657ecc0d2e563ea15cd4c516b0f6ae7ba602d5f6`.
Assignment `/root/r116_proof`, handoff revision 1. Claim class: conditional finite constructor algebra, **CONSTRUCTED / UNCHECKED**. No kernel acceptance, independent review, Rust extraction or production authority is claimed.

## Files, sources and pins

Only these two leased outputs were written:

- `notes/theory/lean/YulangClosure/SuppressionPermissionR116.lean`, frozen SHA-256 `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`.
- This handoff; its final SHA-256 is reported externally to avoid a self-hash cycle.

No scratch, generated output, cache, root import, compiler file or shared status was written. Other writers' changes were preserved.

Direct imports are `YulangClosure.InternalPermissionIncidenceR45` (`9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`) and `YulangClosure.OwnedResidualProjectionR54` (`cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`). The exact transitive dependency actually used for producer facts is `YulangClosure.ComputationPermissionEntryR39` (`748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`), specifically `exact_row_retained`, `prepare`, `permissionFor`, `Valid`, and their record types. R54 supplies `Owner`, `Owned`, `join`, and `same_owner_composition`. R45 supplies its exact probe/certificate types, `extract`, and `accepted_payload`. No imported theorem from outside these pinned modules/their exact transitive imports is used.

Source evidence is the corrected frozen `tasks/agent-loop/inbox/effect-permission-suppression-permission-r116-source.md`, SHA-256 `879d1653d1b24b86dc707b52283cd13dbc73f3e8ad56dcfdf1515aee64064444`, immutable Rust revision `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. The earlier source handoff hash `ea940af573abaffcc1d6cb07fcc7847ea41774aefa711dd38c32b93e24f57256` had a copied R114 contract hash; primary reports the author corrected only that header. This handoff uses the corrected revision. Proof author read this source handoff, not dirty Rust bytes, and does not independently certify its source trace.

Original semantic authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, including contravariant local subtraction, resolved identities, computation argument example, `[signal, write]` inflow, and permission/inflow/residual separation. The original parent remains `SourceProblem.InferenceSoundness` in `Contracts.lean`: for all supported `s`, scopes `x`, generated `d` and solutions `a`, successful generation/solving must yield one source witness `e` with `sourceJudgment s x e ∧ sameScoped s x e a`. No quantifier or source constructor is removed. `docs/yulang-whole-proof-closure-ja.md` §§1,3,4 and its current birth-level correction preserve full language, shared evidence, observation and inference obligations. `OriginalSourceGeneration.lean` opening, operationArm clause and reconstruction roots retain actual operation-rigid binders, continuation contracts and original contexts; this packet supplies no new concrete Kernel/Checking instance. `FormalPermissionAnnotatedRelay.lean` opening and final parent application distinguish source construction from execution arrival; `FormalPermissionSourceAllocation.lean` opening retains the Rust-execution/transcription gap. These draft integration records add no semantic authority.

## Constructed declarations and exact scope

All names below are in `YulangClosure.SuppressionPermissionR116`. Their complete intended types are present in the frozen Lean file, with an unexecuted `#check @...` and `#print axioms ...` for every theorem.

1. `producer_facts`: for arbitrary complete identity type `Id` with decidable equality, `e,a,f,r,port,p`, R39 `prepare e a = some (f,r,port)` and `permissionFor a f r port = some p` derive the named `ProducerFacts`. These include exact registration, formal identity, source occurrence, annotation owner, formal owner, source-owner lookup, source Lambda/formal, scope, annotation/row positions, entry port and `p.concrete = r.concrete`. They are derived from actual R39 constructor equations, not assumed as a LocalLaw.
2. `operation_match_identity`: successful narrow `operationMatch` yields equality of complete resolved operation identity, declaration and family. Provider and handler occurrences and spellings remain separate fields; equal occurrences are not required. This is a comparison transcription, not an implementation of all `source_operation_match` guards.
3. `selected_provider_member`: producer success plus `SelectedSource a r arm` (the SAME annotation row read and `r.concrete = [arm.family]`) and matching provider/arm operation implies `ProducerFacts ... ∧ provider.family ∈ p.concrete`. Membership is derived by exact copy, singleton equality and family equality; it is nowhere a hypothesis.
4. `selected_endpoint_member`: the preceding premises plus `endpoint = provider.family` derive membership of that selected endpoint in the retained concrete vector. The endpoint equality mirrors the provider-origin member check; authenticated Rust/native decoding remains open.
5. `same_source_row`: two successful row reads from the SAME source action imply exact row equality. Equal spellings or canonical images do not join different formals.
6. `internal_certificate_member`: applies the result to the SAME `probe.permission` accepted by R45 `extract`, deriving the output certificate's registration, source occurrence, owner and selected provider membership. The original R45 owning-read/native-identity prerequisites remain in `accepted`; this theorem does not construct those source/native inputs.
7. `same_owner_selected_join`: directly applies R54 `same_owner_composition` to the actual permission/arm values, under equality of state AND batch owner. It does not infer owner identity from equal payload or batch alone.
8. `empty_concrete_no_retained`: an empty concrete source row makes R39 `permissionFor` return none. No provider membership is available from that case.
9. `different_formal_not_same_permission`: registration inequality excludes the derived ProducerFacts for that action.
10. `same_spelling_different_operation_rejected`: same spelling plus unequal complete operation identity yields the narrow comparison's false result.
11. `provider_handler_family_mismatch`: unequal family excludes the narrow comparison.
12. `open_input_write_boundary`: for arbitrary distinct signal/write identities, signal belongs to its singleton permission, write belongs to the two-member inflow and not the permission, and filtering only signal leaves write. This is finite list algebra, not a native propagation/residual theorem.

`ProducerFacts` is a named proposition record whose concrete instance is constructed by theorem 1. `SelectedSource` contains only constructor identities and singleton shape, never permission membership. Neither proposition record is described as whole-parent closure. No project axiom, sorry, admit, checker bypass, circular typing definition or whole-target extraction law was introduced.

## Source correspondence and remaining bridge

The source lane's “Constructor chain and membership result” paragraphs 1–5 give the exact inspected owners:

- `candidate_receiver.rs::assemble`: actual Lambda parameter annotation row singleton, selected Catch arm ordinal 0 and `handled.id.family == row.concrete[0]`.
- `source_operation_match`: full selected-arm/provider `SourceOperationId` equality after authenticating provider declaration and the same Catch/ordinal/arm evidence. This is stronger than spelling equality; its family projection supports the membership chain.
- `candidate_source.rs` collector `Action::FormalEntry`: actual parameter annotation clone, same Lambda occurrence and parameter-indexed registration.
- `candidate_effect.rs::candidate_formal_entry_annotation`: computation role, owner/parameter recipe/scope/source-owner/Lambda identity checks and ordered copy of that exact row into retained permission. R39 models this cut, including no concrete permission inflow.
- `lib.rs` Internal incidence and `internal_formal_entry_permission`: same target owner, registration, Lambda/formal, negative entry port and unique permission. R45 models the conditional owner-incidence cut; it does not authenticate Rust reads by itself.
- Provider view/member check and `complete_residual_plan`: the exact provider member equals the provider operation family; only the matching successful certificate branch creates Suppress. `selected_endpoint_member` retains this equality explicitly.

These are source-owned guard/constructor premises supported by the independent source author's inspected immutable blobs. Lean has no Rust operational relation, authenticated decoder, Catch fact/path/view identity extractor or theorem that actual successful Suppress yields these model premises. `operationMatch` is deliberately a narrow necessary-comparison model, not an equivalence to the full Rust function. Complete source operation identity, declaration and family are separate fields; their coherence with native representations must be constructed by the bridge owner. Similarly, R54 owner equality must come from the same live state read, not a fabricated numeric equality.

Parent application: the local selected-member comparison missing in R115 now has a concrete equality-chain candidate and a static source-owner trace. It does not assert that all open input members are concrete permission members. General callback/result nesting, arbitrary arm lists, multiple concrete annotations, symbolic row propagation, freshened use context, provider arrival, current world, handler continuation, observation equality, replay, principal coverage and termination are not discharged. These cases remain in the original parent source domain and are not claimed false or excluded from it. R114 App/Lambda admission transport also remains OPEN.

First remaining premise / owner: `R116-SOURCE-TO-NATIVE-PERMISSION-1`, source constraint and residual-consumer bridge owner. Construct authenticated reads that map the same actual formal annotation, registered Lambda/owner, retained vector, selected arm, full provider operation and certified endpoint into these exact objects and establish the native-successful-Suppress antecedents, then apply `selected_endpoint_member`/`internal_certificate_member` inside the original semantic Context/Inputs. A falsifier is an actual successful source-reachable suppression with a different selected endpoint family from the same formal's retained row; arbitrary unauthenticated numeric models are insufficient.

## Actual checks, resources and stop

Static reads and SHA-256 commands exited 0. Actual project files were read: `lean-toolchain` pins `leanprover/lean4:v4.35.0`; `lakefile.toml` uses `-j1`, `-M1024`; manifest has no external packages. No installed executable/version was queried or invoked because the fixed R116 packet explicitly prohibits Lean/Lake/checker execution. Every delivered declaration is CONSTRUCTED/UNCHECKED. Actual diagnostics, goal states, theorem-type prints, per-theorem axiom results and kernel exit codes: **NOT RUN / unavailable**. The embedded audit commands are future work, not receipts; no axiom-free or accepted-theorem claim follows from them.

No Lean, Lake, checker, Cargo, compiler, build, test, installation, environment experiment, mount, worktree, cache, descendants, user/third-party contact or Git operation was used. Author resource envelope: 300 seconds; exact external wall-clock/CPU/RSS telemetry was not exposed, actual usage UNKNOWN. Writes are STOPPED and both leased outputs are frozen for primary-appointed independent static review. No descendants or generated/scratch outputs exist.
