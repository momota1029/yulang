# R117 Rust handoff — native provider member to retained permission

Sprint `EFFECT-PERMISSION-NATIVE-DECODER/20261102-R117`; contract SHA-256: `8eca5d0db24a42521706016e90175c5073e8f02146396ac0db964f0f7e08215c`.
Assignment `R117-RUST`, handoff revision 2. Claim class: **research patch candidate; uncompiled and unapplied**. This revision addresses three confirmed independent-review findings. It is not an implementation or source/native theorem.

## Original parent and bounded result

The original inference-soundness and effect-hygiene obligations, with their original source domain and quantifiers, remain OPEN. This patch only strengthens the private `SourceInternalProjection` / `ProviderNativeContextProjection` / `InventoryPackage` observation path. It does not edit ordinary solving, residual-plan construction, suppression decisions, diagnostics, source domains or expected output.

The selected provider endpoint is a native coordinate `AnnotationMember(view, member)`, not a source operation-family ID. In `ProviderNativeContextProjection::capture`, the candidate carries the exact owner inventory view and obtains the family only from that view's `allowed[member]`; the existing same-view pointer/index and provider-origin checks remain in force. The capture joins the Internal incidence permission to exactly one retained `FormalEntryPermission` by its authenticated `registration` field and all source identity fields, including the exact concrete-slice pointer. It does not equate the retained vector's storage position with a registration ID. It requires the decoded family in the retained concrete vector and full `SourceOperationId` equality across provider, selected Catch arm and provider-view origin declaration.

The real retained-inventory position is carried separately as `permission_index`. `InventoryPackage::capture` passes that exact position and borrowed record into the existing `InventoryCatchRequest`. `internal_root_view_from` then searches the actual package permission inventory by `permission.registration == request.registration`, requires exactly one match, checks its storage position against the carried `permission_index`, and compares the actual borrowed record with `std::ptr::eq(*permission, self.catch.permission)`. Thus a registration can differ from its compact retained-vector position.

Concrete static trace for the previously missed unequal-index case:

1. Formal registration 0 is unannotated, so it produces no retained entry-permission record.
2. Formal registration 1 is annotated and produces one record whose field is `registration = 1`.
3. The compact permission inventory is `[(storage position 0, record(registration 1))]`.
4. The unique registration-keyed source selection returns the record at storage position 0; the package request carries `permission_index = 0` and the record reference.
5. The package lookup by `permission.registration == 1` finds the same unique record at storage position 0, verifies the index and pointer, and continues. No executable test or runtime behavior is claimed.

## Frozen files and exact patch

- Patch: `tasks/agent-loop/artifacts/effect-permission-native-decoder-r117.patch`, SHA-256 `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`.
- This handoff: revision 2; final SHA-256 is supplied to Luna with the STOP receipt to avoid a self-hash cycle.
- Patch base and sole target: `crates/yu-solver/src/candidate_receiver.rs` at immutable `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, blob SHA-256 `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`.
- The six unified-diff hunks have header counts reconciled against their bodies. Their original base positions are 231, 603, 1860, 4844, 5052 and 5106. The patch was not applied to the dirty worktree and is uncompiled.

Other immutable R117 Rust dependency pins, read only by exact `git show` paths:

- `candidate_effect.rs`: `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`.
- `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- `lib.rs`: `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.

Reused evidence: R116 source handoff SHA-256 `879d1653d1b24b86dc707b52283cd13dbc73f3e8ad56dcfdf1515aee64064444`; R116 selected-member Lean candidate SHA-256 `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a`; R54 `OwnedResidualProjectionR54.lean` SHA-256 `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`; R45 `InternalPermissionIncidenceR45.lean` SHA-256 `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`.

## Guard sequence and rejected cases

1. Keep the projection within one experiment, collected `ConstraintBatch`, and live effect-algebra `State` by pointer identity.
2. Decode the typed native endpoint only through the exact owner inventory view's `allowed[member]`, requiring the same view pointer/index as the provider view, a closed tail, and the provider declaration's family. Member and family IDs are never equated numerically.
3. Preserve the existing `SourceInternalProjection::verify_owner_round_trips` source checks. Select exactly one retained record by `permission.registration`, compare its formal/parameter, source owner, Lambda occurrence, scope, annotation and row positions, entry-effect ordinal and concrete-slice pointer against the Internal permission, and require the provider family in the concrete vector. Keep its storage index distinct from its registration.
4. Tie provider view origin occurrence and declaration pointer to the provider source operation; check full operation identities for provider origin, provider identity, operation declaration, selected Catch arm and selected arm declaration.
5. Carry `provider_member_index`, decoded `provider_family`, retained `permission_index` and borrowed `permission` in `InventoryCatchRequest`. In `internal_root_view_from`, find the package permission uniquely by its registration field, then verify its retained storage position and `std::ptr::eq(*permission, self.catch.permission)` before consuming it with the existing registration/formal/source-owner/Lambda/annotation checks.

Falsifiers/rejections:

- An earlier unannotated formal followed by registration 1 at compact storage slot 0 is accepted through the distinct registration and storage-position fields; the prior index-equals-registration lookup would reject it.
- A duplicate registration permission fails the unique registration-keyed selection.
- A substituted or foreign permission fails its exact record pointer, stored position, source fields or concrete-slice identity.
- A same-spelling or same-family but distinct resolved operation ID fails full provider/arm identity equality.
- A forged or cross-owner numeric `AnnotationMember` fails owner view pointer/index checks; indices are not decoded as family IDs.
- A wrong member, open-tail view, absent permission family, foreign provider occurrence/declaration, or selected arm from another Catch fails the corresponding view, permission, occurrence, pointer or full-ID guard.
- A view from another session's effect state or a batch from another collection fails the added state/batch pointer checks.

Observer failures remain private projection failures. The patch adds no ordinary inference branch, rule, suppression path, public field or source acceptance rule. R116's bounded singleton Catch permission and operation-ID source trace supports the intended case but does not establish general source-to-native extraction.

## Review limits, checks and unresolved premises

Direct source read was limited to the exact four Rust blobs pinned above, using read-only `git show d177c46ec61fcadd70a3d587c2f8934f6bc91f46:<exact path>`. No dirty source path was read. R116, R54 and R45 were consulted only at their pinned handoff/model evidence. The static hunk audit counted all six old/new body lines; it did not apply the patch. No tests, compiler, Cargo, build, Lean, Lake, repository checker, formatter, patch application, scratch/temp path, worktree, cache, mount, environment experiment or Git mutation was used. The patch has no compile or executable evidence.

Requested model/effort: Luna/high implementation lane. Observed model/effort and runtime telemetry: UNKNOWN. This worker has no independent review authority.

Open premises include original source-to-constraints/native correspondence, R114 App/Lambda admission transport, all-language effect hygiene and inference soundness, principality, termination and production authority. This selected-member candidate closes none of those gates. It remains a provisional research artifact pending fresh independent review and later source integration under an authorized execution envelope.

Mutual TODO `R117-RUST-TO-PROOF-MAP-1`, revision 2: map the exact fields `provider_member_index`, `provider_family`, `permission_index`, `permission`, and the registration-keyed `internal_root_view_from` consumer guard to R116 endpoint/member and owner premises; name every remaining source/native premise and falsifier. Source owner is the private native decoder and owner-projection assembly. Required inputs are the R116 selected-member result plus R45/R54 owner projections. Proposed output is only a proof-to-candidate receipt map, not a theorem. Falsifier: any accepted package whose carried family, exact Internal retained permission, source operation identity and typed native member decode to different owners or families. The earlier-unannotated-formal trace above is required coverage for the map.

Paths written in this revision: this exact patch artifact and this exact handoff only. No scratch or disposable path was created. Writes are stopped; no descendants or generated outputs exist. Worker STOP receipt: this final revision and handoff are frozen, with no further writes. Pending fresh independent review and primary adjudication.
