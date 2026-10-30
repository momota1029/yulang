# R47 Rust handoff — current emission ownership for an Internal entry

Sprint / contract: EFFECT-PERMISSION-CURRENT-EMISSION / R47, contract SHA-256 `af75bcc2dcf6103fe3e3cabfb33f4ce0de91c516acacbe09f74af3a6dfe58d70`; admission SHA-256 `0de99112d82388c050acfe10799d7e0d1af51ed8960a81f4d893519055db4b64`.

Assignment / revision: R47 Rust / handoff revision 1. Parent scope: determine whether a retained bound emission can be joined to its exact current physical entry slot, owning admission and a retained relation ancestry rooted in the complete R45 Internal use. This does not establish provider arrival, Catch selection, residual subtraction, A/B closure, hygiene closure or production authority.

## Frozen inputs and provenance

The R47 contract/admission and all source dependencies below were hashed in this checkout before source edits. Their frozen values still match at freeze, except for the two leased source files changed by this assignment.

- Baseline commit named by R47 admission: `8017b53f5`.
- Leased source baselines: `candidate_context.rs` `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38`; `candidate_receiver.rs` `f5bff0d8aa7a20551fb2c5ad60b7b2b41907f471a55068a9ec1ae61ceba02911`.
- Read-only inputs: `candidate_effect.rs` `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3`; `candidate_scheme.rs` `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631`; `lib.rs` `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`; `candidate_extrusion.rs` `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`.
- R45 source bridge: `InternalPermissionIncidenceR45.lean` `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`; Rust handoff `5ca8058e79015b4896260c19aa2b389449324e223c169419fd873177910c4341`; review `a4e40d0b5ced25574e821047727cdcba21c35bb7d6701e6641ed0869b6647c6b`.
- R46 source bridge: `InternalEntryArrivalR46.lean` `3429aef705d2c059c23c8ec0a33dd1e4a6dcb75c9461e90f4380df679146f3c3`; Rust handoff `5874c13e7332037c1884e63c35966d5f237a9fa1bb09d4696084eb2a32b44831`; proof handoff `f88845dfc5f7e62683e820546f3467c9ce598e786107f5ceee608025bcbf8bf7`.
- R46 review provenance: the R47 contract pins review hash `7fbaed174bee5cae7a92874ddd795b9b80ec1bc8cd7f18acc30e6dedfde7c56e`; I read the current corrected review bytes only, hash `6e4080fe9a7b35a23e93bfebc793f15e8652403df98279fec36fd299e8312090`. I did not inspect the pinned pre-correction review bytes. R46 outcome hash `1edec9719f82f14f25c6ceaea3e858b68ba312c5fb417b8b985653dea3faa430` was inventoried by hash only; its content was not read. My source join reasoning uses R45 and current source records, not the R46 review/outcome; this review-hash correction does not affect it.

Requested model/effort: Luna/high implementation lane per assignment. Observed model/effort, authenticated worker/session ID, and active-work duration: UNKNOWN in this worker view. No descendants. Resource telemetry (CPU/RSS) unavailable. No build/test/compiler resource use.

## Outcome and source correspondence

Outcome class: provisional private source-native evidence. The private query is implemented in the leased paths and returns either a borrowed certificate pair or a precise `CurrentEmissionGap`. It adds no retained identity, no producer evidence, no consumer and no solver state.

`ReceivingResidualExperiment::current_internal_emission(index)` first obtains the existing `InternalFormalPermissionIncidence` for the unique complete `DefinitionUseId` in the batch and verifies its target/receiving owners against this experiment's source roots. It takes the permission's actual `entry_effect` row, then requires the indexed emission's physical owner to be exactly `RowKey::Effect(entry_effect)` and its lane to be a positive lower row or lower atom.

The receiver reconstructs the current bound by indexing `effect_bounds[owner].direct_lower_rows[index]` or `exact_non_variable_lowers[index]`. The context query requires the current key, retained emission key, constructor readback key, physical/readback slot and referenced retained admission key to agree. It rejects another emission for the same physical slot. Each emission's own admission index is followed directly; I removed an initially considered singleton-emission-per-admission restriction because the owner relation is the emission's explicit admission ID, and the contract does not require reverse uniqueness.

The referenced admission must have a relation whose exact retained pair is `bound_pair(admission.bound)`. The root pair is reconstructed from the R45 certificate's exact admitted `internal_fact` lower/upper terms with the corresponding positive/negative endpoint maps. The occurrence is the same use's `ConstraintOccurrenceId::new(use_record.occurrence.clone(), 0)`, matching `route_internal_inner`/`route_many` source construction. The context lookup requires exactly one retained `Origin` with that occurrence and root pair, then a completed `SourceDrainReceipt` whose `origin_index`, `created_seed` and `selected_relation` identify that same root, with no incoming relation or replay acknowledgement and exact matching cause occurrence/task pair. Finally it walks only retained `Dependency` parents from the admission relation back to that root; invalid references, absence and work-limit exhaustion return unavailable.

Identity is anchored by the R45 complete use certificate, exact source occurrence, retained origin and completed source receipt. Endpoint-pair equality is used only as one checked equation inside that chain; row, term, provider, family, history or canonical equality alone does not create identity. The result keeps the same borrowed R45 permission and same retained admission/emission records.

## Falsifiers and limits

The query fails closed for missing emission/admission/relation/root, duplicate physical slot, foreign relation pair, wrong raw entry row/lane, current-slot mismatch, malformed or duplicate root, invalid dependency references, absent ancestry and bounded-search exhaustion. A mismatch in current value catches stale readback when the physical slot has changed; duplicate retained emission at the slot is also rejected. Transaction rollback is represented by the existing checkpoint/truncation behavior of evidence records; if rollback removes a record, this lookup returns unavailable. No injected rollback experiment was run, and no independent generation/ABA theorem is claimed for equal values recreated at a slot. The enclosing successful experiment lifecycle and retained logs remain source obligations for review.

This certificate does not conclude provider arrival or `arrivalAtEntry`, does not inspect operation provider occurrence/declaration for this join, does not classify Catch suppression/forwarding, and does not authorize subtraction. The current physical read proves only the indexed entry-row bound currently stored there, coupled to the exact R45 entry row and retained ancestry checks.

## Delta, checks, and resources

After source edits, SHA-256:

- `crates/yu-solver/src/candidate_context.rs`: `184f09e91221f8ae0969d1dbc792b7707ef5571ff56d96e276467641215bf32e`.
- `crates/yu-solver/src/candidate_receiver.rs`: `1426526cad48d4bc02984e0a5967e30e50cd188cb01fbeb71bc6f15442e59448`.
- R47 contract/admission rechecked at freeze: `af75bcc2dcf6103fe3e3cabfb33f4ce0de91c516acacbe09f74af3a6dfe58d70` / `0de99112d82388c050acfe10799d7e0d1af51ed8960a81f4d893519055db4b64`.
- All read-only source pins above were rehashed at freeze and remained unchanged.

Only the two leased Rust files and this assigned handoff were written by this lane. No Git diff/status or other Git operation was used, so this handoff reports exact per-file baseline/final hashes and lane ownership without asserting a workspace-wide isolated diff. Existing unrelated dirty/deleted paths were preserved; no other path was written and no scratch/disposable path was created.

Static source review only. No build, test, Cargo, Lake, compiler, formatter, target/cache/scratch/environment/worktree operation or nested CLI was run. No tests were added or run. No source expectations, diagnostics, input domain or natural inference behavior changed. Assignment budget is at most 1,200 seconds; actual active-time spent/remaining is UNKNOWN in this worker view. No separately measured resource telemetry is available.

Next in-envelope step: none. Freeze these exact bytes for independent review of source correspondence, rollback/current-read semantics, per-slot ambiguity and dependency ancestry. Any need for producer retention or transition changes requires a new lease.

Worker state: STOPPED; writes ceased after this handoff. No descendants or generated outputs. No commit performed by this worker. This is a frozen implementation artifact, not its own review or a theorem closure.

STOP.
