# Applied local-use structural retention correspondence

Status: candidate source/native correspondence and conditional application of corrected M2; independent review NOT RUN. No parent or production closure.
Assignment: `LOCAL-USE-RETENTION-APPLIED-CORRESPONDENCE-20261017`, revision 1.
Sprint: `local-use-retention-implementation-20261017`, contract revision 1.
Author: `/root/local_use_retention_applied_proof`, sole author; no descendants.
Requested role/model/effort: prover / `gpt-6.1-sol` / high. Observed effective model/effort: UNKNOWN / UNKNOWN; no model-switch claim.
Administrative baseline supplied by Luna: `9a2c7d80826ae33493f2bcc4786bc06e450ae36a`; no Git inspection.

## Parent application

`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN over all original providers, assignments, worlds, contexts, source occurrences, typed positions, guards, continuations, interactions, Call demands and futures. F1/FK1 remain independent. The adopted source interface is NPAIR §§2–4 under the adoption receipt pinned below. Ordinary Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying Value-SCC intrusion and generalization remain required.

For `f () -> install(g) -> fresh local use -> g ()`, this patch removes one specific structural loss: successful local-use commit now retains every existing FreshUse field alongside the exact captured Graph. Previously only Graph/rows survived. Thus corrected M2's map-retention premise is now supplied by actual commit code for its finite Qmap subset. This supplies neither a complete presentation map `rho_u` nor the missing semantic operands that Qmap never contained. J1/J2 and initializer effects remain separate; one local route action discharges no foreign-continuation quantifier.

## Actual ownership construction

Locators refer to applied `candidate_scheme.rs` SHA-256 `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`.

`route_candidate_local_run` (:1552–1581) captures the installed root, constructs `FreshUse`, and charges Graph/fresh payload before putting them in `LocalUse`. `prepare_candidate_fresh_use` (:1134–1408) remains unchanged by the patch. Therefore the corrected proof's M1 constructor coordinates remain applicable: canonical eligible row copies, all four Function children, native contribution endpoint copies, bound-context/scope/bundle/evidence maps. In particular a graph-node coordinate requires its exact Graph, a row image may be shared, and a contribution endpoint is not a provider witness.

`FreshUse::into_retained_parts` (:210–215) destructures all nine fields exhaustively. It moves `rows` into one result and all other fields into one `RetainedFreshUseMaps`. `commit_local_use` (:298–321) moves those results and `frame.graph` into one `LocalFreshRoute`, retaining slot/local/occurrence. No field is reconstructed, filtered or rekeyed.

| Precommit field | Unique postcommit owner | Preserved coordinate |
| --- | --- | --- |
| Graph | `LocalFreshRoute.graph` | exact graph-local domains/metadata |
| rows | `LocalFreshRoute.rows` | Graph row index -> stored RowKey |
| scope_remap | `route.retained.scope_remap` | original region/scope/input IDs and membership |
| scoped_relations | `route.retained.scoped_relations` | captured parent RelationId -> copied ScopedFlow |
| context_use | `route.retained.context_use` | actual allocated scalar use counter |
| terms | `route.retained.terms` | Graph node index -> Option<Term> |
| effect_operands | `route.retained.effect_operands` | Graph operand-node index -> native endpoint |
| bundle_remap | `route.retained.bundle_remap` | original bundle ID -> retained bundle ID |
| context_remap | `route.retained.context_remap` | visited source context ID -> target context ID |
| evidence_remap | `route.retained.evidence_remap` | Graph.bound_evidence index -> imported snapshot ID |

Rust moves preserve collection contents, domains, misses, capacities and association; exhaustive destructuring prevents an omitted FreshUse field. The row vector has a sole route owner. The retained record's scalar is inline; the other seven fields contain collection storage, with three maps inside scope_remap. Ownership of native referent payloads remains in their session term/effect/context/scope owners. This is not global identity uniqueness, an inverse map, or a public postcommit lookup API.

The production publication path is `step_candidate_local_use` (:1694–1734) -> `lib::finish_route_transaction_with_candidate_accounting` (:9281–9331) -> `GraphState::commit_local_use`. Restoration consumes fresh term/operand images at `begin_candidate_fresh_bound`, then admits the mapped root-to-use link. Route capacity is reserved and sampled before `cursor.complete=true`. The success branch commits only a completed frame after the fallible operation returns Ok; the split itself moves allocated values and adds no fallible step. The old allocation is retained in the journal until success. An exclusive session borrow and no callback in this transfer prevent observation of a partial collection. This is the successful production route boundary, not cross-thread atomicity. The existing cfg(test) census may clone selected maps before the transfer; it is separate optional instrumentation, excluded from the allocation-free production statement.

`shadow_apply::fresh_use` (:353–378) still validates errors, occurrence ownership and local identity, and returns the same route Graph/rows references. It does not expose the newly retained record or interpret it as NPAIR evidence.

## Capacity-accounting derivation

Let `B_T(c)=c*size_of(T)` with the source's checked arithmetic. Let R be `B_RowKey(rows.capacity())`. Let H be the sum of the seven summands in `RetainedFreshUseMaps::bytes` (:153–162): scope_remap.bytes, scoped relation capacity, term capacity, effect operand capacity, bundle-map capacity, context-map capacity and evidence-vector capacity. `ScopeRemap::bytes` at candidate_source.rs:124 counts each of its region/scope/input map capacities once. Let G be Graph.bytes.

Termwise comparison with `FreshUse::bytes` (:203–208) gives **FreshUse.bytes = R + H**, whenever those checked sums succeed. Moving the fields changes no capacities, so a frame's payload contribution `G+FreshUse.bytes` becomes the route's `G+R+H` exactly. `refresh_bytes` (:322–343) enumerates both forms with this identity. It counts backing payloads once according to ownership, including each retained non-row map, and never puts rows in H.

Inline headers are charged separately by the capacity of the containing vectors: `B_LocalUse(local_use.capacity())` and `B_LocalFreshRoute(local_routes.capacity())`. These include nested Graph, FreshUse or retained-record headers, scalar context_use and padding. Their payload methods exclude these inline headers. Popping a frame changes length, not vector capacity, so the LocalUse header allocation stays charged. Pushing into already reserved local_routes changes length, not capacity. Therefore commit's correct incremental retained-byte change is zero; the old subtraction of H would now undercharge live maps.

If the route vector grows from capacity c to c', `step_candidate_local_use` adds `(c'-c)*size_of(LocalFreshRoute)` before completion, using the actual enlarged route type. It moves existing entries into the replacement without cloning payloads. The old allocation, emptied of entries, is journal-owned; `lib.rs` resource accounting (:10709 onward) separately adds its full `c*size_of(LocalFreshRoute)`. Thus the live vector plus undo allocation are both accounted during growth. On success the undo allocation drops; on rollback entries move back and `refresh_bytes` recomputes the retained census. Native referent payloads remain charged by their own owners.

These identities concern the compiler's capacity accounting, not allocator bucket overhead, exact physical bytes, measured peaks or unchanged resource acceptance. Retention increases memory and may cause earlier resource-limit rejection; the practical envelope is unmeasured. No new allocation occurs at the production commit split itself.

## Corrected M2 application and lifetime

Fix the actual precommit state v0, exact Graph/session association, and any finite registered structural Qmap expression from corrected M2 §4. This includes only stored-field lookups, Graph metadata, finite compositions and enumerated native read projections whose intermediate IDs resolve. A map miss or None remains that structural answer. It implies no absent At, empty inflow or permanent future ineligibility.

The transfer above supplies M2's unchanged-map/domain/association premise for every original FreshUse field. For each postcommit evaluation **valid at v0**, direct lookup equals its precommit answer. For a dereference, require the same live owner identity, no removed/reused ID, no stale raw pointer after relocation, and unchanged exact read projection or a genuinely retained immutable v0 projection. Induction over the finite query expression then gives `q_post(v0)=q_pre(v0)`. The implementation adds no runtime query registration, version field, historical projection or Invalid(v0) checker. A changed/unavailable projection is outside equality; invalidation remains a distinct outcome for any future checking protocol.

The success path calls `commit_replay_operations` before route publication; candidate_context.rs:1899 onward can retire completed replay state. A query dereferencing such removed state is not valid at v0 merely because a related ID/map survives. Likewise a stored RowKey remains numerically equal while its later canonical representative may change; canonicalization is a distinct projection needing its own v0 validity. These conditions are not discharged by map movement.

`lib::rollback_route_transaction` (:9429 onward) restores intrusion/source/cursor, clears a new uncommitted frame, truncates routes and moves surviving entries into the old allocation. Truncation drops the newly route-owned retained maps along with Graph/rows. Session suffix rollback may remove referents and reuse IDs. No escaping-reference or arbitrary outer-rollback lifetime follows. Later checkpoints that already include a committed route and its referents can preserve those prefixes, subject to the same projection conditions. Session replacement/destruction ends that owner identity. This patch does not establish universal monotonic IDs or require exact private-capacity restoration for inference correctness.

## Reuse, remaining premise and next owner

Reused: corrected M2 revision 2 only with valid pinned-v0 evaluations and explicit lifetime premises; unchanged M1 constructor correspondence; the approved rows-preserving split and accepted memory tradeoff. The actual source diff against the pinned pre-retention snapshot contains exactly the retained record, exhaustive split, commit transfer/removal of release subtraction and route payload census. No ordinary constraint producer or consumer is changed. Historical revision-1 M2 equality across invalidation is rejected. Broader conditional R1, anchor/J2 and architecture candidates are not promoted to a whole-presentation theorem here.

**NPAIR-NATIVE-INTRO** remains the first semantic producer obligation: `candidate_effect::candidate_formal_pair` (:1119), `candidate_formal_effect_port` (:1145) and `candidate_formal_annotation` (:1191) must actually emit the adopted shared negative port plus occurrence descriptor/Permission and both ordinary formal edges. The present negative-concrete guard still fails before construction; moving maps cannot cure that. Removing the guard alone is insufficient. The source annotation/Function constructor owner, assigned by Luna, owns this missing evidence; mixed/multiple-symbolic forms retain their original C_sym obligation and accepted source domain.

**NPAIR-REPLAY-AUTHENTICATION-20261017** then needs actual `At(D,w,delta)` production from native constraint/Function propagation (`candidate_constrain_live_effect`, real Function child comparisons and candidate_context bound/replay transport), with exact provider/contribution/use/scope/lineage and tail/future dependencies. `prepare_candidate_fresh_use` and `begin_candidate_fresh_bound` now retain existing structural crosswalks but do not emit these semantic records. Their owners must establish whole-presentation transport through capture/use, extrusion and qualifying intrusion, and compatibility of direct/annotated ordering before dependent publication. Falsifier: two equal-family contributions or uses are identified, a required derivation is lost, or an absent/pending association permits finalization.

**NPAIR-RESIDUAL-OWNER** requires Luna and the original source effect-elimination owner to identify the real native consumer h, its actual g() demand/J2, same-contribution transport, scope/eligibility and selecting evidence, then derive the contribution-indexed residual while preserving independent contributions and consumer effects. No concrete receive subtraction symbol is established by these inputs; `shadow_apply::admit_candidate_fact` supplies demand formation, and Catch experiments cannot fill the missing consumer. The receive specimen itself supplies no Catch subtraction event. Falsifier: permission/map retention alone removes a contribution or publishes a residual before actual selection/dependency completion. This is an evidence TODO, not a code lease or consumer design choice.

The exact next step after fresh review is Luna's owner-directed NPAIR-NATIVE-INTRO evidence packet, retaining NPAIR-REPLAY-AUTHENTICATION and NPAIR-RESIDUAL-OWNER as dependent open obligations. Whole rho_u, authentic At, source/native adequacy, N-Transport, N-Subtract-Elim, F1/FK1, complete Call/effects, source-Generalize, soundness, principality, F5 and production remain OPEN. This assignment ends here; no additional semantic implementation is authorized.

## Frozen inputs, checks and cessation

| Direct dependency | SHA-256 |
| --- | --- |
| sprint contract revision 1 | `c6ed05c5ed10e16d97cfe4e367af5f2bc2a8e650f2169ec8e8d81b7df81e9935` |
| approval receipt | `356231ad001a02c5085119412af26534e56e38082aca747262e8873ffa67f13c` |
| implementation handoff, revised primary check receipt | `e78fd6cee9c1afeac740158b45084647dc495b963ddbafaad00f9f8f26b9b009` |
| applied candidate_scheme.rs | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| pre-retention candidate_scheme snapshot | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| approved code-contract proposal | `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a` |
| corrected M2 existing-map proof revision 2 | `f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e` |
| adopted negative-formal-pair definition | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| source-formation adoption receipt | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| native implementation-readiness contract revision 2 | `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064` |
| lib.rs | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| shadow_apply.rs | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| candidate_context.rs | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| candidate_effect.rs | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |

Implementation/proposal/approval author: Luna `/root`; corrected M2 author: `/root/local_use_existing_map_retention`; NPAIR definition author: `/root/negative_formal_pair_proposal`. This artifact's source conclusions are the present author's static derivation, not independent certification. Governing receipts supply approval/review provenance only within their original scopes.

Checks: actual-byte hashes, static source/snapshot diff, field/accounting/publication/rollback inspection. No tests, builds, probes, compiler execution, Git or external contact by this worker. Luna's revised handoff separately reports `cargo check -p yu-solver --features shadow-apply-candidate --tests` passed in 9.12s with no tests run; that is reported compile evidence, not this proof's method or theorem evidence. No physical-memory measurement or executed source-qualified counterexample.

Four bounded stages: pins/authority; applied ownership/accounting; conditional parent application/next owners; frozen handoff. Conservatively charge full allocated 360s, remaining assignment budget zero; exact active elapsed UNKNOWN. Sole new paths: this artifact and `tasks/agent-loop/inbox/20261017-local-use-retention-applied-correspondence.md`; no scratch paths. Writer STOPPED on frozen handoff submission; no descendants or unresolved descendant leases. Fresh independent review/adjudication belongs to Luna; producer cannot certify this result.
