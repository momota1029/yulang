# Native implementation contract for adopted negative effect pairs

Status: corrected implementation-readiness contract, revision 2; independent
delta review pending. No compiler code lease or semantic/production approval.
Original authoring sprint: `adopted-npair-construction-and-native-plan-20261017`,
contract revision 2, SHA-256 `0e4544b0833d0b5f7bbe61783b67882a1af13d6bf3a5b5c41ad50615c36aa12e`.
Authority-boundary repair sprint: `native-plan-authority-boundary-correction-20261017`,
contract revision 1, SHA-256 `14939b5254a4f1cc26c05b10acc33538d31d8988b7e5a11273a1fe37356d71d1`.
The pre-repair bytes are preserved at
`tasks/agent-loop/snapshots/20261017-negative-pair-native-implementation-contract-pre-repair.md`
(SHA-256 `ff91cfa400bbf547b8cfa6a3ddf773eb54e36ca6aabf9023750fd5308b60a8d4`).
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, unchanged original
receive fixture and all original quantifiers. Mathematical/source-native/
implementation/production gates remain separately OPEN.

## Frozen inputs and current proof boundary

The exact adopted definition is the NPAIR proposal
(`0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`) under the
user's adoption receipt (`d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`).
The frozen proof artifact is
`notes/theory/2026-10-17-adopted-negative-pair-construction.md`
(`6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2`), with
handoff `tasks/agent-loop/inbox/20261017-adopted-negative-pair-construction.md`
(`0d769225832fd1320412e8ae01b57389ff2db31e8a274b9b76d67dc79c4b085d`). A fresh
compiler referee gave CLEAN on that exact artifact: L1 graph-level P2 and the
local derivation-indexed L2/P3 are accepted within their premises. L3 reaches
J1/R1; its J2 step requires an absent whole-presentation map. L4 proves only a
native contribution-node remapping fact. The review does not close transport,
source/native adequacy, implementation, or the original parent.

Treat J2 as conditional until a complete dependent map `rho_u` is constructed.
The exact open proof input is: map every actual ingress derivation and its
provider, source occurrence, tail/future lower, use, receiver scope and lineage
through installation/capture/fresh use, extrusion and qualifying intrusion;
also prove direct and annotated routes publish compatible evidence before any
dependent residual decision. Mixed/multiple-symbolic source coverage and the
actual residual consumer remain separate open inputs. Do not assume
`N-Transport` or `N-Subtract-Elim` from their adopted definitions.

## Inspected native owners and boundaries

Pinned source hashes are listed at the end. The following is source inspection,
not an execution result.

| Owner | Existing producer/consumer | Required extension and present limit |
|---|---|---|
| `candidate_effect::candidate_formal_pair` / `candidate_formal_effect_port` | Recursively builds positive/negative Function terms. It accepts omitted and singleton symbolic ports, but the current negative-concrete guard returns `Unsupported` before pair creation. | For the adopted supported forms, create one shared flexible effect row and retain occurrence descriptor/permission metadata separately from row constraints. Preserve the singleton-symbolic identity. Do not encode permission as `Support`, a lower edge, a closed `Allowance`, or `EmptyNegative`. Mixed/multiple variables remain unavailable until their original `C_sym` contract is proved. |
| `candidate_effect::candidate_formal_annotation` | Emits the paired ordinary formal value links at source slots 43 and 44 and records the negative domain. It runs under the route transaction. | Preserve the occurrence descriptor, both links and permission facts consistently across commit/rollback. A partial pair or permission fact without both edges must not escape. Keep root computation-effect and X/Y/Z ports distinct. A recursive registry is one possible representation; no registry shape or storage owner is selected here. |
| `candidate_effect::candidate_constrain_live_effect` / `State::contributions` | Contributions carry effect family, source origin and allocated instance. Ordinary propagation and the `TypedPairKey`/constraint-origin machinery record some routes. | Establish `At(D,w,delta)` only from the actual lower derivation and actual nested result-child comparison chain. The evidence must distinguish contribution instance, descriptor identity, derivation/use context and independent same-family lineages, and let a reviewer reconstruct delta. Family or canonical-row equality cannot supply this evidence. Predecessor IDs or any other storage encoding are unselected options. Current origins/bound receipts do not yet prove complete NPAIR incidence at every route. |
| `candidate_context` bound evidence | `BoundAdmissionCause` records owner emission, extrusion link, fresh-use antecedent/source bound/use origin/mapped relation or transport. Coverage explicitly records missing relation/origin/antecedent gaps. Attachment bundles are inert. | Reuse these only as inputs. A `BoundAdmission` is not an `At` proof. Any future native realization must validate the actual ports, ingress derivation and complete dependencies, while preserving coverage gaps and undo/duplicate behavior. Whether that evidence lives in this context, another owner, a graph, or an indexed store is unselected. |
| `candidate_source` install/publication | `Work::Install` creates `Action::Install` or `Action::LocalAnnotation`; initializer computation effect is emitted once to the enclosing block. `Stage::PublishLocal` installs the exposed positive root and capture boundary. | Associate the formal descriptor with its actual source occurrence/path before local publication; carry the exposed R1 root and initializer fact as distinct. Publication must wait or remain pending when a required ingress/symbolic dependency is unresolved. Never replay initializer effect as a fresh function-call effect. |
| `candidate_scheme` capture/use | `route_candidate_local_run` captures the installed root and prepares `FreshUse`; rows, Function terms, views, contribution endpoints, context relations, scopes and bound evidence get different remaps. FreshUse allocates distinct contribution instances for distinct processed contribution nodes, preserving family/source origin. It reconstructs captured bounds before publication. | Capture/fresh use must preserve and validate the relation among each descriptor, actual contribution instance, derivation, use identity, receiver scope and pending tail dependency against the original frontier. L4 alone does not show complete identity, NPAIR evidence seeding, or universal remapping. Independent uses need distinct use identities even when canonical rows are shared. Whether this relation is stored in `Graph`/`FreshUse`, a registry, side table or another representation is unselected. |
| `candidate_extrusion` and Function/context propagation | Copies polarity-selected rows, Function nodes, effect views and bounds; selected copies are linked by ordinary constraints. Existing generic transport/evidence can record a relation. | Preserve a reconstructible correspondence between actual source and copied ingress evidence through extrusion, each Function result descent and qualifying SCC/context route. Preserve descriptor, contribution lineage, use identity, tails and unresolved futures. Noninjective canonical row equality cannot recover which same-family contribution had the incidence. Explicit maps or proof objects are possible representations, not decisions made here. No changed SCC criterion is permitted. |
| `shadow_apply::admit_candidate_fact` | Validates original Call operands and creates a separate invocation row for each source `Apply`; records a `NativeInterface` retaining callee, argument, demand, invocation and application effect. This can supply distinct J1/J2 demand endpoints. | Map the stored R1 graph's evidence to each actual `g` use and then to that use's fresh invocation row. Do not equate J1/J2 because their families or endpoint representatives compare equal. A successful shape comparison alone is not the full Call judgment. |
| `candidate_receiver` / `candidate_catch_operation` | The bounded `ReceivingResidualExperiment` has a real but experiment-scoped suppress/forward consumer tied to a selected Catch operation and provider. `candidate_catch_operation` builds operation payload/continuation interfaces; it is not by itself an NPAIR subtractor. | The receive fixture has no Catch and provides no subtraction event. Identify and derive the actual original source/native consumer before invoking N-Subtract-Elim. The experiment's specialized outcome code is not blanket authority to delete a contribution or a proof of NPAIR lineage correspondence. |

`candidate_signature_effect` represents declared Support/Allowance views and
ordinary tails; it is not a substitute for the new shared negative port. In
particular, the current negative branch rejects nonempty concrete rows. Removing
that guard alone is not an implementation: it would still lack permission vs.
inflow separation, actual ingress, transport, scheduling and consumer evidence.

**Representation boundary.** Binding here are the adopted, externally checkable
evidence invariants: original typed occurrence and scope, one shared row, both
ordinary edges, actual contribution derivation, independent lineage, complete
dependencies, and valid correspondence through use/copy/consumer. Notation such
as `rho_u` names a mathematical source-to-destination correspondence; it does
not require a runtime map object. Registries, explicit graph fields, typed nodes,
IDs, side tables, memory ownership, update order and invalidation encoding are
unselected implementation options. Choosing among them requires its own
architecture review and authority gate before a code contract makes one binding.

## Required implementation sequence for a later exact code sprint

This contract establishes readiness requirements only. A later code sprint must
freeze a new exact compiler lease after any newly required proof/review inputs
are accepted.

1. **Formal producer.** Under source-owned annotation scope, allocate/reuse the
   one row `x_alpha`, construct both polarity terms over it, and retain
   `D_alpha=(owner, formal, annotation occurrence, structural path, lexical
   scope, concrete operands, symbolic operands)`. Record concrete permission
   declarations as metadata only. Emit both existing ordinary formal links.
   Preserve the supported source cases and return the existing unsupported
   result for genuinely unproved symbolic forms; do not rewrite source
   signatures or expected outputs.
2. **Authentic derivation producer.** Establish `At(D,w,delta)` from actual
   propagation work when a particular contribution derivation composes through
   the two result Function edges to the negative port. The evidence must retain
   exact derivation provenance and ordinary occurrence/cause identity. If direct
   propagation reaches the same demand before the annotated route, retain the
   same contribution identity and pending association instead of publishing a
   family-wide match, empty row or prematurely finalized residual. A failed
   attempt must not publish a partial pair or evidence, and any retained
   continuation must stay consistent. The detailed rollback, allocation,
   duplicate and invalidation mechanisms are left to the later design review.
   Incidence nodes, registries, predecessor IDs and maps are examples only;
   none is mandatory under this contract.
3. **Capture and fresh use.** Capture only evidence justified by actual graph
   nodes/bounds in the source frontier. Freshening must establish and validate
   the source-to-destination correspondence for rows, contribution instances,
   descriptor occurrences, derivations, bound relations, use identities and
   scopes. Keep equal family atoms
   from independent providers or routes distinct. Map all tail/future
   dependencies and ordinary four-child Function constraints. Do not copy the
   old receiver scope into a new use without source-owned remap evidence.
4. **Extrusion/intrusion.** Preserve the typed incidence relation through the actual
   selected bound and Function worklist edges. Preserve old/new endpoints,
   derivation provenance and annotation occurrence through extrusion copying
   and qualifying SCC intrusion. Drop evidence only with an explicit
   invalidation reason that returns the dependent proof to pending; never treat
   endpoint canonicalization as proof transport. The internal encoding is
   unselected.
5. **Actual second consumer.** At original `g ()`, use its own fresh
   `NativeInterface` and J2. First identify the actual downstream elimination
   consumer and provide its demand, actual input, permission, ingress and
   transported proof, receiver scope and selected-consumer evidence. Then apply
   subtraction only to the licensed contribution instance. Preserve every
   additional effect, tail, symbolic dependency, provider and independent
   lineage; false/mismatch has no subtraction, and suspended work retains its
   pending inputs. If no such native consumer exists in the authorized source
   path, implement that consumer in a separately approved exact lease.
6. **Publication and validation.** Do not expose a solved residual while any
   required At association or future lower remains pending. Any later
   verification must demonstrate the actual producer-to-transport-to-consumer
   path for both calls, all Function children, direct/annotated arrival orders,
   captures/fresh uses, copied bounds, extrusion/intrusion, tails, distinct
   same-family providers, false/mismatch and suspension. Tests can falsify a
   proposed implementation but cannot replace the proof. Keep all unrelated
   parent gates open.

## Next exact evidence and non-goals

Immediate next step is to resolve the missing dependent map or name its first
precise source owner. Do not start code by deleting the present negative-row
guard. Required evidence owners are `candidate_formal_pair` plus the two formal
links; ordinary effect propagation and typed-pair origin tracking; source
installation/publication; graph capture/fresh-use and replay; extrusion/SCC
transport; and the actual effect-elimination consumer. The proof worker's five
stable TODOs are copied unchanged in its frozen handoff.

This plan does not change source semantics beyond the adopted definitions,
compiler code, tests, fixtures, expected output, gates or resource policy. It
does not claim that the current compiler accepts the fixture or that the
bounded receiver experiment is the general residual consumer. The adopted
contract requires preservation of complete typed positions, authentic ingress
derivations, contribution identity, dependencies and coherent capture/fresh-use
transport. It does not select their representation. Recursive port registries,
typed-incidence nodes, predecessor-edge identifiers, explicit Graph/FreshUse
maps, storage ownership and processing order are implementation options only.
Their representation, allocation, processing and scheduling remain unselected
pending a later architecture decision. No option is mandatory or authorized by
this plan.

## Frozen native dependency hashes

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_receiver.rs` | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |

The sprint/source baseline remains `74bfaa6a8ce0a60051e40e531c54576516d6c151`.
This contract is reviewable planning evidence, not independent approval,
implementation, source/native adequacy or production readiness.
