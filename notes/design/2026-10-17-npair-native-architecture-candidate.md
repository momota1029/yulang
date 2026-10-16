# NPAIR native evidence architecture candidate

Status: Draft; candidate architecture only. Independent architect/spec review pending.
Scope: a possible native realization path for the adopted negative formal pair and its evidence lifecycle. No compiler implementation authority.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still OPEN.
Sprint: `npair-commit-retention-repair-20261017`, revision 1.

## 1. Decision proposed for review

Choose an **inference-session incidence ledger with graph-owned capture references** as the next architecture candidate:

- `candidate_effect::State` owns typed negative-port descriptors and actual ingress derivation records for the inference session. Each record is indexed by an allocated local identity, never by family or canonical row alone.
- The source annotation transaction creates one descriptor for the original annotation occurrence and one shared ordinary effect row. It publishes the descriptor only with both formal links. Permission remains metadata on the descriptor; it never creates an effect lower, input cap, or empty-row conclusion.
- Function propagation extends an ingress derivation over the exact child comparisons that lead to the descriptor's negative effect position. Each edge records its parent comparison and `FunctionField`. Same-family contributions remain distinct. Duplicate routes for the same source contribution may share its identity while retaining route evidence.
- `candidate_scheme::Graph` captures descriptor references, local ingress records, and anchor references alongside its existing typed rows, Function nodes, bounds, context payloads, and scopes. While `FreshUse` is live, its maps provide construction-time images. Before the successful local-use commit discards those maps, the candidate prepares and atomically attaches a committed Use certificate containing the finite registered-query projection in §2.3. That certificate must preserve original descriptor/contribution identities, create a distinct use identity, and mark unauthenticated derivations Pending. Current native code does not do this: `LocalFreshRoute` keeps only slot/local/occurrence/Graph/rows.
- A native bound snapshot or an `AttachmentBundle` is not itself an ingress proof. If capture/replay cannot authenticate a required antecedent, the association stays pending and blocks any residual publication that depends on it.
- A future residual consumer must receive a `NativeInterface` for its actual call plus the selected consumer's own demand, scope, matching/selection evidence, and exact ingress lineage. The consumer removes only the licensed contribution. No such consumer is currently established for the receive fixture, so this candidate deliberately does not assign subtraction to `ReceivingResidualExperiment` or to a signature view.

This selects one internal design to review, not a runtime map requirement adopted by NPAIR. The source definition's required evidence remains authoritative; the ledger is merely this candidate's representation.

## 2. Owner-local lifecycle

### Formation and ordinary constraints

`candidate_source::preflight_formal` currently rejects the receive annotation's negative concrete row before constructing the formal. A future approved change would extend `candidate_formal_pair` / `candidate_formal_effect_port` and the separate `candidate_signature_effect` owner. The descriptor would retain definition/formal identity, `SourceNodeKey` occurrence, structural path, lexical scope and resolved operands. One flexible row supplies both positive and negative projections. `candidate_formal_annotation` would stage the descriptor, both ordinary formal constraints and rollback metadata in the existing route transaction; it commits the complete unit only after both links are admitted.

The formal root computation effect and X/Y/Z ports remain separate. Existing `Support`, `Allowance`, concrete operation declarations, and `Contribution` are not reused as the negative port. Existing mixed/multiple-symbolic cases stay unsupported by this candidate until their original `C_sym` is derived; source acceptance must not be narrowed to the parser's present envelope.

### Ingress derivations and arrival order

The inference-session ledger has distinct records for:

```text
NegativePort(id, descriptor, shared_row, permission_operands, source_scope)
Ingress(id, port_id, contribution_id, actual_derivation, typed_position)
Transport(id, prior_ingress_id, comparison_edge, FunctionField, destination)
Use(id, local_occurrence, caller_scope, graph_remap)
```

Names are illustrative for this design candidate. Every identity is session-owned and cannot be recycled while any ledger, graph, undo log or pending consumer refers to it. A contribution's effect family and source origin remain payload, not identity. A direct path and an annotated path can only share an ingress identity after proving they carry the same original contribution; comparing row representatives does not establish that fact.

The Function-comparison owner records child-edge evidence for all four fields. Only the actual result-effect descent chain can establish incidence at the adopted nested negative port. It does not skip the argument, argument-effect or result-value comparisons. When a direct route reaches a dependent consumer first, the consumer remains pending until the required matching incidence is present or a proven negative result resolves that requirement. Missing evidence cannot become permanent ineligibility.

### Capture, fresh use and scope

`candidate_scheme::Graph` stores the descriptor/ingress references adjacent to its existing captured graph. Capture follows the existing local-closure rule: copied local rows and Function children are explicit graph nodes; nonlocal rows remain live anchors. The sidecar retains the source descriptor and lineage references for anchors rather than copying their current lower lists and calling that closure complete.

For a fresh use, `FreshUse` construction maps can produce descriptor, row, contribution, evidence, bound, context, term, bundle and scope images. Non-generic/shared ports keep the ordinary source representative; generic local rows get their allocated fresh row. Captured owned scopes map through the caller boundary, with the actual receive route preserving the `r_g` child under `r_B`. Each use receives a distinct use identity even when it shares an anchored port or provider. The anchored J2 result in the reviewed proof is the present justified case; general dependent provider replay and quotient/extrusion correspondence remain obligations. These construction maps are not the committed record: current `GraphState::commit_local_use` discards all except the row crosswalk.

### Committed Use certificate and registered query boundary

The required logical record is the finite query projection `P_u` from R1 in
`notes/theory/2026-10-17-npair-use-certificate-retention.md` (artifact SHA-256
`c5c069798cd5822918e09438ac7e82e627d562ba0b13f8233ca5709e43f9c922`; handoff
`tasks/agent-loop/inbox/20261017-npair-use-certificate-retention.md`, SHA-256
`4ef908c919d1e94b1c65960d31df730b0620980382f725a5c6bab75585099514`). R1 is a
conditional author result, not independently reviewed yet, and does not show
that current native code implements this contract.

For each registered packet, the retained information must answer these queries
after FreshUse destruction: (a) original descriptor/permission operands and
shared-port image at the exact source occurrence/path; (b) selected original
contribution/provider lineage and its target endpoint, distinguishing anchors
from copied nodes; (c) authenticated ingress/transport derivation, its typed
Function-field steps, comparison/bound identities and predecessor references;
(d) actual-use and original lexical/context coordinates, including owned versus
external scope/input and demand use identity; and (e) validity, coverage gaps,
Pending reasons, required dependency owners and expected wake-up events. This is
a logical query contract, not a mandated runtime object layout or byte-minimal
representation. A field may be represented indirectly only through a stable,
complete lookup; family, row representative, source origin or copied bundle
alone cannot recover provider/use/lineage identity. No query may infer At,
selection, closed-world absence of a future lower, or permission to subtract.

Build the projection from actual construction-time maps before their destruction.
The candidate owner may choose copied values, immutable shared records or another
reviewable representation, but must prepare all allocations, dependency closure,
capacity reservations and validity metadata before final commit. The final
successful `commit_local_use` must make the complete certificate visible with
the route as one unit; no consumer can observe a partial certificate. Keep the
existing source-side `Graph` and `rows` crosswalk where useful, but do not treat
them as a substitute for the per-use descriptor/contribution/derivation/scope
projection. A failed private attempt publishes no certified fragment; abandoning
that attempt is sufficient, while exact restoration of private capacity is not
a semantic requirement. This promotion boundary and representation remain a
Draft candidate pending review and user approval before code.

The session owner pins every transitively referenced record while any committed
Use, graph, pending query, consumer or undo/version record refers to it. Identity
includes session generation and use occurrence and cannot be silently recycled.
On invalidation, mark dependent certificates and pending packets Pending before
affected consumers run. Preserve the original requirement and owner; never turn
a missing dependency into an empty dependency list or solved residual.

The producer of a pending packet is the owner that registers a consumer query
against a use/port/lineage. Until the actual NPAIR residual consumer is found,
this interface remains abstract and no subtraction occurs. Candidate wake-up
events are: new authenticated ingress/Function-edge evidence, successful
replay/restoration, new actual call/demand association, changed scope or anchor
version, and dependency invalidation. Each event reevaluates only subscribed
packets; completion requires every required source-typed predecessor and
consumer selection premise to be authenticated at the current version. A proven
negative result may resolve only the specific tested obligation. Absence of an
event is not completion. A separate progress argument must show that every
eligible event reaches its subscribers and repeated updates do not starve a
ready packet; R1 does not prove this scheduling property or global termination.

`BoundAdmissionCause::FreshUse` and imported snapshots remain evidence inputs only. Current `EvidenceCoverage` can explicitly report missing processing antecedents, seed authentication, bound relations/origins and `ReplayUseAntecedentsNotRetained`. The ledger must preserve those gaps. A future implementation needs to supply source-typed antecedent and provider actions before it can mark the corresponding incidence transported.

### Extrusion, intrusion, and invalidation

An extrusion or qualifying Value-SCC intrusion adds a typed transport record for each selected parent/copy comparison. It may transport a port/ingress only when the actual selected edge carries that proof and every dependent operand has a source correspondence. It cannot synthesize equality of descriptor owners, providers, uses or residual lineages from representative equality. If a dependency is invalidated or cannot be replayed, the transported incidence becomes pending and any dependent residual stays unpublished. The existing Value-SCC selection rule is unchanged.

### Consumer and publication boundary

`shadow_apply::admit_candidate_fact` authenticates each source Apply recipe and allocates its own invocation row and `NativeInterface`; it does not perform negative-pair subtraction. `candidate_receiver::ReceivingResidualExperiment` is tied to a selected Catch operation and provider; the receive fixture has no Catch. Neither is the established consumer for NPAIR.

The candidate consumer boundary is therefore an explicit missing owner. Before any implementation can subtract, source inspection must identify an actual receive-path consumer and its observable selection event. If none exists in the authorized source path, the architecture must return to design with a separately reviewed source/API decision. The fallback behavior remains no subtraction from permission alone; a pending association cannot publish a solved residual.

## 3. Transaction, failure, and resource behavior

Pair creation and its two formal edges form one route transaction. A failure before commit exposes neither a partial pair nor a ledger record. Session-local identities are monotonic across rollback so a stale receipt cannot name a retry. A fresh-use attempt that cannot authenticate its evidence publishes neither a partial association nor a residual; the existing retained continuation remains at its prior coherent frontier. Duplicate evidence is idempotent only when descriptor, original contribution, derivation, use and dependent scope all match. The complete P projection is assembled and capacity-accounted while the local-use frame still exists, before the final commit boundary; commit transfers the prepared record without fallible partial publication. Invalidation changes validity state before a dependent consumer may publish.

Use a shared immutable derivation/dependency DAG or an equivalent representation
that stores each distinct complete record once; do not materialize every path
through a shared graph. Deduplicate only when the full descriptor, provider,
contribution, derivation, use, scope and dependency tuple agrees. Family or row
equality is insufficient. If `V` is the number of live unique records, `E` the
dependency edges, `I` lookup entries, `W` pending subscriptions, and `U` undo/
version references, retained charge is `O(V + E + I + W + U)` plus operand
payload and required map fragments. This is an accounting model, not a bound on
the number of solver derivations, a termination theorem or a performance claim.
Charge capacity in the existing session owner, including indexes, references,
subscriptions and rollback/version data; release only when no live owner refers
to a record. Any later implementation still needs measured limits and a bounded
falsifier. This sprint grants no code lease.

## 4. Why this candidate

A flat `SourceEffectId` permission set loses the distinction between two providers that contribute the same family. A canonical `EffectRow` key loses actual contribution and use identities. Reusing `BoundAdmission` as an At proof ignores its explicit coverage gaps. Copying `AttachmentBundle` vectors preserves provenance only. Placing subtraction in `shadow_apply::admit_candidate_fact` would confuse call-demand generation with a consumer event. Borrowing Catch experiment behavior would invent source authority absent from receive.

The session ledger keeps derivation identity where propagation emits it; the graph stores evidence references needed to capture and remap a local value; a committed Use record preserves the finite query projection across the existing commit boundary. These are candidate responsibilities, not claims that existing owner APIs already produce all listed facts. R1 proves only conditional lookup retention for registered queries; it does not authenticate missing source evidence or prove progress. The separately CLEAN-reviewed anchor lemma supports only the direct shared-anchor J2 path.

## 5. Review requirements and unresolved decisions

Independent architect review must assess the pre-commit projection and atomic transfer boundary against the actual `commit_local_use` lifecycle; committed ownership/lifetime and invalidation; pending producer/event/completion/progress contract; full identity-preserving query projection; shared-DAG growth/accounting; actual consumer absence; operational failure cases; and fit with graph/resource lifecycles. It must distinguish the conditional R1 from current native compliance.

Independent spec-auditor review must check conformance to adopted NPAIR §§2–4 and the corrected readiness contract: permission is not inflow/cap/emptiness; both ordinary edges remain; At is derivation-indexed; same-family providers stay distinct; direct/annotated ordering and futures remain pending until justified; J1/J2 and initializer effects remain separate; no Catch authority or source restriction is imported. Confirm P is only a proposed evidence-retention contract, Pending cannot publish a residual, and no storage design, source premise or parent theorem is represented as adopted/closed.

Before any code implementation, present the reviewed candidate and unresolved alternatives to the user for approval under `rules/design-authority.md`. Required open inputs include the actual receive consumer, authentic native NPAIR emission, complete replay antecedents, direct/annotated scheduling completeness, general representative/extrusion correspondence, mixed/multiple-symbolic `C_sym`, and qualifying intrusion transport. F1/FK1, full Call/effect, source-Generalize, soundness, principality, F5 and production remain separately OPEN.

## 6. Frozen inputs and inspected owner pins

- Adopted definition: `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md`, SHA-256 `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006`.
- Adoption receipt: `notes/design/2026-10-17-source-formation-proposals-adoption.md`, SHA-256 `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa`.
- Reviewed L1–L4: `notes/theory/2026-10-17-adopted-negative-pair-construction.md`, SHA-256 `6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2`.
- CLEAN-reviewed bounded anchor/J2 result: `notes/theory/2026-10-17-npair-whole-presentation-transport.md`, SHA-256 `cc9aee77661de00ac011a9da411b385e9e440277bb194bc13a83d71f973b0719`.
- Corrected readiness contract: `notes/design/2026-10-17-negative-pair-native-implementation-contract.md`, SHA-256 `36d9792d7a5bb4d06beeb4a1c62df28d38ff171fc324783061c2219a970ce064`.
- Sprint contract: `tasks/agent-loop/sprints/npair-whole-presentation-transport-architecture-20261017.md`, SHA-256 `bb5ba6e065afcd611472c83ff4af0240707adeaa7b8a5b821f975040b23c94a3`.
- Conditional finite-query retention lemma: `notes/theory/2026-10-17-npair-use-certificate-retention.md`, SHA-256 `c5c069798cd5822918e09438ac7e82e627d562ba0b13f8233ca5709e43f9c922`; its handoff is `tasks/agent-loop/inbox/20261017-npair-use-certificate-retention.md`, SHA-256 `4ef908c919d1e94b1c65960d31df730b0620980382f725a5c6bab75585099514`. It is a conditional author result; independent proof review has not run.

Directly inspected owner bytes:

| Owner | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_receiver.rs` | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |

This artifact is a reviewed-design candidate when its fresh review is complete. It is not an authoritative architecture decision, not source/native adequacy, and not permission to implement it. Any later compiler contract must separately establish authentic pair/ingress production, replay antecedents, progress and the actual receive consumer; planned storage alone does not authorize disabling negative preflight.
