# Contravariant concrete subtraction: source-to-proof bridge audit

Date: 2026-10-10
Status: reviewed research source audit; proposed bridge obligation only
Review: compiler-referee PASS, 2026-10-10
Source baseline: `32c65f07671b9de7b05ece3044a714c4d8d0e61b`
Oracle source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`; never executed
Method: targeted producer/consumer correspondence, complementary to the prover
and falsifier lanes; no constructive subtraction theorem or new witness here
Lease: this new note only; no production, test, shared-record or Git mutation

## Objective and authority

Determine which premises of retained hygiene results the committed source
actually supplies, and locate the missing construction/consumer transition.
Governing policy is [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and the [concrete annotation implementation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md).
Transport dependencies are [typed boundary realization](../design/2026-10-02-typed-boundary-realization-draft.md)
§6 and [typed source owner realization](../design/2026-10-02-typed-source-owner-realization.md)
§§1–5. Repository research, authority and concurrency rules apply.

The selected meaning is fixed: concrete `[E]` at a composed negative position
permits exact-position function-local subtraction; positive `[E]` allows E.
Nested Function arguments reverse polarity and results retain it. Variables
are omitted only from concrete atom collection; their flows and future concrete
checks survive. Nominal identity is resolved. Independent attached siblings at
the same nominal point survive. No support-wide cancellation, literal legacy
ID migration, pending Call metadata grant, or result from the withdrawn callback
example is used.

The policy integration §4 table described an earlier implementation boundary.
Its HIR and concrete-alphabet gaps have since been partly repaired. The
[implementation delivery](2026-10-10-concrete-effect-annotation-implementation.md),
[initial review](2026-10-10-concrete-effect-initial-review.md), and committed
`tasks/current.md` tail distinguish completed covariant construction from open
negative admission, contextual transport and recursive invalidation. Historical
test counts in those records are reported evidence, not checks rerun here.

## Retained results and exact premises

“Supplied” below means supplied by pinned compiler source, not assumed by a
research model. A reviewed conditional result retains its scope despite the
enclosing document's Draft label.

| Result / claim class | Exact hypotheses and quantification | What pinned source supplies / does not supply |
| --- | --- | --- |
| Typed boundary §6 composition, identity and source-union distribution; established algebra under supplied correspondences | Fix finite monomorphic ownership/signature descriptors and one assignment ν. For every typed path correspondence M,N and path-indexed χ,D, `N*(M*χ)=(N∘M)*χ`, `Id*χ=χ`, with tagged source union and original predicate identity retained. | Source annotations distinguish owner/row occurrence and scoped variables; live solver bounds retain relation fibers. There is no established decoding from these bounds to the theorem's χ,D or typed M. Canonical row equality alone supplies none. |
| Typed boundary §6 no-authority creation, depth preservation and live filtering; reviewed conditional transport theorem | Output is exactly the indexed relational image of input profiles; transport preserves original boundary/receiver references. For each fixed candidate h and configuration C, `M*(live_C^h χ)=live_C^h(M*χ)`. Grant additionally requires original receiver equality and explicit Γ admission at the matched position. | `SourceAnnotation.owner`, exact `SourceEffectRow.position`, and source-set polarity/scope are retained. Definition/local lexical ownership is not dynamic receiver activation, receipt or event-specific observation; Γ/Flow/Observe/Receive derivations are not constructed by these annotation owners. |
| Typed boundary §6 uniform transport / complete observation; reviewed conditional theorem | For any tagged input packets `(v,t,χ,K,D,L)` under the same ν, two routes with the same composite typed map, target receipt, and preserved event Observe witnesses agree at the same h,C. A later latent observation requires its own matching view/receipt/path and active original identities. | Current view copies preserve nominal members, origin, source position and mapped tail. This is useful representation evidence, but it is not a proof that arbitrary function/latent/store routes construct the theorem's packet. No dynamic activity claim follows. |
| Source owner §§1–4 preservation and expiry; reviewed decorated-kernel theorem | Fix finite monomorphic decorated Ω, supplied profiles/maps and one ν. Start with a related initial state. Every finite ordinary execution and finite sequence of lawful calls/forces/raw resumptions preserves clauses 1–5. Fresh control owners never rename historical boundary receivers, receipts, request origins or K,D. Infinite behavior is covered at finite prefixes. | HIR static owner/source identities are available. Annotation solver construction does not implement the required saved control/owner-view graph or related initial-state decoding. Static `DefinitionRootId` is not an established dynamic invocation witness. |
| Source interface adequacy §4 exact-image simulation and bind lemma; established within candidate semantic carrier | For every well-typed candidate C at fixed ν,σ,π, exact embedding E(C), whose transitions are source-rule relational images, simulates each source step and every admissible typed resumption. Bind additionally assumes simulation of F/F# at every reachable related return pair after any finite matched resumption sequence. | A finite constraint graph is not that potentially infinite exact image. No negative annotation transition or complete output-image decoding is supplied here. Simulation cannot be inferred from a checker that assumes the same transitions. |
| Concrete capture profile corollary; conditional derivation | For concrete τ at actual Handler boundary b/port p, assume source elaboration connects the occurrence and establishes Γ_b(p) admitting exactly τ-compatible operations under ν. For each q,h,C, eligibility requires compatibility, actual Inc_C witness, and current receiver/handler activity; selection additionally requires ordered search and OpCompat. | Nullary identity/position are supplied; the complete Handler profile, typed incidence and current search configuration are not. This corollary proves eligibility once supplied, not subtraction or a public inferred scheme. |
| Protection-only filtering; separate conditional result, not used to discharge `[E]` | For each full Flow/Observe/Receive derivation w, supplied `Release_s(q,w,C)` changes only protection; grant, Inc_C, identity and K,D stay fixed. Selection occurs before existential route projection unless release factors through that projection. | No Release_s rule is inferred from concrete annotation atoms or attachment IDs. `[E]` is not reinterpreted as `'e?`; the separate result remains available if an authentic release operation later requires it. |
| Attached-subtraction separation; bounded characterization, not a source theorem | Fixed supplied attachment/consumption/output flags for two events in one ν,K,D fiber. Removing an attached contribution removes nominal support only if no same-point contribution remains in the complete output image. Historical enumeration: 256 pairs, 96 differential shallow histories with shared assumptions. | Source retains distinct contribution and annotation-member representations, but does not yet supply a live negative attached-subtraction transition or its complete output projection. Counts and model consistency do not prove those source rules. |

No pure injective parent-renaming theorem is used to justify parent/copy SCC
equality. No theorem above establishes the missing negative constructor merely
because its hypotheses mention annotations.

## Frozen Yulang2 producer and consumer chain

All locators in this section refer to the frozen Oracle commit, obtained with
`git show`, without execution.

| Owner | Exact source loci and retained fact |
| --- | --- |
| Signature polarity | `crates/infer/src/lowering/mod.rs::SignatureLowerer::lower_pos` 571–615 and `lower_neg` 619–663: parameter/argument-effect polarity reverses, return/result-effect polarity is retained recursively. |
| Positive row and symbolic connectivity | `lowering/signature_effect.rs::lower_effect_row_pos` 78–107 builds `Pos::Row` and retains a tail variable. `connect_effect_tail_exact` 336–358 emits both directional links. `lower_arg_effect_neg` 19–38 instead introduces a connected fresh effect for ordinary argument rows. |
| Negative return boundary | `lower_ret_effect_neg` 56–65 calls `lower_ret_subtractable_effect_row_neg` 162–178. `function_boundary_effect_stack_inner` 319–334 selects the connected boundary variable; `effect_row_stack` 382–421 creates fresh SubtractId plus concrete subtractability, and `register_stack_facts` 434–439 retains declared facts. The negative wrapper is a filter around that inner variable. |
| Paired annotation construction and matching returned-value evidence | `annotation/constraints.rs::AnnConstraintLowerer::lower_value_bounds`, Function case 363–390, reverses parameter endpoints and wraps returned value with `NonSubtract`. `lower_ret_effect_bounds` 424–470 pairs the pushed positive view with a filtered negative view and matching output subtracts; `effect_row_stack` 657–690 constructs the attachment set; `predicate_weights` 921–924 constructs matching pop/filter weights; `wrap_non_subtracts` 848–851 retains them on returned values. |
| Concrete collection versus variables | Signature `effect_atom_con` 453–460 and annotation `effect_atom_con` 741–748 return no concrete atom for variables. `annotation_var` 835–845 and row/tail connections retain the solver variables. This separation is why skipping variables is not deleting flow. |
| Authentic local lambda boundary | `lowering/expr/lambda.rs::connect_lambda_pattern_annotation` 1244–1307 constructs the actual pattern annotation, connects the parameter computation, and extracts its call/output predicates. `mark_lambda_param_call_predicate` 919–936 and `mark_lambda_param_call_predicate_frame` 938–943 retain local/frame ownership. `connect_defined_lambda_skeleton_predicates` 1176–1241 wraps actual output effect and value at 1232–1237. `lambda_parameter_output_predicate_constraints` 1571–1578 distinguishes Function annotation call predicates from immediate output predicates. |
| Existing and later concrete filter consumers | `constraints/machine/bounds.rs::check_and_erase_upper_left_filter` 3193–3210 checks before erasure. `constrain_type_var_lowers_by_filter` 3213–3255 records filters and checks stored lowers. `constrain_lower_bound_by_registered_filters` 3285–3301 checks future bound insertion. `constrain_weighted_pos_lower_by_filter` 3303–3316 combines stack and concrete checks; `constrain_pos_lower_by_filter` 3318–3360 recursively handles rows/stacks/unions and registers a filter when reaching a variable. |

This independently inspected implementation supports a correspondence question,
not numerical identity of weights/IDs or a general correctness theorem for
Oracle. Closed-row variable sharing in Oracle is not successor permission to
merge source occurrences. Returned-value predicate handling is a real consumer
dependency; migrating only a nominal atom set omits it.

## Pinned Yulang3 formation and consumer owners

Loci below refer to `32c65f076`, not concurrent working-tree edits. HEAD moved
to `75a530a235efd25d66178b21b8a54ee151f161dc` during the audit; this does not
change its pinned-source claims. The changed context dependency is listed below.

| Phase | Supplied evidence | Missing transition / reconstruction owner |
| --- | --- | --- |
| HIR syntax-to-resolved annotation | `yu-hir/src/module/source_annotation.rs`: `SourceEffectId` 31–35 is module plus declaration source key; `SourceAnnotation`/type/row 68–93 retain owner, annotation position, exact row position, concrete identities and symbolic variables. `declarations` 125–305 populates nullary family/operation identity. `form`/`parse_annotation` 307–358, `parse_type` 381 onward and `parse_row` 487–544 preserve the occurrence tree. `local_source.rs::LocalSourceParameter` 147–153 and constructors 283–304, 746–771 retain actual formal annotations. | No general parameterized operands, dynamic Handler profile or contribution attachment to a negative row is inferred. The earlier complete loss at HIR is repaired for this admitted nullary syntax. HIR owns preserving source occurrence and resolved arguments for any subsequent syntax extension. |
| Source admission and scheduling | `candidate_source.rs::preflight` 56–81; `preflight_formal` 86–91 starts a formal negative and composes Function variance; `preflight_annotation` 92–101 starts binding annotations positive. `Action::FormalAnnotation` / `Annotation` / `LocalAnnotation` and `execute_candidate_actions` 503–527 route source construction. | Concrete negative rows are explicitly rejected before execution. Omitted formal ports and singleton variable ports differ from explicit empty rows; do not infer uniform admission from the negative-empty whole-binding slice. |
| Paired checked/exposed target | `candidate_effect.rs::candidate_formal_pair` 895–913 and `candidate_signature_value` 1188–1279 compose variance independently of endpoint polarity. `candidate_formal_effect_port` 915–932 admits concrete only at positive variance. `candidate_formal_annotation` 934 onward constructs a shared paired domain. `candidate_annotation` 1033 onward and `candidate_local_annotation` 978 onward check original value and publish exposed target while retaining evaluation effects. | `candidate_signature_effect` 1280 onward explicitly returns unavailable for nonempty concrete at negative variance (1340–1342). This is the authentic owning seam for negative concrete construction, not a missing Call registry query. |
| Source attachment sets | `candidate_effect.rs::candidate_signature_view` 597–648 stores exact owner/position, resolved members, tail, source weight; `candidate_context.rs::source_weight` 814–835 stores composed polarity, lexical scope and member ordinals. Its unit-PUSH marker is dormant; `materialize_unit_push` 837–855 has only a detached adapter. `candidate_negative_empty_bundle` 1114 onward retains written negative empty rows anchored to source annotation check/exposure. | Written positive sets and inert negative-empty provenance are real supplied inputs. They are not event attachment, negative concrete permission execution, or a complete flow-path witness. Negative concrete set construction plus its actual checked/exposed residual owner remains open. |
| Contributions and covariant checks | `candidate_effect.rs::Contribution` 72–76 separates resolved effect, source origin and instance. `candidate_effect_contribution` 725–748 allocates that operand. `candidate_check_effect_operand` 749–817 expands Support into annotation members/tail and checks matching concrete against Allowance, forwarding unmatched members to a tail. Operation `candidate_operation` 650–669 constructs declaration interface support. | Annotation members and operation-interface members are not emitted contribution instances. The factory's production caller in scheme freshening copies an existing contribution; source annotation/operation interface construction does not produce authentic executed events or negative subtraction. No set membership test may replace an attachment-specific output consumer. |
| Live contextual relation | `candidate_context.rs::RelationKey` 91–94 includes typed pair and context. `candidate_context_seed` 1073–1101 links source empty bundles; `candidate_context_replay_impl` 1231–1295 preserves ordered lower/upper fibers. `candidate_context_execute` 1128–1187 executes only the direct closed zero-word Allowance filter, installing/replaying its bound before discharge. | Other context constructors and detached numeric evaluation do not establish source nonempty dispatch. The missing consumer must activate the real attachment/residual transitions and current/future lower checks, rather than simply discharge the source payload. |
| Completion/equality | `lib.rs::pair_is_current` 11318–11326 uses actual processing RelationId plus SCC generation despite its pair-shaped helper name. `record_typed_pair_admission` 12168 calls `candidate_intrusion.rs::mark_candidate_pair` 223–254; raw diagnostic admission is separated from canonical completion. Intrusion generation/canonical-bound update is at 529–592. | Relation-sensitive completion is already retained; do not report an endpoint-only completion gap. Exact nonempty two-cycle licensing/invalidation and rollback/retry is an additional open contract, not supplied by ordinary SCC completion alone. |
| Copy/extrusion/capture | `candidate_effect.rs::candidate_copy_effect_view` 670–691 retains source scope/polarity and remaps tail; `candidate_remapped_effect_view` 693–709 keys copies by original view plus mapped tail. `candidate_extrusion.rs` 280–301 remaps Support/Allowance/member views. `candidate_scheme.rs::capture_candidate_graph` 558 onward retains bound relation and bundle incidence; `freshen_candidate_graph` 764 onward copies views/contributions (831–855) and restores relation/bundle transport (935–947). | Current view/bundle transport is supplied. Freshening reuses `post_check_context(parent)` in `candidate_context_transport` 1326–1347 rather than establishing remapping of arbitrary nonempty operation DAGs/payload IDs. There is no proof here of complete nonempty attachment/gamma lineage under capture, extrusion or intrusion. |

The owning debt is consequently at annotation target/attachment construction
and its contextual effect consumer, with lifecycle correspondence at the
ordinary scheme/extrusion/intrusion owners. They should retain the facts they
already know. Reconstructing a position from equal rows or a grant from effect
support would discard evidence the HIR/source constructor already supplies.
Dynamic receiver/activity facts belong to actual operational introduction;
static source-set identities must not impersonate them.

## Minimal sufficient bridge obligation

The following is a proposed source-to-proof lemma for the primary/prover. It
states an implementation correspondence requirement; it adds no language
clause, carrier, support restriction, or proof prerequisite for full Call.

Fix the accepted nullary source annotation envelope, its real source action
schedule, one shared assignment ν, and the exact local subtraction transition
from the selected proof. For every actually formed annotation row occurrence p
at composed negative polarity, and every source-generated finite sequence of
typed bounds/uses reaching p, require a decoding J of the retained source
annotation, attachment, scoped symbolic tail, concrete contributions, relation
fibers and residual consumers satisfying:

1. **Formation agreement.** The authentic paired annotation action supplies one
   original attachment for p with exactly its resolved concrete members,
   lexical/function ownership and composed polarity. The check and exposed
   endpoints denote that same local contract; independent source rows/uses
   retain independent attachment identities even if nominal support or rows
   coincide. No annotation support member is decoded as an executed event.
2. **One-step consumer agreement.** For every actual arriving lower (stored or
   later), J of the real consumer step equals the selected local subtraction
   step, including the exact contribution/attachment and current residual
   dependencies. An unrelated attachment or sibling contribution is retained.
   A symbolic lower preserves its connection and installs the corresponding
   future-concrete obligation; allowed concrete membership creates no effect.
3. **Lifecycle agreement.** Copy/capture/extrusion/intrusion transport the same
   decoded attachment and residual dependencies through the actual directional
   maps, freshening independent uses consistently. Equality identifies solver
   coordinates without erasing source ownership or relation alternatives.
   Completion, filter discharge, withdrawal and rollback preserve this
   decoding, including the actual admitted recursive certificate cases.

Given an authentic formation satisfying (1), step agreement (2), and lifecycle
agreement (3), induction on the finite source-generated transition sequence
supplies the local source-to-proof commuting diagram. Existing transport laws
then apply to its supplied correspondences; they do not prove (1)–(3).
Output support may lose E only after projection establishes that no independent
same-point contribution remains. This does not assert that every inferred
program has the decorated dynamic profile needed by the broader handler
simulation theorem.

At this baseline (1) fails to be supplied for concrete negative p because source
admission/target construction reject it; (2) has only covariant Allowance checks
and detached nonempty evaluation; (3) covers existing view/bundle copying and
RelationId completion but leaves arbitrary nonempty payload/residual transport
and recursive invalidation open. A theorem quantified only over currently
accepted negative concrete actions would be vacuous. Do not present it as
implemented subtraction.

## Evidence, limits and recommended next action

Read-only commands: targeted `git show <baseline>:<path> | nl -ba | sed ...`,
`git grep` at each frozen ref, direct governing-document reads, targeted source
tree listing, `git rev-parse`, and `git hash-object` without `-w`. Initial broad
task/log reads were truncated; follow-up reads targeted exact headings/tails
and owner ranges. No full repository audit is claimed. No pending question
contents were inspected.

No Cargo, compiler/Oracle execution, Python probe, seed enumeration, mutations,
timing measurement or independent review ran. Historical checker counts above
remain bounded characterization with supplied flags/shared rules. Oracle and
successor source were inspected independently, but both are interpreted under
the same accepted policy; source inspection alone is not oracle-independent
semantic correctness. Parameterized effect variance, arbitrary source roles,
complete dynamic incidence/selection, all-client principality and F5 cutover
remain outside this audit.

Resource use: sequential short source/document commands only; no heavyweight
process or benchmark sample. Exact aggregate CPU/RSS/wall-time was not measured.
Freeze check: scoped whitespace diff check recorded in the completion report.

Recommended next action: give the annotation/context producer a confirmed
constructor-plus-consumer packet for bridge clauses (1)–(2), retaining exact
source set/position and the real residual dependency at formation; require the
prover's selected transition bridge and lifecycle evidence before enabling
negative concrete admission. Another model over supplied attachment flags
cannot discharge this source gap.

## Commit packet

- Exact lease: `notes/progress/2026-10-10-contravariant-source-bridge-audit.md`.
- Baseline: `32c65f07671b9de7b05ece3044a714c4d8d0e61b`.
- Claim/review: compiler-referee PASS; proposed bridge obligation; no theorem
  closure, semantic promotion or production authority.
- Checks: targeted frozen-source/document inspection; leased-path whitespace
  diff check after final write; no builds/tests/Oracle execution.
- Direct pinned blob IDs: `candidate_effect.rs`
  `8a56220edd907cbf52ddfd81635c55bef3a8d3c7`, `candidate_source.rs`
  `d44026eb53c69b49c2c6e6d5d281c47675928466`, HIR `source_annotation.rs`
  `51b18f029540dbf549c05a8718e2c1ed4a6e2302`, hygiene design
  `2a2517f94df2969ed4c865298cb8395998b07c65`, concrete implementation design
  `c8c64dee1b19c864e8d6ac558162d4c3989f8c06` matched live files at inspection.
- Concurrent dependency delta: pinned `candidate_context.rs` blob
  `26846297c7ae4e1eb003252dcfcef7cdc68ebfc3`; observed live blob
  `9cde58ddce0a2bb308567fc2b2d1f0aa0d1f5089`. The independent reviewer
  inspected this delta and found only detached `rename_contexts` preparation,
  with no production caller; live contextual transport remains unchanged.
- Proposed message: `research: audit contravariant annotation source bridge owners`.
- Shared deltas left to primary/curator: update `tasks/current.md` and any
  theory/index locator to distinguish repaired HIR/covariant source evidence,
  retained RelationId completion, and missing concrete-negative attachment /
  residual consumer / nonempty lifecycle bridge; annotate the historical
  policy §4 table through an appropriate status record rather than using it
  as a current implementation inventory. No shared paths edited here.
