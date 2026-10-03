# Concrete compatibility boundary audit

Date: 2026-10-03
Branch: `research/simple-sub-intrusion`
Mode: M3 semantic/source-authority clarification
Review budget: one architect pre-write audit, one implementation-source explorer,
and two independent bounded reviewers (`compiler_referee`, `spec_auditor`)

## Decision recorded

The user's current decision allows transitivity for bound propagation among
type variables. A concrete type pair is checked by a local compatibility
judgment that can resolve cast/adaptation evidence. Compatibility successes
do not enter one transitive concrete subtype closure. The supplied optional
Record chain is accepted by Oracle although its direct string-to-int optional
Record comparison is rejected. These observations constrain the successor
design but do not yet specify field adaptation or optional-Record source
syntax.

`notes/design/2026-10-03-concrete-compatibility-boundary.md` records the
relation split, preserves the declared mathematical scope of the reviewed
structural theorems, and makes evidence-preserving compatibility normalization
the next research gate. It grants no implementation authority.

## Bounded repository evidence

- `yu-solver::TermView` and `InferenceSession::constrain_live` represent
  polarized Function comparisons and variable-bound replay, but no Record or
  adapter constructor.
- `yu-types` has no Record or adapter constructor in its closed type algebra.
- Successor HIR excludes cast declarations from the current resolved
  expression envelope. The parser and stable-core corpus contain cast syntax
  and an implicit value-cast example.
- Successor named-Record type syntax requires `name: Type`; optional Record
  pattern defaults are different syntax and semantics.
- The typed-boundary adapter theorem covers fixed-shape Function/Thunk
  realization. It does not decide concrete compatibility or optional Records.
- Frozen Oracle Record comparisons and registered nominal casts use distinct
  paths. `enqueue_record_fields` skips absent lower fields and otherwise
  derives matching-field comparisons; specialization separately checks
  missing required upper fields and matching children. By contrast,
  `NominalCastNeeded` for different nominal paths adds candidate cast
  constraints, then eligible source boundaries resolve exact path candidates
  as missing, unique or ambiguous. The optional-Record examples therefore do
  not establish that Oracle routes them through the nominal cast table.
- Specialization recreates materialized source-boundary pairs for expression
  consumption, function bodies and computed definition signatures. Its local
  type graph then propagates variable-to-variable edges, stores variable to
  concrete bounds, and validates concrete Record pairs separately. This is
  evidence that concrete validation is not inferred solely from whether an
  earlier propagation step emitted a child comparison; complete transport of
  every inference obligation remains unproved.
- The Evidence VM has a recursive Record adapter path, but generic Record
  `Coerce` can lower to an alias, and the directional runtime-equivalence
  shortcut can preserve the original Record including extra fields. The
  recursive adapter rebuilds target fields, except deferred source-Thunk to
  non-Thunk fields; it does not resolve registered nominal casts recursively.
  Explicit Record literals can materialize registered casts at child fields.
  The older mono runtime returns supported Record values unchanged. These
  paths do not constitute one existing runtime resolver.
- Nominal cast handling also differs by phase: type-graph constraint
  generation instantiates all exact-path candidates, emission takes the first
  exact-path rule, and `CastTable::resolve_value` separately classifies
  missing/unique/ambiguous declarations. This remains historical evidence,
  not a candidate selection policy for the successor.

This evidence supports a common successor compatibility boundary only as a
candidate local dispatch interface across checking and resolution. Record
shape derivations, selected nominal cast evidence and executable adapter plans
must remain distinguishable unless a preservation proof justifies stronger
unification. It neither rejects the user's direction nor establishes that the
Oracle paths already share a runtime adapter mechanism.

The reviewed §5 candidate now makes the Record check phase-explicit: a missing
optional target field is permitted, a missing required target field is rejected
at concrete validation, extra lower fields are ignored, and shared fields
generate child compatibility obligations. Frozen inference skips a child
comparison for optional-lower/required-upper, while concrete validation still
checks a present matching child's type; the skip alone is not accepted as a
final result. This reproduces the supplied optional-Record discriminator
without transitive closure. It does not yet prove how a successor preserves
such obligations across phases or realizes the result at runtime.

The new draft passed bounded independent semantic and conformance reviews with
no findings. A further compiler-referee delta audit verified the frozen
Record and nominal-cast routes described above. The §5 proposal had an
architect pre-write audit and fresh compiler-referee and spec-auditor reviews;
all reported no findings within scope. The compiler referee did not audit the
whole successor call graph, full predecessor proofs or backend adapter
realization; the spec auditor did not run Oracle or tests. No code or test
expectations changed. A focused regression audit of the added specialization,
runtime and cast-route evidence found one qualification: thunk-to-value Record
fields may be deferred instead of recursively adapted. The text was updated
and the primary cross-checked that branch in the frozen runtime source.
`git diff --check` passed. No tests, builds or measurements were run.
Measurement budget consumed: 0.

This runtime-route delta used one read-only implementation-source explorer and
one independent regression auditor. The auditor found that source-Thunk to
non-Thunk Record fields may be deferred by the Evidence VM; the design note
now states that exception. The primary independently checked the cited
deferment branch. Review was limited to these added source-path claims and did
not re-audit the prior relation theorem or candidate Record table.

## Boundary-conservation correction

A bounded architect audit found that the prior §2 candidate sentence deriving
`Compat(A,B)` whenever a variable path exposed concrete endpoints was not
justified by the user's authority. Under the conditional interpretation where
`Compat(A,X)` and `Compat(X,B)` remain separate suspended local obligations,
assigning `X={}` satisfies both optional-Record checks while direct
`Compat(A,B)` fails. Therefore variable-bound transitivity alone cannot
license an unconditional concrete lower/upper cross-product.

The candidate now retains source-boundary identities and requires source
semantics to justify any moved bound payload or additional concrete query.
The next theorem is boundary-obligation conservation under a shared
assignment: original guarded checks are neither lost nor replaced, and any
additional mandatory query must have its own source derivation. This does not
settle the source meaning of variable bounds or suspended checks. The
candidate edit received clean bounded compiler-referee and spec-auditor
reviews; both confirmed the conditional counterexample and unresolved source
semantics. No implementation or tests were run. This clarification preserves
the user's relation split and does not extend ordinary structural closure.

## Explicit bound-replay route

A follow-up frozen-source read found that Oracle has a specific same-variable
lower/upper replay rule. `cpk_lower_bound_replay_actions` prepares routes from a
new lower bound to existing uppers; `cpk_upper_bound_replay_actions` does the
symmetric operation. Eligible replay comparisons retain
`BinaryReplayDerivation { pivot, lower, upper, rule }` and replay claim parents;
trivial, duplicate and evidence-only routes can be prefiltered. An independent
architect audit confirmed the significance: this is a bound-derived concrete
query, not composition of two successful local compatibility judgments. The
conditional `X={}` counterexample only rejects interpreting the pair of local
checks as the entire variable-bound semantics; it does not refute a distinct
bound-replay judgment.

The theorem gate is therefore refined from plain boundary-obligation
conservation to bound-replay conservation: establish which source bound
premises admit replay, preserve original boundaries and replay parent
identities, prove no mandatory query is lost or unjustifiably added, and retain
the generated query's own local conversion evidence. The frozen proof parents
do not locate the runtime expression boundary for executing that conversion.
Architect pre-write audit plus independent compiler-referee and spec-auditor
reviews found no blocking or major semantic/conformance issue. Both reviewers
identified one factual overstatement that replay plans always enqueue; the text
now records route eligibility and prefiltering. No tests or builds were run.

The design now sketches the judgment split as candidate rules: variable edges
transport lower/upper bound payloads, while a same-pivot lower/upper pair
generates a fresh locally resolved `Compat` query. The compiler referee found
no semantic finding and confirmed that no successful `Compat` judgment is a
premise of those rules. The spec auditor found no conformance finding and
confirmed that source typing, guard propagation, principal solving and
conversion placement remain unapproved proof obligations. The equations are
not implementation authority.

The finite fixed-graph closure lemma is now recorded in
`notes/design/2026-10-03-finite-bound-replay-closure.md`. Independent semantic
and conformance review found two minor formal gaps: context domains and replay
key counting, and the fixed background facts needed by conditional model
conservation. The primary repaired both and clarified that unresolved
endpoints stay suspended because this lemma defines no solving rule. Review
confirmed the approved distinction: no successful concrete `Compat` judgment
is composed. The lemma proves only finite least closure and conditional
conservation for the abstract rules; source meaning, guard soundness,
boundary-replay completeness, conversion placement and source-wide finiteness
remain open. No implementation, tests, builds or measurements were run.
Measurement budget consumed: 0.

The next semantic audit asked whether replay follows from treating lower and
upper payloads as independent suspended checks. It does not: with optional
Record endpoints `{foo?: string}`, `{}`, `{foo?: int}`, the two local checks
pass while replay's direct check fails. This is recorded as a necessary
condition, not a rejection of the frozen replay route. A transparent
producer/consumer port is one conditional hypothesis: variable transport keeps
the producer view intact, while an actual concrete adaptation boundary ends
that transport and starts a new producer contract. Fresh compiler-referee and
spec-auditor reviews found no issue in the hypothesis' presentation; neither
establishes source applicability. Frozen-source inspection then grounded a
producer-to-local-to-consumer path through open value slots and located
registered casts at concrete function-argument consumption/emission. A local
annotation constrains the same existing value slot and does not establish a
conversion boundary. The design draft now cites the frozen local-lowering,
specialization and argument-emission owners; a bounded semantic delta review
found no issue. A follow-up clarification now says a successful check alone
does not by itself establish a new consumer-facing contract. The contract
could be sealed by a source check even if runtime preserves the original value;
conversion evidence and typed-view evidence are separate. A reviewer found a
major overclaim in the prior version, which incorrectly made emitted conversion
necessary. The primary revised the hypothesis to leave check-only typed views
open for source proof; the same reviewer confirmed the major finding is closed
with no new issue. Successor source generation and exact Record adapter
placement remain unverified.
No tests, builds or measurements were run.
Measurement budget consumed: 0.

A bounded frozen-source ledger was then added to §8 of the closure note. It
separates application `SourceBoundaryId`s, inference `BoundRecordId` replay
parents, specialization `SpecializeSubtypeProvenanceRecordId`s and emitted
cast instances. The frozen routes do not provide one identity chain from an
original source boundary through replay to the emitted conversion; cast
selection uses solved endpoint types and rules. Check-only Record shape paths
can retain the original expression while presenting expected-type metadata,
but whether they seal the source contract or discharge replay remains unknown.
Independent semantic review found one minor phase-boundary overclaim: materialized
argument comparisons may still contain open variables and are not already
concrete compatibility checks. The primary corrected this and clarified that
occurrence keys look up existing sidecar evidence. No blocking or major finding
remained. No tests, builds or measurements were run. Measurement budget
consumed: 0.

The next bounded source read found that each materialized consumption submits
its endpoint comparison, while equal endpoints may be elided and equal
semantic keys may share merged graph/provenance records. `add_expr_consumer`
combines repeated consumers at one `ExprId` by intersection. `finish` resolves
one aggregate solved consumer, and boundary emission reads that solved actual
and consumer pair. Thus endpoint-based emission is at the same expression
site, but it does not identify which member consumption—or which replay
pair—the emitted boundary discharges. A single-consumer path remains a
possible conditional correspondence case; it cannot establish the general
rule.
The closure note and task gate now include this multiplicity gap. This is
frozen-source evidence only; no successor semantics or implementation
authority follows from it. No tests, builds or measurements were run.
Measurement budget consumed: 0.

The requested common-dispatcher direction was then examined as a documentary
candidate. §5.1 gives one local query boundary with tagged structural, Record
and nominal-cast check derivations, while keeping compatibility evidence,
selected conversion/adapter evidence and emitted execution correspondence
separate. Record children remain independent local queries; their successes
cannot compose into another check or an executable aggregate adapter without
a realization proof. An architect pre-write review plus independent bounded
compiler-referee and spec-auditor reviews found the candidate consistent with
current authority. Cast policy, check-only identity, Record runtime behavior
and conversion placement remain undecided. The candidate does not change the
theorem order: establish bound-replay conservation before selection and
runtime realization. No implementation or tests were authorized or run.

A further frozen-source pass sharpened the admission gate. `step_subtype`
stores `A <: X` as a lower bound on `X`, `X <: B` as an upper bound on `X`,
and `X <: Y` as lower `X` on `Y` plus upper `Y` on `X`. The lower/upper
builders do not enqueue every raw same-pivot pair: they require prepared
`pair_replay` evidence, preserve both bound record IDs and pivot, and compose
weights in lower-to-upper order. Lower insertion can use incremental row
residual routes; ordinary actions can also be trivial, duplicate or
evidence-only. An architect audit recommends representing ordinary pair
selection with a separate abstract `ReplayAdmissible` premise and keeping
admission distinct from worklist materialization. Its source meaning remains
unproved, and residual row routes are outside the current fixed-endpoint
closure fragment. The candidate equation now has a separate
`ReplayAdmissible` premise, and the theorem gate covers only ordinary
fixed-endpoint pairs until a residual-route carrier is proved. This does not
adopt frozen proof-store policy as language semantics.

An architect pre-write audit and independent bounded compiler-referee and
spec-auditor reviews found no issues in this refinement. Their scope was the
new admission premise, ordinary fixed-endpoint closure claims and synchronized
records; they did not certify its source meaning or the excluded incremental
row routes. No tests or builds were run, and implementation remains
unauthorized.

A follow-up read of `compose_prepared_replay_route` exposed another
conservation condition: live coverage by upper-claim roots can suppress an
ordinary pair for a concrete lower endpoint when all upper parents are
covered; uncovered parents or no upper parents select generic replay.
Variable lower endpoints retain covered parents unless an incremental route
handles them. This is CPK route policy, not a successor type rule. A
suppressed pair needs an independent explanation: either the source has no
such replay obligation, or its obligation remains discharged by identified
evidence. Endpoint equality and previously successful local compatibility
results alone cannot show that. The current fixed-endpoint theorem records
this discharge question.

An independent compiler-referee delta audit confirmed the frozen coverage
conditions and found no issue in the conservation wording. It verified the
concrete-lower suppression case, variable-lower parent retention, and the
separate incremental route behavior. This review does not establish the
successor source meaning of coverage or discharge.

A bounded follow-up traced the owner path behind that predicate. When a
semantically new lower insertion reaches row routing at the same source
variable, it invokes each unprocessed local unweighted row state before
ordinary replay composition. A matched lower
creates row-item child obligations, advances the residual, and routes against
the original upper; an unmatched or ineligible lower routes against the
current reduced upper; when selected, the corresponding incremental replay
applies the lower weights unchanged. This supports a
candidate reading of row coverage as delegated processing, not as a successful
local compatibility check. The processed-lower set records visitation and
does not itself prove a check succeeded.

The local explanation fails as a universal account. Frozen
`unweighted_row_upper_cross_source_replay_inherits_covered_lineage` creates a
covered upper on `alpha`, derives a covered upper on `beta` through a Function
return-effect edge, and asserts `beta` has no row-reduction state. A later
concrete lower on `beta` receives no generic replay against that inherited
upper, while the test also asserts no residual contamination. The contract
shows inherited coverage can suppress a pair without a row router at that
owner; it does not prove where the interaction is represented. The remaining
gate is graph-wide conservation through variable-edge transport to the
originating row state, including guards, weights, provenance and eventual
consumer conversion. Independent compiler-referee and spec-auditor reviews
confirmed the local-route bounds and the cross-source counterexample; they did
not certify successor semantics. No tests or builds were run.

A bounded call-path reconstruction explains the tested `alpha`/`beta` case:
the new `beta` lower can replay against beta's separate upper `alpha`, which
inserts a corresponding lower at `alpha`; alpha's row state matches its item
against the original row upper and leaves the reduced residual unchanged.
The test directly checks beta's suppressed residual pair and absence of
residual `f`, but does not assert this alpha replay, its row derivation, or the
original-row check. Those links come from tracing `step_subtype`, lower-bound
replay, and row routing. Since the fixture's constructor heads have no
arguments, this case also omits child-argument obligations. The trace narrows
the open graph-wide gate for this example only. No test was executed.
An independent compiler-referee delta review found no issue in the reconstructed
path or in the separation between test assertions and call-path evidence.

## Next gate

Prove graph-wide bound-replay conservation for a fixed finite source
elaboration and closed Record shapes. Define concrete-to-variable bound
meaning and admissible same-pivot replay; account for covered row uppers both
at their owning variable and through inherited coverage on other variables.
Preserve original guarded obligations and required replay queries with their
identities, without deriving queries from successful `Compat` compositions.
Prove finite replay provenance/context closure before extending residual
normalization. Then establish where replay conversion evidence executes,
specify Record adapter behavior and prove evidence-preserving normalization
and residual factorization. Source-wide context finiteness, unknown Record
shapes, effectful interfaces, lifecycle and implementation remain open.
