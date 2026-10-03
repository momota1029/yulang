# Concrete compatibility boundary audit

Chronological record. The final section records the user's later clarification
to one inequality judgment; that clarification supersedes the earlier
candidate `Bound`/`Compat` terminology below.

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

A bounded proof/refutation audit refined the upstream-spine candidate. Source
`Var(vᵢ) <: Var(vᵢ₋₁)` installs the mirrored upper on `vᵢ`; a fresh normalized
concrete lower replays to `vᵢ₋₁` if the prepared upper entries are empty or
include an uncovered root. Exact endpoint transport additionally requires
that the payload outer head has already passed `step_subtype` normalization:
`Bot` exits and `Union` splits before variable-upper propagation, while
`Stack`/`NonSubtract` rewrite. The pair must be admitted and processed without
terminal failure. Each subsequent hop needs a new lower insertion and an
eligible mirrored upper at replay time, or independent evidence that the
corresponding obligation was already processed. Equivalent insertion skips
replay; duplicate canonical replay merges evidence without enqueueing. Empty
weights and identity-preserving extrusion remain premises. The source-generated
`var_var_replay_materializes_transitive_edges` test supports the `int`
constructor instance; the raw multi-hop bound test does not install mirrored
uppers. Cycles, covered-only bridges, mixed-root provenance beyond retained
uncovered roots, filters, contexts, and consumer conversion remain open. This
is a frozen operational characterization, not successor semantics. An
independent spec-auditor delta review found no further findings after the
normalization premise was added.

## Next gate

Prove graph-wide conservation between source inequalities and endpoint-dependent
solver transitions for a fixed finite source elaboration. Account for covered
row uppers both at their owning variable and through inherited coverage on
other variables. Preserve original guarded inequality tasks and required replay
queries with their identities, without deriving a new query from successful
concrete-resolution outcomes. Prove finite replay provenance/context closure
before extending residual normalization. Then establish where replay evidence
executes, specify Record adapter behavior and prove evidence-preserving
normalization and residual factorization. Source-wide context finiteness,
unknown Record shapes, effectful interfaces, lifecycle and implementation
remain open.

## User clarification: one endpoint-dependent inequality judgment (2026-10-03)

The user clarified that Yulang has one basic type inequality `A <: B`; its
solver dispatches on endpoint form. Do not model `Bound` and `Compat` as
separate semantic judgments followed by a cast-resolution relation. Variable
edges, lower/upper payload records and replay routes are internal solver state
for the same inequality. Concrete structural checking, optional Record rules,
registered cast resolution and adapter resolution are endpoint-specific ways
to solve it; cast/adapter results are evidence or realization attached to that
query.

The non-composition constraint remains: variable-edge propagation may use
transitivity, while concrete resolution successes do not compose into a third
concrete inequality. A replay is a newly generated inequality task and needs a
source-preserving route; same-pivot coexistence and earlier concrete successes
alone do not authorize it. The optional Record example remains the direct
counterexample. A failed replay is a candidate solver failure until proof
establishes that source rules require the replay.

The boundary design note now records this single-judgment direction. The
finite replay note is reframed as a closure theorem about internal solver
transitions, not separate semantic `Bound`/`Compat` relations. Its source-ledger
conservation, concrete evidence placement and source-wide context gates remain
open. Architect audit found this reformulation viable without a new user
choice; no implementation or source rejection is selected.

## Bounded application-consumption subgate (2026-10-03)

A frozen-source trace now identifies a candidate first subgate for the open
source-to-replay conservation proof: the argument lane of one ordinary
application with a literal leaf, non-Record constructor endpoints, one
monomorphic closed Function signature and one callee
scheme instantiation with no quantified variables, one consumer, empty
weights, and no aliases, cycles or row reduction. The application lowerer
creates an `ApplicationArgument` boundary and Function demand; a callee-pivot
replay exposes the Function comparison, Function decomposition derives an
argument comparison, and literal lower and upper payloads can produce a
selected same-pivot replay. Specialization
independently materializes the argument check, while emission chooses a cast
from solved actual/consumer endpoints. Specialization also submits a callee
Function check. For this closed non-Record signature, the callee argument
component remains equal; reflexivity of the full Function pair still depends
on return and effect components, whose acceptance impact needs accounting.
Record shapes may change that callee consumer and need separate accounting. The inference replay identity does not
flow to cast selection, so the subgate uses endpoint/boundary correspondence,
not ID equality.

A bounded compiler-referee delta review found no blocking or major issue in
the corrected scope. A subsequent source audit found that ordinary annotated
parameter effects materialize from `Neg::Bot` to `Never`, while pure
application construction uses `EffectRow([])`. Therefore the callee Function
query is not reflexive in the literal representation: under the candidate
closed shape, Function decomposition creates `EffectRow([]) <: Never`, which
the current solver accepts through its non-fixed-head fallback. This is a
conditional non-rejection argument only; the fixture's complete exported
scheme and absence of extra bounds/wrappers remain unproved. The next bounded
step is to establish that scheme, then prove the conditional acceptance path.
No tests or builds ran.

The initial review found that a general expression may contain both a block
root and tail materialized comparison. The subgate was narrowed to a literal
leaf so the one-comparison premise is explicit; extending it to blocks must
preserve both identities and boundary relations. Review also caught an
omitted callee-pivot replay and the need to allow one monomorphic callee
instantiation; both are now explicit, and the focused delta review found no
remaining issue. The frozen missing-cast test
asserts `int -> bool`, `OneSidedReplayPair`, an `ApplicationArgument` owner,
and the `42`/`f` source sites; this closes one fixed inference-side witness.
Source inspection also traces the same unique-cast argument through
specialization: `apply_type` submits `int <: bool`, `finish` resolves the
actual/consumer pair, and the emitter wraps the argument with the unique cast
application. This is not an executed end-to-end runtime witness, and no replay
identity reaches emission. The general two-direction lemma remains open.
An independent compiler-referee delta review confirmed this fixed positive
source path and its endpoint scope; the emitted runtime result was not run.
Frozen coverage suppression, multi-consumer aggregation, Record realization
and source-wide replay policy remain open.
See §8.1 of `notes/design/2026-10-03-finite-bound-replay-closure.md`. No tests
or builds were run.

The fixture's stored `poly::Def.scheme` and SCC simplification of its skeleton
slots have not been established. Accordingly, the specialization and unique-
cast path above are conditional source-path evidence, not a verified
successful end-to-end instance. The next bounded evidence target is the
stored scheme (including quantifiers, role predicates, stack quantifiers and
recursive bounds), followed by the callee-query non-rejection trace under
that exact materialized signature.

### Follow-up: application callee scheme and materialization mode (2026-10-03)

A source trace through the annotated declaration, its internal skeleton,
compact simplification and SCC publication derives the scheme predicate
`Fun(bool, Never, Never, bool)` with empty value/effect quantifiers, role
predicates, stack quantifiers and recursive bounds. This is a source
derivation; the diagnostic fixture has no direct scheme assertion. The
independent delta reviewer did not certify the exhaustive skeleton-variable
elimination, so retain the derivation as source evidence rather than a tested
fixture fact.

Review corrected the TaskSolver materialization premise: principal inference
materialization turns the positive bottom return effect into
`EffectRow([])`, while the negative argument effect remains `Never`. The
callee type is therefore `Fun(bool, Never, EffectRow([]), bool)`. Pure apply
replaces its argument effect by `EffectRow([])` and copies the return effect,
so the callee comparison decomposes into reflexive bool/result-effect
children plus `EffectRow([]) <: Never`. That child reaches the current
non-fixed-head fallback and succeeds. This is a single-query resolution; no
concrete successes compose. The zero-cast fixture still fails before
specialization, so this does not establish an executed successful instance.
The next gate is two-direction conservation for the complete application
ledger and materialized consumer/evidence. No tests or builds ran.

### Follow-up: reviewed two-lane application crosswalk (2026-10-03)

The fixed application ledger now places the Function-derived `X <: bool`
bound and literal bounds `int <: X`, `X <: int` beside the materialized
consumer query `int <: bool`. The nontrivial selected replay and the
specialization query share ordered endpoints and the `ApplicationArgument`
consumer boundary; `int <: int` is reflexive. The separate callee Function
query has one non-reflexive effect child, `EffectRow([]) <: Never`, which the
current non-fixed-head fallback accepts. A bounded compiler-referee delta
review found no issue in this two-lane crosswalk and confirmed that it uses no
concrete-success composition or replay-ID identity.

The review also pointed out a resolver-local check omitted from the
application-owned lanes: `constrain_direct_cast` filters candidates to value
casts with matching ordered source/target paths, then submits each matching
candidate scheme against `Fun(int, bool)`. Emission subsequently solves the
selected cast body at that signature. These are witness/instance checks within
resolution of the same concrete inequality, not another cast relation. Source
tracing of the fixture's sole cast derives a nonrejecting candidate Function
check and equal bool/Function endpoints for the selected body instance.

A follow-up compiler-referee review found no blocking or major issue. It found
one minor overstatement, now repaired above: unrelated registered casts are
not instantiated. The review confirmed the ordered candidate Function check,
selected body signature and equal body/definition endpoints, while limiting
its conclusion to the fixed fixture. It does not establish executed runtime
success, general candidate behavior, successor cast policy, or the unstored
scheme. No tests or builds ran.

### Semantic correction: endpoint kinds and polarity (2026-10-03)

The user clarified that `never` is value/data bottom and `Any` is value/data
top; neither is an alias for empty effect or an effect-universal endpoint.
Polarized solver bottom/top are also distinct internal sentinels. The prior
description of the Function fixture as effect lifting with two empty rows was
too strong: frozen `Neg::Bot`/`Neg::Top` materialization and
`is_pure_effect` are representation behavior, not semantic authority. The
exact user-stated coupled Function case remains the target, but its
position-sensitive interpretation and combination algebra are open. The
frozen `EffectRow([]) <: Never` fallback and source-traced candidate cast
check are characterization only. The current task is to derive the coupled
rule with kinds and polarity retained; no tests or builds ran.

### Source-semantic effect-lifting derivation candidate (2026-10-03)

The successor derivation now starts from the user-selected source call rules,
not Oracle propagation: an ordinary `Value(a)` parameter receives a reified
argument computation, forces it at entry in the same activation, rebinds its
value, and executes the body. Thus the complete invocation's may-effect
support is bounded using both the argument bound `d` and body bound `b`; the
intended `[b,d]` coupling reflects one argument computation executed at
entry. This explains the coupling mechanism and why the same `d` must occur at both
Function ports. It does not explain how the displayed negative argument
effect endpoint `never` denotes or selects that `Value(a)` source role. The
successor bridge from the kinded Function interface to the source role, exact
denotation/normalization of `[b,d]`, and symbolic typed-family transport
remain open.

Luna's bounded frozen-source report supplies only implementation facts at
commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`: effect lowering uses
distinct positive/negative row nodes; role materialization maps some
polarized bottoms/tops to `Never`/`Any`; `is_pure_effect` accepts both
`Never` and empty rows; and inference has a special negative-bottom Function
branch. Those facts characterize the historical artifact risk but are not
premises in the source-semantic derivation. No tests or builds ran.

Luna's follow-up source map adds the concrete row-subtraction path, still only
as characterization. At the same frozen commit, `Pos::Row(items)` and
`Neg::Row(items, tail)` are distinct nodes; Function ports carry opposite
polarities (`poly/src/types.rs:740–762,781–796`). Concrete row matching accepts
same-path constructor heads or the same variable (`propagate.rs:860–865`),
and matching constructor payloads adds invariant argument constraints
(`propagate.rs:923–989`). For weighted upper bounds,
`row_effect.rs:88–233` filters row items using active stack facts, subtracts
retained families from the left weight, creates/reuses a residual variable,
and routes that residual to the original tail. Set/exception transforms are
implemented at `row_effect.rs:1005–1062,1190–1274`. Signature lowering records
`Subtractability`/stack facts and wraps weighted endpoints
(`signature_effect.rs:382–450`; `poly/src/types.rs:147–154,292–309`).

Function propagation itself uses different paths for the negative
argument-effect `Neg::Bot` case and the general case
(`propagate.rs:212–270`); variable-to-row transport enters the upper-bound
path (`propagate.rs:104–138`). The special branch, row matcher, and residual
transforms describe implementation operations only. They do not determine
the successor descriptor semantics, define how a `never` spelling enters an
effect port, or authorize four independent Type subtyping checks. No tests or
builds ran.

### Initial descriptor comparison candidate; superseded by later user direction (2026-10-03)

The user first redirected the Function rule away from independent subtyping
of effect fields as general `Type`s. The initial candidate said
contravariant descriptors contain
effect variables plus subtractive concrete effect records; covariant effect
descriptors contain effect variables plus concrete effect records. Their
relation is resolved jointly from shared effect-variable correspondence and
subtraction evidence. A Never/Any/empty-row lattice explanation is outside
this rule. This supersedes the earlier Value-role-to-negative-`never` bridge
as the proposed Function comparison explanation; source entry-force semantics
remain evidence that argument effects are observable through calls.

Sol's bounded derivation proposes one joint resolution witness
`W=(θ,M,S,R,Ψ)`: shared effect-variable correspondence; concrete-family
matches with type-argument obligations; admitted subtraction steps with
context/ownership; correlated residual routing; and retained family
equations, `K,D`, and request witnesses. For the intended examples the
witness carries the same target effect variable from argument to result,
preserves source contribution `b` in `[b,d]`, and generates no independent
`d <: never` child. The descriptor elaboration of the effect-position
`never` spellings remains unresolved; they are not silently reinterpreted as
empty effect, value bottom, or a solver sentinel. `[b,d]` has no derived
lattice or normalization law yet.

Luna's frozen-source work remains implementation evidence only: row matching
preserves effect-variable identity, family matches emit invariant argument
obligations, and weighted residual routing carries subtractability facts and
context. Sol's report treats those operations as evidence for a candidate
shared witness, not as the successor semantics. The design note and task map
now follow this latest direction. No tests or builds ran.

### Review closure for the superseded Value-role candidate

A bounded compiler-referee review found no blocking or major issue in the
earlier source-semantic candidate. It identified one wording overclaim: entry
force and body execution justify a conservative combined output bound, not
that both supports must occur on every execution (an argument may diverge
before the body). That wording was repaired. This review predates and does not
cover the later joint descriptor witness or its subtraction obligations. No
tests or builds ran.

### Mixed-row and nested-component refinement (2026-10-03)

The user clarified that a body/tail syntax split is not fundamental. Effect
variables and concrete records may be interleaved as elements of one row;
simple nested rows may flatten, while nesting must remain when it preserves a
separate co-occurrence component. Sol's candidate grammar is
`E ::= α | ρ | row(E₁,…,Eₙ)`. Its normalization invariant retains the
co-occurrence partition, variable correspondence, record attachment, and
scope/owner evidence; flattening is admitted only when these are preserved.
The joint Function witness therefore grows a `Π` component for co-occurrence
classes and permitted merges, which travels with `θ,M,S,R,Ψ` through
normalization and subtraction.

One semantic choice remains for user direction: when co-occurrence merges
`'a` and `'b`, does it identify their original effect witnesses (so all
outside references share one witness), or does it form one aggregate row
component while retaining separate original witnesses and their incident
constraints? The examples distinguish a same-class flattenable row from a
nested independent component, but do not settle how same-class merging affects
outside references. No tests or builds ran.

The descriptor-section delta review found no blocking or major authority
drift. It requested two minor precision repairs: make use of `[b,d]`
conditional on it soundly presenting the combined source support bound, and
label the prior review as scoped to the superseded Value-role explanation.
Both repairs are now reflected above. The full witness calculus and
subtraction semantics were not certified. No tests or builds ran.

The mixed-row delta review found no blocking, major, or minor issue. It
confirmed that flattening is conditional on preserving the recorded component
structure and that the open choice about original-witness identity remains
explicit in the records. The full normalization and subtraction calculus was
not certified. No tests or builds ran.

### General component clarification and Sol derivation (2026-10-03)

The user clarified that “effect variables + concrete effect records” is too
narrow. Contravariant effects use abstract type components and concrete type
components generally; effect variables and effect records are examples.
Eligible concrete components may be subtracted in contravariant position, and
nested rows may be retained to preserve abstract components. Covariant
descriptors likewise admit both abstract and concrete type components.

Sol revised the candidate grammar to
`E ::= Abstract(A) | Concrete(C) | Row(E₁,…,Eₙ)`, with `A` and `C` retaining
their original terms, identities, scope and ownership. These are semantic
classes under an admitted endpoint interpretation, not a proposal for new
source constructors. The witness `θ` now tracks shared abstract terms and
components; `Π` tracks nesting, co-occurrence, and justified consolidation;
`M` handles admitted concrete matches and dependent constraints; `S` records
eligible subtraction; `R` retains correlated residual comparisons; and `Ψ`
retains original terms and dependent evidence. Collecting common variables is
an auxiliary view of the abstract components, not their complete
representation. Normalization must preserve the joint solution set through
an original-term map; the earlier structural equality theorem does not
automatically establish this broader factorization.

Still unresolved are the source meaning and classification of abstract versus
concrete components, when classification can change during solving, eligible
subtraction, co-occurrence consolidation versus equality, safe general-row
flattening, and the full Function resolution/factorization proof. The
intended coupled examples remain obligations. These corrections update the
design note, task map, and index. No tests or builds ran.

### Polarity-specific row form and witnessed reverse addition (2026-10-03)

The user fixed the row representation by polarity: covariant rows have a
canonical flat form, and correlations belong in constraints/evidence rather
than a row tree. Only contravariant effect handling may retain structure, as
needed for subtraction. The user further clarified that this is not a total
subtraction algebra: it is partial reverse addition, justified only when the
corresponding concrete contribution and its attachment in the accumulated
effect are known.

Sol recommends representing both polarities through one joint comparison
witness, with `N⁺` recording covariant flat normalization and its transport
map, `N⁻` recording only necessary contravariant structure, and `S` recording
the source-supported forward accumulation, concrete contribution and
attachment, and transport needed for a particular reverse step. A concrete
head or successful concrete comparison alone does not establish such a step.
Ambiguous preimages after normalization/co-occurrence consolidation require
the original attachment evidence; otherwise the solver retains a residual or
defers. This is candidate evidence notation inside the single inequality
solver, not a new semantic relation or a total inverse law.

The remaining semantic work is to define the covariant accumulation and
normalization rules, attachment provenance and ambiguity handling, eligible
reverse steps, and preservation of shared abstract components and dependent
constraints. The concrete matching/subtraction forms and the resulting
principality/soundness proof remain open. No tests or builds ran.

### Abstract-only contra meet and source-ledger conservation candidate (2026-10-03)

The user further clarified the contravariant normal form: a row containing
only abstract components may normalize to their meet `[]`; a row with any
concrete component is instead an attachment-preserving descriptor for
reverse addition, not itself a meet. The design, task map, and index now record
this distinction.

Sol proposes stating the fixed application-lane result as conservation of
source boundaries and proof obligations, without requiring inference and
specialization replay IDs to match. A source task is
`j=(origin, A <: B, Γ, consumer)`. A correspondence `ρ` maps solver tasks
either to an original task with ordered endpoints/context/consumer preserved,
or to a justified sub-obligation of that task's resolution witness.

The architect audit found that coverage under one shared assignment and
source-justified rejection obligations alone do not prove reverse completeness.
Each resolution rule needs an independent local-exactness premise: a root
witness is admitted iff one source-admitted alternative has an admitted family
of child obligations and its constraint/context/ownership transport holds.
Otherwise state soundness and reverse completeness separately. The fixed
unique-candidate fixture permits one conjunctive candidate branch; general
candidate checking must preserve alternatives and cannot reject the root
because an unselected candidate fails.

The callee Function check is nonreflexive and must relate to the independently
elaborated application contract; it cannot be called a sub-obligation of
nominal `int <: bool` without a derivation. The matching candidate's Function
check also needs the joint kinded descriptor rule. Only actually equal
administrative and selected-body endpoints use reflexivity. Those descriptor
checks must distinguish abstract-only contravariant components, which may
normalize to meet `[]`, from concrete-bearing attachment descriptors that
enable only witnessed reverse addition. The meet is not an empty-effect or
`Never` identity.

With local exactness as a stated premise, the fixed fixture yields a
conditional source-ledger conservation theorem: every source task and required
child obligation is covered under one shared assignment; constraints of
selected branches hold under it, while unselected alternatives remain guarded
and are not conjoined. Endpoints, context, consumer ownership and admitted
alternatives are preserved; stage-local solver IDs may differ. Forward
completeness expands each source witness via local exactness; reverse
soundness reconstructs each source witness from the admitted child family.
The fixed reviewed crosswalk supports endpoint and consumer correspondence,
but does not prove the nonreflexive descriptor checks' local exactness or
expose the stored scheme.

### Existing subtraction machinery versus “reverse addition” (2026-10-03)

At the user's direction, I reread frozen `main:spec/2026-05-31-effect-variable-subtractable.md`
(§§ Directed weight, Weight composition, Variance, Row upper bound, Filter,
Protect, Family arguments, Bound replay, Compact/finalize, and Runtime), plus
the Yulang3 Astra-era design interpretation in
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §8 and
`notes/design/2026-09-29-intrude-effect-hygiene.md` §§1, 3, 10–11, and the
existing coupled-interface candidate in
`notes/design/2026-10-01-coupled-effect-interface-core-draft.md` (formulation
comparison and one denotational row relation). The frozen spec defines a
directed operational constraint calculus: per-identity ordered push/pop
histories; active-family intersection; a row split at
`J = K ∩ Common(L)`; a residual with `L - J`, hash-consed by
`(source, J, L - J)`; invariant payload constraints when family heads meet;
and replay/variance transport. The Yulang3 interpretation explicitly treats
the old data structures as prior art only and requires a declarative source
meaning and preservation proof before retaining any of their transformations.

The overlap is substantial. The old calculus already has edge-local directed
weights, scoped subtraction identities, ordered eligibility budgets, row
splits, residual transport, and invariant argument checks. The coupled
interface candidate already has the source-owned identity/incidence,
shared-assignment, and relational transport account. Calling those facts
“reverse addition” does not make them new and does not warrant another
descriptor/provenance ledger. But the old operational weight evidence does
not by itself prove which source accumulation a concrete component belongs
to, and neither document yet proves that its proposed carrier fully supplies
the attachment needed by the user's partial inverse. That bridge is a real
open proof obligation, not permission to clone the carriers. The frozen spec
is not successor authority: it does not prove that Oracle-directed rules
preserve the successor's source denotation, and its `StackWeight` rules must
not be copied as meaning.

The precise new obligation is the source elaboration bridge from Function
effect-row components to existing carriers. In the coupled-interface
candidate, `g(o)` owns the family argument of a typed request occurrence; it
does not identify every abstract component. An abstract component may denote
an entire correlated row view, while a concrete component may contribute
multiple typed occurrences. The source rule must map each component to its
complete interface under the same `ν`, then preserve the existing occurrence
incidence `D`, predicate `K`, and any applicable directed-weight path/split.
The existing relation has the ownership/incidence/transport vocabulary; do
not copy it into another ledger. Exact component-to-occurrence elaboration is
not in the present source definition, so no exact mapping is derivable yet.

The coupled handler relation defines subtraction by the residual support of
the complete handler image, not by family-set difference. A handled request
may be emitted again by the raw continuation and remain in the outward row.
Therefore old `L - J` residual evidence alone does not prove a reverse step
that claims a family/key disappears from outward support; that claim needs
the corresponding output-absence proof through the complete handler image.
This is not a blanket condition for every reverse step: other partial
inverses must follow their own source accumulation rule. No lost fact requiring
a new carrier is identified yet. Prove the existing evidence sufficient first;
only propose a field if a specific source fact cannot be recovered from it.

Other genuinely new obligations are defining source classification and
correlation of abstract/concrete type components, proving canonical-flat
covariant normalization and polarity-specific contravariant descriptor
elaboration preserve the existing solution fiber, and jointly resolving both
ports for the linked `[b,d]` / shared-`e` cases. Existing `Force(D) >>= B`
source structure accounts for argument and body effects together, but does not
settle exact `[b,d]` combination, component classification, or `never`
elaboration. These are source-integration and preservation proofs, not
justification for another subtraction algebra.
Until a concrete evidence gap is demonstrated, partial “reverse addition” is
only a possible reformulation of existing subtraction evidence. No Oracle
`Never`/`Any`/empty-row behavior was promoted into the account.

The `W_j` tuple in §8.2 of `2026-10-03-finite-bound-replay-closure.md` is
proof notation only: its coordinates are views and obligations over existing
inequality, coupled-interface, and subtraction evidence, not a stored witness
bundle or new attachment/provenance mechanism. In particular, an `S` reversal
must be derived from the old scoped history and source accumulation; failure
to derive it leaves a localized proof gap and does not itself authorize a new
field. The design note now says this explicitly, and `tasks/current.md` keeps
the fixed application-lane gate as the next action. No code or semantic rule
changed.

### Fixed application-lane source exactness audit (2026-10-03)

A bounded Sol architecture derivation checked the §8.2 roots against the
ordinary-computation, source-interface adequacy, concrete-compatibility, and
coupled-interface clauses. It confirms two separate application roots:
`j_arg = int <: bool` and the nonreflexive callee Function check. An admitted
cast branch for `j_arg` separately owns its candidate Function check and
selected body-instance checks. Neither Function root can be obtained by
composing concrete successes.

The source machine gives the execution shape `Force(D) >>= B`, and the exact
interface transports it under one assignment with complete request origins
and joint `K,D`. Those clauses do not interpret the Function effect ports as
the challenge/observation domains in that relation. The concrete comparison
law is sufficient after those domains and images are related; it is not an
iff characterization of accepted Function comparisons. Thus it cannot prove
both implications of §8.2 local exactness. The candidate check additionally
needs a source rule for admission and checking of that candidate branch; the
one-candidate fixture only removes general selection alternatives.

This audit found a missing source interpretation/exact rule, not an evidence
storage gap. Keep `W_j` as views over existing carriers. The correct next
dependency is the source annotation/checking bridge and candidate-branch
contract; only then can the two Function local-exactness obligations be
instantiated and the conditional fixed-lane conservation theorem considered.
No new carrier, resolver phase, semantic rule, or implementation follows.
No tests/builds ran.

### Source-call adequacy for the four-port Function cases (2026-10-03)

Sol derived the source call accounting from the selected ordinary-computation
rules. At fixed `ν`, a `Value(a)` receiver performs
`Force(D) >>= (v => B(v))`. The complete call's support is bounded by the
argument support plus the union of body supports over all reachable post-force
`(v,C₁)` outcomes, provided the body bound is uniform over those outcomes.
Thus the source machine supports a coupled argument-plus-body effect bound.

This only explains the first intended inequality conditionally: the missing
four-port elaboration must map input `d` to the argument bound and `[b,d]` to
the combined call bound. The call rule does not define what the negative
effect port denotes, or whether the positive port denotes body-only or full
call effects. A sufficient explanation of the second intended inequality
would interpret both effect-position `never` occurrences as request-free in
their respective source ports; this is one conditional explanation, not a
necessary interpretation of the approved relation. Value-bottom meaning and
`Result(Value(A)) = Comp(empty,A)` do not establish it.

The genuinely missing source definition is the elaboration from the
role-sensitive receiver interface to the four-port Function descriptor,
including port observations, combined-bound presentation, and
contextual effect-position `never`. It must preserve the same assignment,
family constraints, and occurrence incidence, then prove both displayed
comparisons without port-wise general-Type subtyping. Sol's architect review
found the existing relation/weight carriers reusable but insufficient to
derive that elaboration; compiler-referee and spec-auditor review closed two
minor wording findings (quantifying all post-force outcomes; treating the
request-free `never` reading as sufficient only). No implementation or test
work was authorized or run.

Follow-up source check: typed-computation-core §9 already gives a sufficient
joint receiver-comparison law, `D_checked ⊆ D_actual` and
`P_actual(d) ⊆ P_checked(d)` for every checked challenge at the same `ν`.
That law is reusable as the adequacy target, but it does not build the
challenge/observation descriptions from arbitrary effect-row components or
the four Function ports. It explicitly leaves finite construction of the
complete `ExecuteCallable` image and higher-order/store challenge relations
open. The source docs therefore do not yet define a uniform component
interpretation; this is a missing definition, not a counterexample to one.

`Force(D) >>= B` supports only a conditional support upper bound over all
reachable post-force `(v,C₁)` outcomes. It does not prove an unconditional
row union: retained receivers can ignore their carrier, and state-dependent
continuations and handler transitions remain in the complete image. The next
gate is to construct a candidate uniform component interpretation, derive
its joint `D` and `P` views, then test both intended inequalities against
effectful/diverging value-entry arguments, ignored retained arguments,
dependent `K,D`, continuation re-emission, and operation callables whose
native body returns a carrier consumed later by the declared result
interface. Parameter roles, source call scheduling, result forwarding, and
the intended inequalities remain selected; no uniform
component-to-interface interpretation or general four-port Function
comparison rule is selected. A separate port rule requires a source
counterexample to the uniform approach first. Sol's architect investigation,
spec-auditor pre-write review, and compiler-referee delta review found no
basis to add a carrier or promote Oracle behavior. The compiler-referee
review also identified operation callables whose native body returns a
carrier for later consumption by the declared result interface as a useful
additional adequacy case; that case was added to the next-gate record. No
tests/builds ran.

Sol then tested one uniform diagnostic lift:
`Cτ(ρ) = ⋃{Rel_c(ρ) | Γ ⊢ c : Comp(E,τ), for some admitted E}`. It is
meaningful only conditionally: included relations must first share a complete
interface/challenge carrier, with source-local binders capture-avoidably
transported while preserving the same `ν`, assignment fiber, occurrence
incidence, and `K,D`. Even then, it interprets `τ` as a result-type constraint
and does not map it to an effect contribution, typed-request incidence, or
receiver challenge/observation behavior. It therefore fails as an
effect-component interpretation and derives neither target inequality. This
rejects that candidate only; no source counterexample to every uniform
interpretation was found. The exact missing source clause is the mapping of a
literal component into its contribution to an existing complete
receiver/computation view. Spec-auditor pre-write review flagged the common
carrier and fiber-preservation condition; the candidate is explicitly
conditional on them. No carrier, independent judgment, or port rule is added.
Next work remains semantic research; implementation and tests are not
authorized by this result.

Sol's operation-instance follow-up narrows the next source step. `OpInst` and
`OpCompat` characterize a resolved operation declaration and an already
typed request occurrence; ordinary invocation plus source-demanded force
explains how such an occurrence is emitted. They do not build an occurrence
from a row item. The stable-core fixture `act tick 'a` with bracket-arrow
slot `[tick 'a; 'e]` and its expected-signature/`deny_contains` assertions
show accepted surface use, not the row-item-to-interface rule. The fixture is
bare `BracketRow`, not apostrophe-prefixed standalone `EffectRowType`; both
syntax authorities reserve semantic lowering outside their scope. Next derive
the annotation contribution clause for resolved Act-family applications plus
abstract components, then determine whether it is restricted or extends to
all admitted components. The pre-write spec review confirmed this boundary
and cautioned against treating the fixture as an `EffectRowType` instance.
No semicolon-tail meaning or new evidence carrier is authorized.

The first generalization obstacle remains replay admission: same-pivot records
alone do not justify a replay, and optional Records refute unconditional
concrete transitivity. Guard inheritance, row/residual alternatives and
occurrence-specific multi-consumer ownership add further obligations. This
remains a candidate theorem template, not a completed theorem or
implementation authorization. No tests or builds ran.

The bounded compiler-referee review of §8.2 found no blocking or major issue
and two minor premise-qualification ambiguities. The theorem now requires one
shared assignment to satisfy shared root-context constraints and the selected
branch constraints, while keeping unselected alternatives guarded; it no
longer says that the assignment itself admits every source root. Primary
inspection and `git diff --check` closed both wording repairs. The review did
not certify local exactness, Function descriptor elaboration, or replay
admission. No tests or builds ran.

### Conditional annotation coverage review (2026-10-03)

Sol adjudicated the pre-write conformance findings for a possible coverage
interpretation of resolved Act-family items and abstract components. No
source-derived annotation rule is available yet. Existing operation rules
construct a complete `OpInst`, emit a typed request at source-demanded force,
and check an already existing occurrence with `OpCompat`; none maps an
annotation component to that occurrence or selects a coverage meaning.

The narrow candidate is conditional: concrete and abstract component views
must first be jointly defined at one admissible `ν`, with shared predicates,
occurrence incidence, and nonempty fibers retained. A coverage predicate may
then restrict complete observations. Such restriction can remove observations
and whole assignment fibers; it is not request-coordinate `Filterφ`, which
preserves the valuation domain. Neither operation alone validates an
annotation: every accepted fiber must satisfy coverage for all represented
behavior under the admissible challenges. Independently projected component
fibers cannot be unioned into a joint view. Family projection remains weaker
than complete `OpCompat`, including operation-local binders, payload/response,
profile, and handler conditions.

This narrows the research candidate but selects no annotation semantics and
adds no carrier. Existing coupled-interface evidence supplies the joint
assignment, `K,D`, restriction/filter distinction, and complete handler image
once their source premises exist. Existing directed-weight/subtraction
evidence supplies scoped boundary and residual-routing facts but cannot
establish this coverage meaning or prove outward family absence; continuation
re-emission still requires the complete handler image. The next derivation
must establish universal coverage within the complete receiver contract before
using the clause to derive either intended Function inequality. Compiler-
referee/spec-auditor review is required before any later semantic selection;
no user decision is needed merely to continue this conditional derivation.
No tests or builds ran.

### Conditional support projection from receiver comparison (2026-10-03)

Sol derived a source-independent corollary of typed-computation-core §9. Fix
one admissible assignment `ν`, one checked challenge `d ∈ D_checked(ν)`, a
common complete-observation carrier, and the same supplied support projection
`Q` at the same source-defined boundary on both sides. Under
`P_actual,ν(d) ⊆ P_checked,ν(d)`, each actual observation is itself a checked
observation, so:

```text
∀O ∈ P_actual,ν(d):
  Q(O) ⊆ ⋃ { Q(O′) | O′ ∈ P_checked,ν(d) }.
```

If the supplied bound additionally satisfies
`∀O′ ∈ P_checked,ν(d): Q(O′) ⊆ Allowedν(h)`, for the same boundary/context
`h`, then every actual observation at that checked challenge is covered by
`Allowedν(h)`. Actual execution coverage also assumes the actual behavior is
represented in `P_actual`. The accompanying
`D_checked(ν) ⊆ D_actual(ν)` premise makes checked challenges admissible; it
does not extend this conclusion to actual-only challenges.

The independent spec-auditor review found no blocking or major defect and
three minor qualification issues. The statement now quantifies only over
`d ∈ D_checked`, fixes the same complete observation boundary and supplied
allowance, and treats empty challenge/observation cases as vacuous. Those
vacuities do not prove nonempty typed-row fibers; any `RowSub` conclusion still
needs its separate nonempty-fiber premises. The review confirmed that this is
only a consequence of supplied `D/P/Q/Allowed` data. It constructs none of
them from annotations, defines no annotation acceptance rule, and establishes
no handler subtraction or general Function comparison. `Filterφ` is not used,
and deleting uncovered behavior cannot establish coverage of the original
actual relation. No tests or builds ran.

### Restricted component-support candidate (2026-10-03)

Sol derived a conditional support obligation for a proposed annotation view
containing a resolved concrete family application and an abstract component.
Under the existing complete §9 comparison, suppose component denotations
independently supply `Allowed(ν,h,O,q)` inside the same jointly satisfiable
fiber and retained `K,D`. Require that predicate for every request in every
checked observation at each `h ∈ D_checked(ν)`. Since
`P_actual(ν,h) ⊆ P_checked(ν,h)`, the same support condition holds for actual
observations at those checked challenges. The domain premise
`D_checked(ν) ⊆ D_actual(ν)` supplies no condition for actual-only challenges.

This remains only a necessary support projection inside complete comparison.
The family predicate ranges over already established typed requests and the
full family tuple; it constructs no request or operation instance. Abstract
views, the source family relation, `Allowed`, and the fixed `Q` boundary must
be supplied independently and jointly under the same `ν,K,D`. Complete
`D/P` inclusion and `OpCompat`/handler obligations remain separate. The rule
uses no `Filterφ`, observation deletion, `L - J`, accumulation law, or concrete
success composition, and derives neither intended Function inequality.

The initial independent spec and semantic audits accepted this only as a
conditional hypothesis and identified scope/tautology risks. Sol repaired the
quantifier and independent-denotation premises; a fresh compiler-referee delta
review then found no remaining issue in the written corollary. The review was
limited to that subsection and its direct source dependencies. It did not
review or select a row-component meaning. Still missing are the source rules
that construct component views and `D/P/Allowed`, negative-port challenge
admission, the meaning of `d` and `[b,d]`, and both effect-position `never`
contributions. No compiler changes, builds, or tests ran.

### Successor source-to-solver ownership check (2026-10-03)

I checked the current Yulang3 crate boundary after deriving the conditional
receiver-comparison corollary. `yu-syntax` exposes `EffectRowType` and
`BracketRow` as direct-item CSTs, with syntax authority explicitly excluding
row interpretation and lowering. `yu-hir` is still an HIR-adjacent operator
association/module-name-resolution slice: `HirExpr::Value` retains syntax
kind, range, and children, and the crate has no `BracketRow`, `EffectRowType`,
or effect-row lowering symbols. `yu-types`' indexed Function node contains
value argument/result children only. Separately, `yu-solver::Term` can build
four-port Function nodes and validates the effect ports as `ComponentKind::Effect`
with negative argument and positive result polarity.

This is an implementation-boundary map, not semantic authority. It confirms
that the component-to-complete-interface rule has no current HIR owner or
source-lowering implementation, while solver-side four-port and effect-row
infrastructure already exists as internal machinery. It does not show that
the solver representation has the required annotation denotation, same-`ν`
fiber preservation, component classification, or universal coverage rule.
No code changed and no tests/builds ran.

### Intended Function-case necessary conditions (2026-10-03)

Before extending effect resolution, I reread the directed-stack-weight and
effect-subtraction specifications and the Astra-era interpretation. Their
existing scoped identities, ordered push/pop history, family budgets, row
split/residual evidence, and invariant payload constraints are candidate
evidence for the user's partial reverse-addition description. “Reverse
addition” does not itself require new regional, attachment, or provenance
machinery. The draft now marks the genuinely open work as source component
classification/correlation, canonical-flat covariant transport,
polarity-specific descriptor elaboration, joint `[b,d]` and shared-`e`
resolution, and a source proof that existing evidence licenses each reversal.

Sol's derivation of necessary conditions from both intended Function cases was
recorded with the explicit restriction that it uses the sufficient complete
comparison law in §9; it is not a claim that every adaptation follows that
proof route. It excludes request-free-only admission for the actual negative
endpoint only when an admitted checked challenge has a nonempty typed request
observation. It gives a conditional support upper bound for `Force(D) >>= B`,
not an exact union law, and requires linked ports to retain one joint `ν,K,D`
fiber. A fresh bounded `compiler_referee` review found no blocking, major, or
minor findings. This adds no component denotation, `never` interpretation,
normalization, reversal rule, or complete inequality proof. `git diff --check`
passed; no tests, builds, or measurements ran. Measurement budget consumed: 0.

### Conditional resolved-family coverage candidate (2026-10-03)

I separated the source order from the missing annotation bridge. Existing rules
resolve an Act operation into `OpInst`, execute it only under source demand,
and retain the resulting complete request. They do not derive request events
from a row annotation. Operation-instance §2 also shows why family support
cannot stand for a whole request: the family projection forgets operation-
local binders and may merge requests whose payload, response, or continuation
interfaces differ.

The design draft now records one explicitly unselected, support-only candidate
for a resolved `F(α)` item: it checks family identity and the source-prescribed
invariant family arguments on requests already in the complete view. Full
operation identity, local witnesses, payload/response, continuation and
shared `K,D` remain there. The abstract-component side and component
combination are left as open denotations; §9's inclusion corollary applies
only if they are independently supplied. This candidate introduces no
request constructor or parallel attachment/provenance machinery and does not
derive either Function inequality.

A bounded M3 compiler-referee review found one minor ownership ambiguity about
which rule retains the live continuation; I repaired it by distinguishing
`OpInst` data from the continuation constructed by execution. Primary
inspection and `git diff --check` close that wording finding. No tests, builds,
or measurements ran. The source annotation meaning, candidate selection,
abstract denotation, component combination, fragment/uniform scope, and full
Function resolver remain open; implementation authority remains none.

A later conditional derivation of the singleton `TypedRow` projection received
a compiler-referee delta review. It found that equality of the occurrence's
family tuple did not imply that the candidate row fiber was inhabited: the
coupled-interface definition also requires the assigned tuple to lie in
`ArgDen_A(oτ,ν)`. I added that explicit premise and `J_{ {τ} }(ν) ≠ ∅`;
the repaired singleton calculation passed the bounded delta review with no
residual finding. This proof remains conditional on the missing annotation-to-
occurrence source clause. `git diff --check` passed; no tests, builds, or
measurements ran.

The singleton support calculation was then composed with the existing
coupled-interface draft's candidate Function clause. Under that candidate,
every immediate request in every complete call observation must belong to
`TypedRow(E,ν)`. For the stipulated singleton occurrence and nonempty
argument fiber, this reduces to family-point membership in the resolved
`F(α)` point. A bounded compiler-referee review found no issue in this
conditional specialization. It neither selects the candidate Function
contract nor supplies the annotation-to-occurrence mapping. The next safe
derivation is the abstract component view and its joint combination with the
resolved family point, still without implementation authority.

Before adding any effect-resolution structure, I cross-checked the abstract
component candidate against the frozen directed-weight/effect-subtraction
rules and the Astra-era interpretation. The old calculus already accounts for
scoped subtraction identities, ordered push/pop history, family budgets,
row splitting, residual transport, and invariant payload checks; the coupled
interface already carries source ownership/incidence, shared assignments,
and relational dependencies. The proposed support-union equation therefore
cannot follow from separate component projections: a major review finding
required a nonempty joint fiber and a source-derived occurrence-union rule.
The repaired candidate now requires both and keeps both contributions in
that joint `Rel_C` context. Its bounded delta review closed without residual
findings. No new regional, attachment, provenance, or subtraction structure
is introduced. The genuinely open bridge is mapping source Function row
components into those existing carriers and proving that their existing
evidence licenses each partial reversal. No code changed; `git diff --check`
passed, with no tests, builds, or measurements run.

### Source owner for Function effect components

A bounded Sol architecture derivation inspected the current source-machine,
typed-computation, complete-interface and operation-instance clauses. Those
clauses determine invocation, designated force, handler execution, complete
request retention, and the conditional comparison target
`D_checked ⊆ D_actual` plus `P_actual(d) ⊆ P_checked(d)`. They do not map an
abstract effect-row component to a contribution in that complete relation.
`TypedRow` starts only after occurrences and their source-owned family
arguments are supplied; it does not create them. The missing owner is source
annotation/typed-interface elaboration. Treating `α` as “the complete view it
denotes” would only restate this missing rule.

The existing `Rel_C` fiber is a permissible transport candidate: a source
rule could identify a typed port there while retaining one `ν`, `K,D`, request
incidence and continuation. The inspected clauses do not prove that this map
covers all abstract components or that several component contributions
combine by occurrence union. The coupled row-union law still requires a
nonempty joint fiber and a source constructor with that support coordinate.
The intended inequalities therefore remain selected targets, with no derived
port-wise rule: the first needs effectful challenge admission and a combined
argument/body observation bound; the second needs both `e` ports in the same
assignment/fiber. Diverging prefixes, ignored retained carriers, raw
continuation re-emission, and operation result-consumer execution remain in
the complete source image. No `never` effect interpretation follows. The
exact unresolved decision is the source component contribution and its scope;
no new carrier or implementation follows from this audit.

### Frozen Oracle annotation-lowering characterization (Luna)

I checked the frozen `main` annotation builder and constraint lowering only as
historical evidence. Its `AnnEffectRow` has separate `items` and optional
`tail`; the parser-side builder treats pre-semicolon entries as items,
accepts only a type variable after the semicolon, and normalizes a lone
unseparated type variable into the tail slot. Historical positive lowering
constructs `Pos::Row(items ++ tail)`, while negative lowering constructs
`Neg::Row(items, tail-or-Top)`. The old subtraction view separately ignores
type variables when collecting concrete head keys; nonvariable row atoms must
resolve to constructor paths, then become a set or set-of-sets filter.

Those details explain how the frozen implementation operationalizes its
historical row syntax and head subtraction. They do not establish successor
component identity, source occurrence ownership, same-fiber combination, or
reverse-addition semantics. In particular, the old `items; tail` split and
constructor-head filter are not evidence that a successor abstract component
denotes a tail variable or that concrete atoms contribute by the same rule.
This characterization adds no successor policy or carrier. Read-only source
inspection; no tests/builds or edits to frozen `main`.

### Independent Milestone-3 Record residual lemma

While the source component decision remains open, I advanced an independent
pure structural residual slice. For one fixed equality-quotient class `X`
bounded above and below by finite mandatory Records with unique labels and
identity-only atomic fields, the draft now gives the exact whole structural
fiber. If lower bounds exist, `X`'s labels range from the union of required
upper labels to the common lower labels whose atomic values agree; selected
fields retain those common atoms, and required upper atoms must agree with
them. With no lower bounds, every finite extension of the required upper
labels is admitted, with arbitrary regular field assignments on extra
labels. With no bounds, the whole regular domain remains. This captures
`X <= {}` without choosing only the empty Record and shows that conflicting
lower-only fields may be omitted.

The derivation keeps the structural fiber separate from permissions, immutable
guards, and `Phi/K,D`, which are conjoined on the same witness. It does not
claim full residual satisfiability or authorize source rejection. An
independent bounded M3 `compiler_referee` review found no blocking, major, or
minor findings on necessity/sufficiency, arbitrary extensions, guard and
permission distinctions, and the stated edge cases. The draft, index, task
navigation and this progress record were synchronized. `git diff --check`
passed; no tests, builds, or measurements ran. General residual acceptance,
projection with feedback, source-generation closure and lifecycle remain open.

### Uniform component interpretation derivation (Sol)

The current task directs uniform interpretation as the first research route;
the restricted-fragment and Function-only routes are not primary alternatives
unless later evidence defeats the uniform route. A follow-up Sol derivation
therefore tried the uniform mapping first. The strongest no-new-carrier schema
is a proof view of the existing complete fiber at one typed effect path,
assignment `ν`, and shared `K,D`. It must preserve literal component identity,
lexical ownership, full challenges and observations, and combine components
before projecting support. This schema is not yet a denotation: existing
source clauses do not map general `TypeExpression` components to it.

For a resolved family component `F(ᾱ)`, `FamilyAllowed` is only a conditional
support projection after an owned occurrence and nonempty argument fiber have
been supplied. For an abstract component, the same-fiber `View_α` is likewise
conditional on a source port mapping and a joint nonempty fiber. `TypedRow`
presupposes these occurrences; neither it nor `Rel_C` creates their mapping.
Reading components through value inhabitants would require a new embedding
from value denotations to request/interface descriptions, which current rules
do not supply.

One necessary consequence is fixed by the intended first inequality: a
request-free incoming interpretation of the negative `never` port would
exclude an admitted effectful challenge. Conversely, value-bottom does not
exclude request prefixes from a computation that diverges or returns no value.
`Any` likewise cannot be read as unrestricted effects merely because it admits
all values; `EffectRow([])` remains a distinct pure computation row. Mixed
components must retain one admissible `Rel_C` fiber. Support union follows
only from a source combination rule and is not a definition of complete
combination.

The remaining semantic choice is whether a uniform component denotes a bound
on the complete challenge/observation view at its port, or an additional
contribution composed by the source invocation/handler rules. Existing source
rules do not select between them. The latter is a possible direction only; its
source boundary and combination law are not yet defined. No carrier, solver
phase, or implementation change is justified. A user decision is pending
before writing either rule; preserve the current uniform-first research order.

### Role-first Function elaboration clarification (2026-10-03)

The user then clarified that source introduction and expected context choose
the Function receiver role before Function interface and effect-port
elaboration:

```text
function literal + expected context
  -> receiver role (pure / handler)
  -> Function interface elaboration
  -> effect-port interpretation
```

The intended cases are an unannotated ordinary function literal inferred as
pure, an explicitly annotated Function boundary acting as a handler boundary,
and a callback-position literal receiving handler role from expected context.
This is not charter §21's separate `Value`/`Computation` parameter-entry
choice. No special effect meaning is assigned to `never`; value bottom, empty
effect row, and polarized internal bottom/top remain distinct. This user
clarification supersedes the preceding paragraph's immediate binary choice and
uniform-first research order; that component question may remain downstream if
role-specific elaboration still requires it.

Sol's bounded source audit found that existing clauses establish every
function's computation-receiving invocation, inert whole-argument reification,
parameter entry/retention, result forwarding, and the conditional complete
interface path through `J_arg`, `J_body`, `J_call`, typed `Flow`/`Observe`,
incidence, and `Rel_C`. They do not yet derive the requested literal role
selection, annotation-to-boundary elaboration, or expected-context propagation
for callback literals. Therefore source Function annotation/context
elaboration now precedes any general component-to-interface mapping. Existing
`Rel_C`, shared `ν`, `K,D`, occurrence/incidence and subtraction evidence stay
the candidate proof substrate; no new carrier or provenance follows absent a
specific demonstrated representational gap.

For `Fun(a, never, b, c) <: Fun(a, d, [b,d], c)`, `Force(D) >>= B` gives a
conditional operational motivation: a request exposed by argument entry
remains in the complete invocation, and the body runs in each reached
post-force state. This can motivate joint accounting by `d` and `b`, but does
not prove the subtype until elaboration derives actual/checked domains, typed
paths, port views, and `[b,d]` under one fiber and assignment. The gate must
not decompose four ports as independent general-Type inequalities. Existing
Astra-era/directed-weight subtraction interpretation is reusable only as
already witnessed partial subtraction; it must not be duplicated as new
reverse-addition evidence.

Updated: design §7, task immediate gate, and design index. No implementation,
tests, builds, measurements or Oracle inspection were done. Literal
elaboration and the intended lifting derivation remain open.

### Role-directed elaboration closure audit (2026-10-03)

I reviewed the role-first case split against charter §§16–21, typed-core
§§6–9, ordinary-computation §§3–4, and the coupled-interface relation. A
bounded Sol architect derivation established that the user-selected cases
remain distinct from §21 parameter entry and that the previous
component-first/binary-choice question is superseded. It found no existing
clause that constructs pure/handler Function descriptions from the literal,
annotation or expected callback context.

The then-candidate immediate theorem combined role-directed Function
introduction with complete contextual checking. A M3 compiler-referee review
found the following blockers for that **full comparison theorem**:

1. **BLOCKING:** actual/checked complete challenge domains and `P` relations
   are not constructed. They must range over source-admissible contexts,
   histories, stores, responses and future callback uses, independently of
   observed calls and comparison success; neither vacuity nor arbitrary
   unconstructible configurations can define them.
2. **Major:** code erasure alone does not preserve decorated behavior when
   callback profiles differ. Core §7 erases proof labels while retaining
   original profiles and paths; it does not prove equivalence for different
   callback annotations.
3. **Major:** receiver role does not select §21 parameter entry. `Force(D) >>= B`
   applies only to `Value(A)` entry; retained computation entry follows its
   actual body consumers, including the unused and explicitly forwarded cases.
4. **Major:** support union is not full Function inclusion. The joint image
   includes handlers, raw resumption, designated result consumption, live
   state, latent return paths and future callbacks. `[b,d]` remains unproved.

The spec-auditor review found no conflict with selected rules and confirmed
that role alone creates neither a capture grant nor a changed existing
callable entry. Both reviewers found no concrete insufficiency in `Rel_C`,
shared `ν`, `K,D`, `Flow`, `Observe`, incidence or existing subtraction. The
defect is missing source derivation/domain construction, not storage. The
design §8 and `tasks/current.md` record these as open closure obligations;
the intended lift and implementation gate remain open. The later user
clarification split the gate: bounded literal-role/interface elaboration and
callback invocation accounting come first; these domain/decorated-behavior
findings remain prerequisites only for the later complete inequality proof.

No compiler code, Oracle, tests, builds or measurements were inspected. The
working change is records only; `git diff --check` is the focused integrity
check. The bounded literal-role derivation below is now next; the
source-admissible challenge/interface relation and decorated-behavior
transport remain later prerequisites before deriving the complete inequality.

### Context-domain follow-up (2026-10-03)

Sol's follow-up audit found that the coupled-interface draft's all-context
`CallCfg` and typed-core §9's `D_i` are the correct semantic schemas, but they
do not discharge the domain-construction blocker. Context typing, the relation
for other environments/stores, and evaluation closure remain open. Typed
holes avoid one direct self-membership circle but do not establish
well-formedness of aliased environments and shared store/lineage. The earlier
value-hole non-vacuity argument also does not cover whole-argument reification.

Counterexample to using the old non-vacuity lemma unchanged: a value-entry
`f x = ()` called with a pure-diverging carrier `D : Comp([],Unit)` never
reaches its body; `Delay(Return Unit)` does. Both arguments have the same
result endpoint and empty support. The first is still an admissible carrier
challenge because receiver receipt precedes force. A retained receiver can
ignore `D`, so this distinction is the independent §21 entry mode, not
receiver role or an effect-row special case.

For the later complete-comparison gate, the smallest missing proof input is
decorated source evaluation-context typing with callable and argument-code /
carrier holes, a well-formed environment/store at shared `ν`, source
lineage/profiles/`K,D`, and admissible
future inputs, responses and raw resumptions. The resulting later theorem
is source-context closure and invocation coverage: role/entry introduction,
non-vacuous receipt before force, context composition and execution closure,
then future-use/resumption preservation for existing `Flow`, `Observe`,
incidence and expiry. Existing-value checking constructs actual/checked
domains before comparison and retains actual entry/decorations. This can first
be extensional and infinite; effective finite representation and principal
comparison remain separate. No concrete carrier gap was found.

Updated design §8 and `tasks/current.md`. No tests/builds/Oracle/compiler-code
inspection. Focused verification: `git diff --check`. This remains a draft
proof obligation, with no implementation authorization.

### Rigid-hole contextual schema delta (2026-10-03)

A second bounded Sol derivation proposed proof-only rigid holes typed against
the checked interface, with tested values kept out of the hole context's
semantic environment. Actual callable/carrier and joint source-state evidence
are separate premises. This avoids direct circularity and does not justify
checked-type preservation after plugging; actual preservation is usable only
after checked-domain inclusion is proved.

Conditional immediate-application non-vacuity now has a precise trace: after
callee evaluation, the whole argument is inertly reified, the callable enters
its **actual** receiver, and receipt occurs before force. A pure divergence in
the carrier therefore prevents body execution but cannot remove the invocation
challenge. This requires a jointly admissible source state and proves neither
domain inclusion nor nonemptiness of every type fiber.

The compiler-referee delta review accepted the schema and trace conditionally,
but retained BLOCKING `EnvStore`/`JointWF` construction: an actual closure can
capture `ℓ`, whose contents alias the closure or a callback capturing it, while
another context variable aliases `ℓ`. Checking that store by the checked
Function denotation reintroduces the comparison; excluding it loses legitimate
states. A major context-closure obligation also remains for stored/copy aliases,
later calls, handler exit, mutation and raw-resumption re-entry. Any actual
construction must define a guarded/well-founded joint account, preserve shared
location identity, and avoid independently choosing store witnesses. No new
carrier is justified by the report.

Updated design §8, `tasks/current.md`, and the design index. `git diff --check`
is the only check; no tests/builds/code/Oracle inspection. Immediate theorem
remains open and extensional; finite presentation/principality are later gates.

### Conditional open-graph route (2026-10-03)

A bounded Astra theorem audit, then an independent Sol architect audit,
examined whether the rigid-hole alias gap can use existing graph/evidence
structures. The audits support recording a conditional proof candidate, not a
closed theorem or a carrier redesign.

The candidate keeps `H:T_checked` as a proof-only hole in open source
derivations, builds one joint graph retaining context/capture/carrier location
identity, and uses a monotone positive structural relation only for code,
constructor and decoration checks. Containing closures/cells stay open-derived;
the actual callable never acquires checked semantic membership from the hole
assumption. Plugging is identity-preserving graph substitution. This can avoid
the direct recursive-membership circle if no downstream premise asks for
closed checked membership of a containing value.

That graph argument does not establish semantic `EnvStore`/`JointWF` validity.
The genuinely new obligation is an open decorated source construction and its
substitution/history theorem: preserve hole dependence and shared locations
through mutation, alias reads/calls, capture, returns, requests/responses,
handler exit and raw resumption, with actual role/entry, original profiles,
shared `ν,K,D`, event-specific `Flow`/`Observe`/incidence and expiry. A static
“contains H” marker is insufficient because mutation changes aliases. A
semantic greatest fixed point is also unsupported without a monotone positive
operator; Function inputs are negative and mutable stores couple reads and
writes.

The Sol delta audit surfaced a domain boundary to preserve: the coupled
contextual contract permits semantic free-variable environments, including
ones not constructible by a closed program. Whether open derivations with
admissible imports generate that domain is unresolved; do not narrow it to
closed-program-reachable heaps. Existing graph machinery transports supplied
relations but supplies neither source generation nor finite effective
comparison/principality. No concrete carrier insufficiency was found.

Next: define admissible initial open states/imports, prove rigid-hole
substitution and transition closure over the intended context domain, then
construct the actual/checked complete domains and observations. Keep the
role-first order: only then derive the pure-to-handler lift and joint `[b,d]`
effect interpretation from source execution such as `Force(D) >>= B`. No
implementation, solver carrier, Oracle inspection, test, build or measurement
was authorized or performed. This remains a draft research route with the
existing BLOCKING domain and major closure findings open.

### Step-indexed open-world audit (2026-10-03)

A bounded compiler-referee audit found proof-only step indexing to be a
plausible guarded definition, already anticipated as an open option in the
coupled-interface draft. It changes neither concrete inequality nor solver
carriers. The candidate approximants must hold one actual callable, `ν`,
source environment and identity-preserving heap graph fixed. A recursive
reference to the rigid hole is usable only at a smaller index after a concrete
machine step; index exhaustion cannot establish membership. The same index
must decrease for re-entry through aliases and alternate receiver contexts.

The review retained one BLOCKING and three major proof gaps:

1. Define the exact initial context/import domain independently of the
comparison. Closed-program reachability narrows the selected contextual
domain; arbitrary graph imports may enlarge it. Ordinary imports must have
query-independent validity, while hole-dependent values use the guarded
obligation. Do not use independent `heap_n` witnesses at each index.
2. Prove strict decrease and downward closure with all lower-index contexts,
arguments, responses and resumptions. A shared-cell callback that recursively
calls the tested function `N` times and then emits a forbidden request must
be rejected at some finite index.
3. Prove live-world transition laws for allocation, read/write, handler exit
and raw resumption. A saved heap snapshot can miss mutation before resume;
expired handler authority cannot be restored. Preserve `ν,K,D`, original
profiles, `Flow`/`Observe`, incidence and activation identity.
4. Prove finite-prefix adequacy for the whole complete-interface relation:
challenge admission, typed receipt, full observations, returned latent
interfaces, future calls and raw resumption. A support-only check is weaker.

No counterexample to the conditional proof route or carrier insufficiency was
found, but these premises remain unresolved and no finite principal
presentation follows. Next: define fixed-heap indexed imports/worlds; prove
exact domain preservation and guarded substitution/transition closure; prove
all complete-interface failures have finite witnesses; then construct both
interface inclusions. Continue to derive the intended pure-to-handler lift
only after this role-first gate. No code, tests, builds, Oracle inspection,
measurements or solver changes were performed. `git diff --check` is the
focused integrity check.

### Source-state realization boundary (2026-10-03)

A read-only repository map and a bounded `spec_auditor` review refined the
heap-oriented step-index candidate against the approved source/architecture
rules. Yulang does have mutable references and reassignment: the stable-core
`example_refs` fixture reads with `$x` and writes with `&x = value`; the
`ref_update_local_buffer_public` fixture captures `$buffer` in `get` and
`update_effect` callbacks. These establish user-visible mutation and captured
state access, not primitive mutable heap cells.

The authoritative `docs/yulang3-architecture.md` §6.9 fixes local mutable
bindings as compiler-generated `StateSlotId`s. The identity is a compile-time
origin, explicitly not a runtime address, activation cell or multi-shot branch
identity. §8.3 says `&a = value` lowers to pure continuation restart. The
frozen `RefSet` characterization forwards through the `ref_update.update`
effect and handler; it does not make `RefSet` a primitive heap write. General
first-class refs such as `std::io::file::text` remain a distinct scope and
must not be excluded from Function contexts solely by the local StateSlot
decision.

The recursive shared-cell and write-before-resume examples in the current
Function gate therefore remain **abstract-machine schemas**, not established
typed Yulang executions. Keep them as stress cases only after deriving their
source State/reference realization. The exact source-state world for an
indexed contextual proof must come from the source transition relation:
lexical reference transport, visible State-slot ownership, effect-mediated
updates, active handler identity and raw continuation re-entry. Do not posit
primitive allocation/write steps or treat static `StateSlotId` as runtime
cell identity.

This audit does not close the environment/context-domain blocker. Next derive
the state represented by admissible free-variable imports and connect both
local State and general-reference operations to that state; then define the
step-indexed relation and prove transition/domain adequacy. The source
refinement keeps the role-first Function order and leaves all first-class refs
within the contextual challenge domain when admitted by their interface. No
compiler changes or tests/builds were made; `git diff --check` remains the
focused integrity check.

### Local StateSlot and general-ref proof lanes (2026-10-03)

A bounded Sol architect derivation split the source-state bridge into two
proof lanes while retaining the single `Rel_C` substrate. This is a schema,
not an approved additional relation or carrier.

| Source path | Existing authority/evidence | Needed next derivation |
|---|---|---|
| Visible local StateSlot | `HirModule`-owned static `StateSlotId`; `ConstraintStore` slot/read/write occurrences; shared payload and `StateEffect`; visible aliases/captures/escapes preserve origin; lexical discharge | Source configurations at declaration/read/update; continuation restart with replacement value; captures and resumption; distinct runtime activations for one static slot |
| General first-class ref | `ref_update_local_buffer_public` uses a `ref` with captured `get` and `update_effect`, then calls `update`/`get` | Callback and update request/response behavior; opaque reference import/transport; alias, capture/escape and resumed access |

The open challenge remains a checked role-directed context with rigid
callable/argument holes, independent semantic imports, hole-dependent open
captures, and one admissible source configuration/history under shared
`ν,K,D`, occurrence and activation evidence. It reaches actual receipt before
force. Receiver role and §21 entry stay independent; existing values keep
their actual role, entry and decorations.

The existing `Rel_C`, occurrence/incidence, `Flow`/`Observe`, and
activation/continuation evidence are candidate carriers, with source closure
unproved. Current fixtures establish local state update, captured callbacks,
and recursion; they do not realize recursive storage of the tested callable
or a shared-reference update across a multi-shot branch. Thus keep generic
shared-cell examples conditional. Preserve first-class refs whenever the
interface admits them; do not identify static `StateSlotId` with runtime
identity. No code, tests, builds, Oracle inspection or measurements occurred.

#### Visible State source-step audit (2026-10-03)

A bounded read-only implementation/source audit confirms the authority gap.
Architecture §6.9 fixes declaration-origin identity, shared payload/effect
components, read/write occurrence ownership, lexical discharge and
escaping-closure retention. Architecture §8.3 selects pure continuation
restart for `&a = value`. The typed-source-owner and typed-boundary drafts can
preserve an already supplied store/view, source origin, `K,D,ν`, and live
resumption state. These facts support identity-preserving transport once the
source transition is given.

They do not define executable source equations for declaration, read, update
response/restart, or re-entry after capture/resumption. This workspace has no
separate successor State semantics specification, and current
`crates/yu-hir/src/module.rs:426` exposes only `Lambda`, `Integer`, `Name`, and
`Error` resolved expressions; no StateSlot/StateEffect Rust symbols exist under
`crates`. The architecture contract is not implementation evidence.

The smallest source lemma is local State-step preservation for one supplied
typed visible-slot derivation: establish declaration/read/update transitions
using continuation restart rather than primitive heap writes; preserve static
`StateSlotId` while distinguishing dynamic activations; then show visible
alias/capture, lexical exit, later invocation and raw resumption preserve the
same typed views and shared `Rel_C`/`K,D,ν`, with expired handler authority
absent. This supplies a source-state premise to the `EnvStore`/`JointWF` proof,
not source-wide context generation, general first-class refs, multi-shot
shared-state adequacy, or the Function inequality.

### Role-first immediate-gate refinement (2026-10-03)

The user's clarification changes the order within the Function gate. First
derive a bounded source-elaboration path for ordinary unannotated literals,
explicitly Function-annotated literals, and callback-position literals. In
each case derive receiver role, keep it independent of §21 parameter-entry
role, and only then elaborate the Function interface and its effect-port
views. The stable-core `ref_update_local_buffer_public` callback plus its
public signature is a concrete expected-context anchor; it does not establish
the missing library implementation or complete callback transition.

The next derivation target is the pure-value-function to
handler-capable-callback lift through source application/elimination. For a
value-entry callback, `Force(D) >>= B` motivates joint accounting for
argument computation `d` and body behavior `b` at reachable post-force states
under one existing `Rel_C`/`ν` fiber. This remains a derivation target, not a
four-port structural rule, an interpretation of effect-position `never`, or
an unconditional row-union law. The broad complete-domain `EnvStore`/`JointWF`
construction, state/alias closure and finite-witness adequacy remain later
gates rather than prerequisites for deriving the three introduction clauses.

I reread the frozen effect-subtraction specification and Astra-era
interpretation before this reordering. Existing ordered push/pop histories,
scoped subtraction identities, family budgets, row split/residual transport
and invariant payload checks substantially overlap the proposed “reverse
addition” vocabulary. No missing source fact has yet been demonstrated, so
this clarification adds no solver carrier, attachment ledger or provenance
structure. The exact remaining bridge is to show how the role-elaborated
source invocation and its concrete contributions are already witnessed by
those carriers; only a concrete counterexample to that representability can
motivate an additional proof object.

No code or tests changed. No tests, builds, Oracle inspection or measurements
were run in this refinement; measurement budget consumed: 0.

### Bounded literal-role derivation (2026-10-03)

I cross-checked the new immediate subgate against core §6, charter §21, the
callback fixture, and its public signature. The source core already
constructs a lambda as `Value(Fun(P, Result(I_b)))`; §21 determines `P` and
its `Value` versus `Computation` entry before body synthesis. It does not
select the separate pure/handler receiver role. A bounded crosswalk now
records the three user-directed introduction/check cases and keeps a fourth
case—checking an already-constructed value—separate, preserving its actual
entry and decorated behavior.

The fixture signature
`ref('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()` and source call
`r.update (\old -> old + "!")` give a concrete callback-position literal.
Its ordinary `old` parameter selects `Value` entry under §21, so the existing
call semantics receives the whole argument inertly, forces it once, rebinds,
and then runs the body (`Force(D) >>= B`). This grounds joint invocation
accounting for argument and reachable body behavior under one `Rel_C`/`ν`
fiber. It only supports the already conditional support bound; it does not
derive exact `[b,d]`, a subtraction step, or a complete Function inequality.
Retained `Computation` entry remains separate and does not force unless the
body explicitly consumes it.

This crosswalk sharpens the pending source gap: how an already pure-role
Function value is checked/adapted at a handler-capable callback interface
while retaining actual behavior. That interface adaptation, actual/checked
challenge domains, and effect-port views need source derivations. The
displayed `never` has no effect interpretation here. No specific fact was
found absent from `Rel_C`, `K,D`, occurrence/incidence, `Flow`/`Observe`, or
directed-weight/subtraction evidence, so no new carrier or provenance object
is proposed. The result is a proof-only refinement, not implementation
authority.

No code changed. No tests, builds, Oracle inspection or measurements were
run; `git diff --check` is the focused integrity check and measurement budget
consumed remains zero.

### Conditional callback-slot view derivation (2026-10-03)

I traced the pure-value-to-handler-callback case against the existing typed
boundary, coupled-interface and source call-scheduling records. These provide
a plausible no-new-carrier route with three independent facts: the closure
keeps its introduction-selected receiver role; the expected callback slot
supplies a handler-capable `CallView` on uses through that slot; and the actual
callable keeps its §21 `Value` or `Computation` entry.

Conditionally, for identity argument/result transport and a `Value`-entry
callable, the source order is callee/callback acquisition, inert construction
of the whole argument carrier, actual receipt, then `Force(D) >>= B`. The
callback-slot `CallView` surrounds that invocation and supplies the
observation port for requests from both the forced argument and body.
`Flow`/`Observe`, occurrence/incidence and `K,D` can retain their distinct
correlations under the same `ν`. If `d` and `b` bound argument and all reached
post-force body behavior, respectively, their support union is a conditional
upper bound for this single state-threaded invocation. It is not exact row
addition or independent port subtyping. A retained computation entry does not
force unless the body explicitly consumes its carrier.

This is an explanatory source route, not yet a proved source-elaboration
lemma: the missing premise is that the expected callback context creates the
handler-capable slot `CallView` for a pre-existing pure-role value, with the
correct typed observation profile and actual/checked challenge inclusion.
Non-identity Function adaptation also remains open; the fixed adapter
realization cannot justify forcing before actual receipt. Thus this advances
the source explanation for joint `d`/`b` observations but does not prove the
intended `Fun(a, never, b, c) <: Fun(a, d, [b,d], c)` relation or assign any
effect meaning to `never`.

The existing `Rel_C`, `Flow`/`Observe`, occurrence/incidence, shared `K,D`,
and directed-weight/subtraction evidence still show no concrete missing
fact, so I added no solver/evidence carrier. This derivation is primary-authored
and remains unreviewed; it is research only with no implementation authority.
No code, tests, builds, Oracle inspection or measurements were run;
`git diff --check` is the focused record check.

### Existing CallView evidence crosswalk (2026-10-03)

A focused reread of the typed-boundary evidence definitions sharpened the
conditional bridge. Existing records already distinguish callback boundary
identity `b=(receiver, slot, signature profile, endpoints)`, received typed
views and `Receive`, value-path transport `Flow`, event observation `Observe`,
profile/dependency transport `χ,K,D`, typed `Path`, and current activation
incidence `Inc_C`. The complete source `CallView` encloses argument conversion,
call, result conversion and demanded force. These structures jointly provide
the evidence vocabulary needed to preserve an actual pure-role closure under
an expected handler-capable callback slot; they do not require a parallel
attachment/provenance carrier.

For identity argument/result transport and a value-entry callable, the
conditional event path is: expected slot supplies its source-decorated view;
callee is obtained; the argument is inertly reified; actual receipt occurs;
`Force(D) >>= B` runs inside the call; and each request receives its
`Observe` witness at the currently executing `CallView` ports. Its `Flow` /
`Path` reaches the source contract profile, while `Inc_C` separately checks
that the relevant receiver/handler is still active and eligible. `K,D`
incidence remains on each event at the same `ν`.

The exact missing lemma is now the **source-generated slot-profile
projection**: derive from expected callback context that the slot creates this
boundary/profile; derive the typed receipt and identity value path for the
actual callback; and show that argument-force and body events both reach the
intended complete invocation effect port under one `Rel_C` fiber. A flattened
row containing both family names is not a proof of these path witnesses. This
remains conditional and unreviewed; non-identity conversions and the full
actual/checked challenge inclusion remain open. No solver/evidence carrier,
code, or tests were added. `git diff --check` is the record integrity check;
no builds, Oracle inspection, or measurements were run.

### Role-first gate reset from source clarification (2026-10-03)

The immediate gate is revised: before slot-profile projection, derive the
source judgment `introduction + expected context -> receiver role -> Function
interface -> effect-port view` for ordinary unannotated literals, explicitly
Function-annotated literals, and callback-position literals. The source role
is independent of §21 parameter entry. Existing role-elaboration notes treat
roles as fixed skeleton inputs and retain annotation slots; they do not state
the newly clarified selection/elaboration clauses. The immediate gap is
therefore source-role elaboration, not a uniform effect-component-to-interface
map.

The slot-profile/`CallView` projection, separate `Observe` paths for
`Force(D)` and body requests, pure-role existing-value adaptation, and complete
actual/checked challenge inclusion move downstream. Existing `Rel_C`, `K,D`,
occurrence/incidence, `Flow`/`Observe`, `Path`, `Inc_C`, and subtraction
evidence remain the candidate vocabulary; no specific unrepresentable source
fact or need for a new carrier is established. The intended joint
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)` remains to be derived after role
and interface elaboration, with no effect-position semantics assigned to
`never`. This is a primary-authored proof-gate correction, unreviewed and
without implementation authority. No code or tests changed; only `git
diff --check` is planned for this record slice, with no builds, Oracle work,
or measurements.

### Charter conflict resolved by explicit role supersession (2026-10-03)

The source audit exposed a direct conflict: charter §16 says every function
is a handler, while the user's newer §7 clarification assigns pure receiver
role to ordinary unannotated function literals and handler role to annotated
and callback-context literals. Added charter §24 to supersede only §16's
universal receiver-role claim, while retaining its invocation/entry mechanics
under the role and interface selected by source elaboration. In particular,
§21 value entry still forces and rebinds within a pure-role function
invocation. Updated the design crosswalk, index and task record to name this
boundary.

This is a direct record of the user's semantic clarification, not a new
inference rule or implementation decision. Effect-port elaboration and the
intended coupled Function inequality remain unproved. No code, tests, builds,
or Oracle work; `git diff --check` is the record integrity check, and no
measurement budget was used.

### Role-selection rule skeleton and overlap audit (2026-10-03)

Using the user's selected cases and core §6, I separated the derivable
role-selection clauses from the still-undefined interface constructor:
an unannotated lambda without expected callback boundary selects `Pure`;
an explicit Function annotation selects `Handler` at that annotation
boundary; callback-position elaboration selects `Handler` at the expected
callback slot. Then parameter entry comes independently from §21. Core
`Value(Fun(P, Result(I_b)))` supplies only the value/function/result
constructor skeleton; it does not interpret role-indexed effect ports. The
design note now records this as a proof schema, not a new solver carrier.

The overlap case is unresolved: a Function-annotated lambda may also be in a
callback slot. The two role decisions agree, but available source evidence
does not say whether the annotation boundary is compared to, nested within, or
otherwise related to the expected callback boundary. The elaboration proof
must preserve both original descriptors and explain their interface check
through the one `A <: B` solver, without merging profiles.

As a no-new-carrier working candidate, I recorded introduction under the
annotation-selected handler boundary followed by checking the resulting
Function value against the expected callback slot through the same concrete
inequality solver. This preserves the actual boundary/entry and leaves the
slot as a separate use-site view. It is conditional on a source annotation
introduction/checking clause that establishes this ordering; no type
annotation rule or callback `CallView` projection has been claimed.

The syntax-v0 operator-chain spec confirms only that `as Type` is a generic
annotation tail and explicitly excludes type meaning/checking. The current
HIR likewise preserves that tail generically. Neither supplies the missing
annotation-introduction/checking order, so the candidate remains conditional
on the Function-specific source rule rather than following from syntax.

The unannotated callback fixture has the matching source shape: `r.update`
declares a Function-valued callback slot; the user's callback-role rule
selects Handler for a literal in that position; and §21 independently
assigns `Value` entry to the lambda's unannotated `old` parameter. I had
overstated core §6 as deriving that the formal slot is passed into lambda
introduction before body elaboration. The architect audit found §6 only
synthesizes the argument and constrains its whole computation interface
against the formal; it does not state this contextualization route. The role
choice is user-selected, but propagation from the application slot before
body elaboration remains a conditional schema needing proof. The minimum
missing lemma is a source application/lambda elaboration rule that supplies
the declared callback interface before body synthesis, while leaving inert
whole-argument construction and receipt/entry order unchanged. Interface
ports, `CallView` projection and the pure-value inequality remain later.

I narrowed that obligation to a known callee with a declared ordinary
`Value(F_cb)` Function formal: the source application/lambda rule must feed
that original slot/profile into literal elaboration before body synthesis,
while §21 separately supplies the literal's own parameter entry; all
interface checks remain ordinary inequality tasks. A bounded independent
compiler-referee delta review found no findings and confirmed the candidate
does not claim core §6 proves this propagation. The unknown-callee,
computation-formal, annotation-overlap, role-port and full-CallView cases are
explicitly deferred. This review validates the bounded candidate only; the
source rule itself remains a proof target.

A bounded independent compiler-referee review found no remaining finding in
this correction. It confirmed the selected role versus unproved slot
propagation distinction, the runtime receipt-before-force condition, and that
annotation-first checking remains conditional. This closes review of the
correction only; the contextualization lemma, source annotation order and
role-indexed Function-port derivation remain open.

I also inspected current HIR ownership: `ResolvedExpr::Lambda` stores only
parameter, body, occurrence and range, while the narrow chain HIR retains
annotations only as generic `Value` syntax nodes. This is downstream evidence
that a future source elaborator/HIR must recover annotation and expected-slot
context before it can generate role-directed interfaces; it does not change
the immediate proof gate or authorize compiler edits. The general
role/interface schema remains primary-derived and unreviewed. The correction
and conditional annotation-overlap crosswalk received a bounded clean
compiler-referee review. No code or tests changed; no Oracle inspection or
measurements. `git diff --check` is the record-slice check.

### Static callback template versus runtime boundary (2026-10-03)

A spec-auditor delta review found that the first no-new-carrier crosswalk
confused a compile-time callback formal with the activation-indexed runtime
boundary `b`. I repaired the crosswalk: the known formal identifies a static
signature template `β∈B` and original `Slots(β)`; a still-conditional source
contextualization rule links the literal derivation to `β` before body
synthesis. Only callback receipt at execution instantiates
`b=(receiver activation, callback slot, typed contract)` from that template.
Runtime transport and eligibility remain in existing `Flow`/`Observe`,
`Path`, `Inc_C`, and shared `K,D` evidence. The independent spec-auditor
delta review reports the major finding closed and no remaining findings in
scope. This closes only the static/dynamic carrier crosswalk: the source
contextualization theorem and broader role/interface schema remain open. No
new carrier is justified by this delta. No code, tests, Oracle inspection or
measurements; `git diff --check` is the record-slice check.

### Declared callback-formal availability audit (2026-10-03)

A narrow follow-up architecture audit found an earlier input dependency than
application/lambda traversal. Syntax already represents binding/pattern type
annotations, expression annotations and import routes; however, current
lowering does not produce typed callable interfaces. Annotated binding
headers are rejected, `HirParameter` carries no interface, `HirItem` has no
callable declaration, `HirModule` has no imported typed-interface table, and
`SemanticImports` is empty. `yu-types` can represent closed Function schemes,
but root-indexed `SolvedModule` schemes are private solved output, while its
public root query projects Function schemes to `Unknown`. `ConstraintBatch::collect`
accepts only `Arc<HirModule>` and its scheme positions name local definition
roots. So the source contextualization theorem may stipulate supplied `F_cb`,
but implementation also needs source annotation/import elaboration and an
immutable typed-interface input. The actual `ref.update` example further
needs member/interface lookup. These are current-prototype limits, not
semantic reasons to reconstruct context from solver bounds or add provenance.
The exact input owner/lookup API remains undecided. The initial spec-auditor
delta review found a minor ownership ambiguity between the HIR collection
input and the collector's root indexes; I qualified it, and the follow-up
review closed that finding with no new issue. No code, tests, builds, Oracle
inspection or measurements.

### Current HIR boundary for callback contextualization (2026-10-03)

The source package audit confirms the known-callee pre-body contextualization
rule remains only a candidate: core §6 synthesizes a whole argument and
constrains it against the formal, while source-computation-role §4/§11 leaves
producer/consumer checking rules unfinished. Current implementation evidence
locates the owner boundary more precisely. `yu-hir::ResolvedExpr` currently
has only Lambda, Integer, Name and Error; `lower_simple_chain` resolves only
an atom, while CallTail/MlArgument and TypeAnnotationTail remain in structural
syntax/HIR association. Thus there is no current typed application form that
can carry a known callback formal into lambda elaboration before body
synthesis. This does not justify recovering the expected context from solver
bounds or adding solver provenance. The next implementation architecture gate
belongs at successor source application/lambda elaboration, after its source
rule is fixed. No code, tests, Oracle inspection or measurements; no
implementation authority inferred.

### Frozen application/lambda order characterization (2026-10-03)

Read-only inspection of frozen `main` at `a58eefc31e22141574b6f20c6a5748151c6d79f1`
provides a concrete historical contrast. `ExprLowerer::apply_arguments`
calls `lower_expr` on each argument before `make_source_app`; the latter
builds the application inequality in `make_app_with_origins`. That routine
then registers the newly created callee-to-Function constraint as the
argument's `ExpressionExpected` provenance root. `lower_lambda` accepts the
syntax node and `LambdaScope`, with no expected callback interface parameter.
Thus this frozen path records expected-use provenance after argument/lambda
lowering rather than passing the callback contract before body synthesis.
This is Oracle characterization only: it neither refutes the user's successor
rule nor supplies its source semantics. It confirms that the successor needs
an explicit source-level expected-context route instead of inheriting this
historical order or recovering context from solver bounds. No code, tests,
builds or measurements; no Oracle behavior promoted to successor authority.

### Source owner and HIR/collector timing audit (2026-10-03)

An architect audit compared the current source pipeline owners. The missing
known-callee `Value(F_cb)` contextualization belongs at source application /
literal checking before lambda-body constraints are emitted. The current
`ResolvedExpr` lacks applications; syntax association has call/operator
structure but no declaration typing; the collector emits lambda facts later.
The audit therefore leaves two possible placements open: retain enough
application/literal structure for an ordered contextual collector walk, or
perform an earlier source-check traversal. A resolved application/lambda tree
could suffice; adding an application node alone does not supply the required
context threading. No concrete representation, phase or scheme-instantiation
API is selected, and `yu-solver` must not reconstruct the context from bounds.

The first draft overstated HIR body wrapping as though it were semantic
elaboration and said an application node after HIR lowering would be too late.
Independent compiler-referee and spec-auditor reviews both found this major
timing error: body syntax is lowered into `ResolvedExpr`, but
`ConstraintBatch` emits lambda/body facts later. I corrected the candidate to
place the ordering condition at body-fact generation; both delta reviewers
then reported the major finding closed and no new findings. The remaining
source contextualization theorem, exact owner/API, role-indexed ports and
complete inequality are open. No code, tests, Oracle inspection or
measurements; `git diff --check` is the record-slice check.

### Role-first gate refinement (2026-10-03)

The immediate subgate now states the three source introductions explicitly:
ordinary unannotated function literals select Pure; an explicit Function
annotation selects a handler boundary; callback-position literals select
Handler from expected context. Each role must be established before its
Function interface and effect-port interpretation. The gate does not begin
with a uniform mapping from an effect-row component to a complete
receiver/computation interface, and it keeps §21's independent
Value/Computation parameter-entry role separate.

The callback lift remains to be derived from role-specific source application
and `Force(D) >>= B`, jointly accounting for argument computation `d` and body
effect `b` in the existing `Rel_C` fiber and `ν`. Four independent effect-port
subtyping checks and effect-position meanings for `never` or `Any` are not
premises. Value `never`, `Any`, empty effect row, and polarized solver extrema
remain distinct. This refines research order only: no solver carrier or
provenance structure is justified without a concrete source fact that the
existing `Rel_C`, `K,D`, occurrence/incidence, and directed-weight/subtraction
evidence cannot represent. No code, tests, Oracle inspection, builds or
measurements; record consistency was checked with `git diff --check`.

### Role projection versus source elaboration (2026-10-03)

A bounded architect audit sharpened the immediate gate. Charter §24 already
selects Pure for an ordinary unannotated literal without handler expected
context, Handler for an explicitly Function-annotated literal, and Handler
for a callback-position literal. Charter §21 independently sets parameter
entry; core §6 supplies only the `Value(Fun(P,Result(I_b)))` body/result
skeleton. These decisions fix the role projection, but do not construct the
complete role-indexed Function interface.

For annotation-plus-callback overlap, both role selectors yield Handler while
the annotation boundary and callback slot remain distinct descriptors. Their
source relationship is open; annotation introduction followed by checking at
the expected slot remains a candidate only. The actual next source theorem is
pre-body annotation/expected-context propagation and complete interface
construction. For a supplied known `Value(F_cb)`, the bounded target passes
static `β`/`Slots(β)` before body facts are emitted; current source input/API
and scheme-instantiation ownership remain open. No effect-port or inequality
rule follows from this projection alone.

A spec-auditor delta review found no blocking/major issue and one minor table
formatting issue, which was repaired by converting the non-literal comparison
case to prose. `git diff --check` is the only verification; no code, tests,
builds, Oracle inspection or measurements. Implementation authority remains
none.

### Remove residual effect-position `never` premises (2026-10-03)

A reread of the necessary-condition section found older prose that still
explained effectful challenge admission by interpreting the actual negative
`never` endpoint, despite the newer role-first gate. I replaced that premise
with the actual source obligation: the same checked challenge must belong to
the role-derived actual callable view, respecting receipt and §21 entry. The
`Force(D) >>= B` support bound remains conditional source-call evidence only;
it assigns no row-component denotation. The second inequality keeps shared
`e`/`K,D` correlation without a `never` rule.

An independent compiler-referee delta review found no findings. Neither
inequality is proved; complete role-indexed views and challenge-domain
construction remain open. `git diff --check` is the only verification. No
code, tests, builds, Oracle inspection or measurements; implementation
authority remains none.

### Callback expected-context semantics versus implementation (2026-10-03)

The source contract is now recorded at the authority level given by the user's
clarification: for an unannotated Function literal in a known callback slot,
the slot's expected boundary reaches literal elaboration first, selects
Handler, and governs Function-interface elaboration before body constraints.
The same callback literal still gets its own parameter entry from §21. An
explicit Function annotation selects its own Handler boundary; when it also
occupies a callback slot, both descriptors remain distinct and their checking
relation is open.

The current core §6 synthesize-then-constrain path does not implement this
selected source order. The formal derivation and source owner/API, declared
interface input, complete role-indexed interface and effect-port rules remain
open; the pure-value inequality is still unproved. A bounded spec-auditor
review found no findings in this status correction. `git diff --check` is the
only verification. No code, tests, builds, Frozen Oracle work or measurements;
implementation authority remains none.

### Bounded callback expected-context delivery proposal (2026-10-03)

Reconsidering the immediate gate against the user's role-first source rule
confirmed that effect-port mapping remains downstream. I wrote a bounded
contract in `notes/design/2026-10-03-callback-context-delivery.md`: with a
known, already instantiated `Value(F_cb)` formal and its original static
`β`/`Slots(β)` identity supplied, that context reaches an unannotated callback
literal before any body constraint. Handler selection occurs there; §21 still
independently determines parameter entry; `Result(I_b)` still supplies result
forwarding. The contract neither copies callback ports into the literal nor
proves either intended Function inequality.

The proposal keeps application/member/import lookup, scheme instantiation,
annotation/callback overlap, the complete role-indexed interface, and effect
port laws open. It retains static `β` versus dynamic activation boundary `b`,
leaves runtime receipt/force order unchanged, and adds no solver carrier. The
current HIR/collector lacks both resolved application structure and typed
callback input, so this is a reviewed supplied-input contract, not current
implementation or an API selection.

The architect pre-write audit recommended treating the typed declaration input
and transient expected context as separate responsibilities, without
committing to a compiler phase. A compiler-referee and spec-auditor reviewed the
bounded proposal with no blocking or major findings. The spec audit found one
minor header-status inconsistency; the header now records `Reviewed` while
keeping user approval pending and API/phase unresolved. `git diff --check` is
the only check; no tests, builds, Oracle inspection, or measurements. The draft
is ready for user approval before implementation or durable API selection.

### Separate contextual literal introduction from Pure-value adaptation (2026-10-03)

A reviewed §4 delta in `notes/design/2026-10-03-callback-context-delivery.md`
separates two paths that share the callback context but require different
proofs. A new unannotated literal in a known callback slot selects Handler
before body constraints. An existing Pure function value retains its actual
introduction role and §21 entry, then reaches a handler-capable slot through
one concrete `A <: B` resolution whose evidence may realize an adapter. The
first path does not prove the intended pure-to-handler inequality, and
concrete successes remain non-composable.

The stable-core `ref.update` public signature and literal call substantiate
only the contextual-introduction path. The library implementation is absent;
this fixture does not prove its challenge domain or existing-value adaptation.
The next source proof must construct one complete `CallView` and establish
`D_checked(ν) ⊆ D_actual(ν)` plus `P_actual(d) ⊆ P_checked(d)` for every checked
challenge under the same `Rel_C` fiber. `Force(D) >>= B` provides only the
conditional Value-entry support premise; support union alone does not establish
the effect ports. A spec-auditor and compiler-referee delta review found no
findings. `git diff --check` is the only check; no code, tests, builds, Oracle
inspection, or measurements.

The user approved the bounded source contract on 2026-10-03: an unannotated
callback-position literal receives its expected callback boundary before
body elaboration and is introduced as Handler; an already constructed Pure
Function value follows a separate concrete `A <: B` adaptation path. The
design note is now Authoritative only for that bounded source contract.
Typed-interface ownership, transient context versus a separate elaboration
product, and compiler API/phase remain undecided; no implementation is
authorized by this approval.

### Discriminating source witness for existing Pure-value adaptation (2026-10-03)

The next proof-only slice adds §8 to
`notes/design/2026-10-03-callback-context-delivery.md`. It uses an already
constructed Pure identity function with §21 `Value(A)` entry, specializing
`A = Int` only for the witness. The higher-order receiver receives `f` at its
callback slot and invokes it while that receiver's handler-capable boundary
is live; the schedule distinguishes receipt of `f` from receipt of `D_req` at
the actual invocation, then forces/rebinds before the body. A paired pure-
diverging argument carrier has the same result endpoint but no request
support, exposing why request-row support alone cannot stand for complete
challenge admission or observation.

Compiler-referee and spec-auditor independently found the initial witness
schedule conflated those two receipts and overstated §21's endpoint; the
revised delta separates them and uses `Value(A)` with witness specialization
`A = Int`. Both reviewers then closed those findings with no residual issue.
The witness remains conditional: it requires a live enclosing boundary,
complete `CallView`, both full inclusion clauses, and projection through
existing `Rel_C`/`K,D`, occurrence/incidence, `Flow`/`Observe`, and subtraction
evidence. Escaped callbacks and the intended inequalities remain open. No
Oracle investigation, tests, builds, or measurements were performed.
`git diff --check` passed for this documentation-only delta.

The primary's next-step derivation narrows the identity witness's behavioral
obligation. With an already constructed `f = λx.x` at §21 `Value(A)` entry,
the invocation body is `Return(x)`, so the selected call equation reduces to
`Force(D_req) >>= Return`. The state-threaded bind right-unit law preserves
the forced computation's request prefix, response/resumption behavior, and
resulting store/context and divergence; the identity body adds no request.
This gives behavioral equality only after both paths share the same live
callback-slot `CallView` and the challenge is admitted. It does not show that
the checked view admits `D_req` or the paired diverging carrier, nor that
`[b,d]` projects argument observations through the required
`Flow`/`Observe`/incidence and `K,D` paths. Those remain the immediate proof
obligations. This conditional
derivation is primary-authored and not independently reviewed; no source or
solver implementation changed.

The identity witness also yields a local **runtime-domain** inclusion lemma.
Let `Carrier_A(ν)` contain source-admissible invocation challenges whose
argument computation has exposed value endpoint `A`, with its complete
source histories. The checked callback slot's equal value endpoint `A`
places its admitted argument challenges in this carrier. The closed identity
function's §21 `Value(A)` entry receives and forces any such carrier; it has
no capture or body-state precondition beyond source admissibility, and its
identity body returns the forced value. Thus each challenge has a matching
actual source execution, including request prefixes, state changes, response
histories and divergence. This does not yet prove the static
`D_checked(ν) ⊆ D_actual(ν)` clause: the role-derived actual Function view
must still be shown to denote the `Value(A)` runtime-call domain without
using effect-position `never` as a sentinel. For observation inclusion, the
same live `CallView` and typed path must carry argument `Observe` events into
the checked output's `d` component; `[b,d]` spelling alone does not prove that
projection. This narrows the witness proof but leaves that interface/evidence
bridge open. Primary-authored, conditional, and independently reviewed.

### Identity witness: existing-evidence route for one argument request (2026-10-03)

For one typed request occurrence `q` in `D_req`, a checked challenge supplies
the occurrence at the callback's contravariant input position `p_d⁻` under
component `d`. `Receive(u,slot,view,χ)` records the already constructed Pure
value at that callback slot. Under the candidate source-preserving identity
FunctionView, the expected slot view encloses the actual invocation; §21 Value
entry then executes `Force(D_req)` inside the same complete `CallView`. This
input-side premise is conditional on the concrete inequality providing that
view; it does not map or equate the actual function's native
effect component `never` with `d`. The source-preserving view must additionally
supply an executing `View` occurrence in `EC(C_emit(q))` marked with `p_d⁻`.
Only then does the typed-boundary definition of `Observe` give
`Observe(q,view,p_d⁻)` before handler search. The identity `Flow*` path and
`Receive` do not create that executing occurrence or choose its port;
`Path` composes the source profile, typed flow, observation and slot receipt,
while `Inc_C` checks current receiver/handler liveness. The request's
operation identity, family arguments and constraints remain in the source
occurrence, incidence `D`, predicate `K`, and shared `ν`.

This establishes the input-side observation path conditionally. The remaining
source lemma is a second observation for the same event identity at the
positive output member `p_d⁺` of `[b,d]`. `Flow` should not be invented as an
edge from `p_d⁻` to `p_d⁺`: `Flow` transports typed value/dependency paths,
while both of these are effect positions. Instead, the source call derivation
must directly establish `Observe(q,view,p_d⁺)` for the request exposed by
`Force(D_req)` inside the complete call. The two `Observe` facts then share
the same source occurrence, operation instance, family arguments, incidence
`D`, predicate `K`, and assignment `ν`; the concrete-bearing polarity
descriptor and directed-weight/subtraction evidence can use that attachment
without a duplicate ledger. The identity body contributes no request to `b`.
Whether that direct output observation follows from the role-derived call
interface is the exact open source rule. Independent review confirms that
both input and output observations require their own source-generated
executing `View` occurrence with the exact marked port; transport, receipt and
support preservation do not generate either observation. No carrier gap is
established. The derivation is primary-authored and conditional.

The fixed-shape adapter draft supplies a conditional schedule check for this
identity case. Its `FunctionMap(da,dr)` application equation, specialized to
`da = dr = Id`, reduces as

```text
Apply(FunctionView(f,Id,Id),D)
  = Return(D) >>= (λy. Call(f,y) >>= (λz. Return(z)))
  ≃ Call(f,D)
```

by the existing state-threaded bind unit laws. `Id` executes no argument
conversion, so `Call` still receives the complete inert carrier before the
actual `Value(A)` entry forces it. The administrative FunctionView adds no
receiver or handler; a surrounding expected callback boundary remains the
same complete `CallView`. This demonstrates that the existing adapter
realization vocabulary can preserve the selected source schedule for this
identity pair, conditional on that view being a source-admissible realization.
Here `Id` applies only to value-level argument/result adaptations; it does not
equate the contravariant effect descriptor `never` with `d`. The calculation
does not prove the concrete `A <: B` succeeds or that the view's effect-port
correspondence is sound.

The adapter calculation narrows the observation proof further: it creates no
new request, origin, or `K,D` incidence, so every relevant `Observe` edge is
still generated by `Call(f,D)`'s `Force(D)` and body derivation. The unresolved
source assignments are the input force occurrence to `p_d⁻` and the same
event's exposed complete-call occurrence to the positive output `d` position
of `[b,d]`, plus the matching polarity-specific attachment evidence.

#### Unselected source-port bridge candidate

The smallest source rule that would close this witness is an elaboration rule
for invoking an already constructed Pure value through a known handler-capable
callback slot. Given the slot's expected Function view and a source call that
receives the callback value and then invokes it with `D_req`, the rule would
construct, before inequality success is used, one executing force occurrence
`o⁻` for the `Value(A)` entry and one enclosing complete-call occurrence
`o⁺`. At the same emission of `q`, source typing must establish both:

- the force view `o⁻` is marked at `p_d⁻`;
- the complete-call derivation projects that same request at `o⁺.port = p_d⁺`.

Both facts retain the original callback slot/profile, operation instance,
family arguments, incidence `D`, predicate `K`, and shared `ν`. The source
bind suffix preserves `q` through rebinding and body entry;
`Observe` then follows from the two enclosing executing views, and existing
`Path`/`Inc_C` and directed-weight/subtraction evidence consume the attachment.
This rule changes neither the actual Pure introduction nor its §21 entry, and
its identity-adaptation realization must preserve receipt-before-force. It
introduces no effect-to-effect `Flow` edge or new carrier.

This is a candidate source premise, not a derived rule or established
inequality. Generic core §9 supplies the Force/bind execution and input/output
directions, while boundary §4 projects observations from source-marked views;
neither specifies the two target-port correspondences. A countermodel keeps
the same identity schedule and marks only `p_arg` and `p_call`; it satisfies
those generic rules but lacks the two checked `d` attachments. That is
underdetermination of the current premises, not a source-program
counterexample. A bounded spec-auditor review found no scope/conformance issue in this
candidate wording: it remains unselected, preserves Pure introduction and
§21 entry, and adds neither a sentinel interpretation, effect-to-effect
`Flow`, nor an accepted-program claim. Its semantic sufficiency remains open;
review of candidate wording is not approval of the rule. The candidate must be
reviewed against source-level callback adaptation and complete-interface
elaboration before asking whether this narrow port-attachment rule matches the
intended language semantics.

Independent architect and compiler-referee audits agree that core §9 derives
the negative carrier direction, positive complete-call direction, and
preservation of one Force event through the pending bind suffix, but not the
role-specific checked-port correspondence. Boundary §4 only creates
`Observe` for already source-decorated executing `View` occurrences. An
underdetermination model can therefore preserve the operational identity
schedule and generic directions while marking the force/call as `p_arg` and
`p_call`, with no source correspondence to `p_d⁻`/`p_d⁺`. This is not a
counterexample to an approved source rule; it shows that the current premises
do not entail the desired port attachment. Both exact ports must be generated
from role-specific source interface/application elaboration, independently
of comparison success, and refer to the same event at its emission under the
same `ν,K,D`. Existing `View`/`Observe`, typed correspondence,
occurrence/incidence, `Path`/`Inc_C`, and directed-weight/subtraction evidence
can express and consume those facts; no carrier gap is shown. The next bounded
proof gate is that source-generated decorated invocation for the closed
identity witness, retaining distinct callback-value and argument receipts,
actual §21 entry, live boundary, and resumption suffix. No inequality or
accepted-program claim is established.

### Identity witness: operational challenge-domain simulation (2026-10-03)

For the same closed `f = λx.x`, specialize the shared endpoint to `A = Int`
and retain §21 `Value(A)` entry. Under one source-admissible caller state and
one live callback-slot `CallView`, any checked challenge with that endpoint
can be reused unchanged as the actual call's carrier/history: reify it
inertly, receive it, force it at entry, and return the result. The actual
closure has no captured state or body effect; therefore request prefixes,
store transitions, responses, and finite repeated/resumed histories all come
from the supplied challenge and are preserved. This is an operational domain
simulation that does not inspect or interpret the actual interface's
effect-position `never`.

The static interface clause still needs a bridge: prove that the actual
role-derived complete Function domain denotes these `Value(A)` executions,
and that the checked view admits only challenges in that source domain. The
second inclusion `P_actual(h) ⊆ P_checked(h)` still needs the input event's
`Observe`/`Flow`/incidence route into the checked output component `d` under
shared `ν,K,D`. An independent compiler-referee audit found the operational
lemma clean under its stated fixed-context premises: the state-threaded bind
right-unit law preserves request identities and continuations, resumed live
states, store histories and divergence; the `Int` endpoint rules out latent
result forcing. The reviewer explicitly did not infer either static port
inclusion or equivalence across different `CallView`s. No implementation or
tests changed.

### Force/body source partition for the callback effect-lift witness (2026-10-03)

Sol's next proof slice separates an operational fact from the still-open
typed-port map. For a supplied ordinary application with a value-entry
callback, and identity value-level argument/result transport, retain the
actual call equation from ordinary semantics:

```text
receipt(D);
Force(D) >>= λ(v,C').
  RebindResultPath(D,v,C');
  Run(B,v,C')
```

Label a request transition by the source phase that emitted it: the demanded
argument force, or a reached body execution after that force returned. By
inversion of the state-threaded bind rules, each request in a finite complete
call prefix is emitted by one of those two phases. A left-side request keeps
the typed rebind/body suffix in its continuation; each actual raw resumption
continues that suffix in its resumed state. A right-side request is emitted
only in a body state reached after such a force result. Repeated or multi-shot
resumptions can create further event occurrences, but do not create a third
source phase. The event's operation instance and its original `K,D` incidence
remain attached to that transition. This gives an occurrence-preserving
source partition, not a union equation for solved effect rows. Any separately
executing non-identity conversion would need its own source-phase case and is
outside this witness.

Consequently, if one supplied assignment `ν` and one complete relational
fiber establish phase-specific admission sets `E_force` and `E_body`, then
the call's support projection is contained in `E_force ∪ E_body`. To identify
that union with support of the canonical flat row `[b,d]` requires a separate
source-derived component-combination premise in the same fiber. Admission by
`d` for force requests and by `b` for body requests, on its own, does not
establish that row interpretation. The identity witness `B=Return` has no
body-phase requests; the general body case keeps its reached post-force state
dependence. This support corollary does not select a meaning for `never`,
does not independently subtype the four Function ports, and does not turn the
argument/body relation into a Cartesian product.

There are two limits. First, event partition plus support containment does
not prove complete-observation inclusion `P_actual(h) ⊆ P_checked(h)`: that
still requires checked-view continuation/state coverage for the same
`Rel_C` fiber. Second, the phase label alone does not produce `Observe` at the
checked positive member `p_d⁺`. If the row comparison is justified only by
component support, that may be enough for the extensional support obligation;
it is not yet the typed `CallView`/boundary derivation required by the
existing `Observe` contract. No port-to-port `Flow` edge is inferred.

This is a Sol-authored proof candidate, not a selected successor rule. It
isolates the source fact available from bind and leaves the exact residual
question open: derive a component-combination rule connecting these
phase-specific supports to `[b,d]` while the complete joint continuation
relation stays in the same fiber. The canonical flat form is selected; its
source denotation and combination rule are not. No compiler code, tests or
builds changed.

### Architect audit of the approved callback-context contract (2026-10-03)

The bounded contract establishes pre-body Handler introduction for a new
callback-position literal. It does not derive the distinct existing-Pure-value
adaptation path's checked port marks. Charter §21 and ordinary invocation
semantics preserve the `Value(A)` Force event, its operation instance and
pending continuation under the shared `ν,K,D`; boundary `Observe` still
requires source-marked executing views. Generic operational input/output
directions do not identify those views with checked `p_d⁻` and `p_d⁺`.

The same audit confirms that canonical flat form alone does not identify
`[b,d]`'s support denotation. The phase partition bounds the call by supplied
force/body admission sets, but a source component-combination clause must
connect those sets to `d` and `b` in the same joint fiber. Existing
`View`/`Observe`, `Rel_C`, occurrence/incidence, `K,D`, `Path`/`Inc_C`, and
subtraction evidence can express the needed facts; no new carrier is
justified. This is a missing source-semantic proposition, not an API/phase
problem, and the callback-context contract does not decide it. The proposed
bounded rule has been presented for user decision; no new semantics or
implementation authority is selected here.

### Sol derivation and compiler-referee audit: component projection remains open (2026-10-03)

Sol's bounded source derivation confirms the bind-inversion result: for an
already constructed Pure callback with §21 `Value(A)` entry, requests in the
identity-transport invocation arise during argument force or during body
execution at a reached post-force state. This yields a conditional request-
support containment under one supplied joint fiber. It does not identify
either phase's occurrences with the checked input and output positions of
`[b,d]`.

The compiler-referee audit found no blocking or major defect in that bounded
conclusion and confirmed that the gap is real. Core §9 already gives the
complete relational `J_call` as the image of `ExecuteCallable`; therefore the
missing result is not generic sequencing or all component denotation. It is
the role-specific complete Function description and its projection onto the
checked profile positions, sufficient to prove the two joint inclusion
clauses in one `Rel_C`/`ν` fiber. Charter §24 leaves effect-port elaboration
and the inequality open, while callback-context delivery §4–§5 and §8 require
the checked occurrence/profile projection before `[b,d]` is justified.

The divergent-argument discriminator rejects equality with all body support
unconditionally, but does not reject a conservative union upper bound after
component premises are independently proved. Likewise, flat support cannot
replace the complete challenge domain or preserve response/state correlation
by itself. Existing `View`/`Observe`, `Rel_C`, occurrence/incidence, `K,D`,
`Flow`, and subtraction evidence remain the proposed machinery; no new carrier
is justified. The next gate is the closed identity witness's checked complete
`CallView` and exact profile-position map. If existing source clauses cannot
derive that map, isolate the missing semantic premise for user decision. No
Oracle inspection, code, tests, API/phase selection, or implementation
authority resulted from this investigation.

### Frozen Oracle Function-adaptation characterization (2026-10-03, Luna)

Read-only inspection of Frozen Oracle commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` establishes the implementation
shape, not successor semantics. `specialize2/type_graph.rs` decomposes a
Function comparison into four variance-directed child constraints after
splitting declared runtime shapes. `specialize2/tests.rs` separately
characterizes covariant return-effect and contravariant argument-effect
candidate checks. When both boundary endpoints are Functions,
`specialize2/runtime_shape.rs` emits a `FunctionAdapter`; the runtime
`apply_adapter_value_inline_result` adapts the target argument to the wrapped
function's source argument, invokes that function, then adapts source result
to target result. Thus the historical pipeline has distinct compatibility
decomposition and adapter realization stages.

This trace does not prove the intended
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)`, does not identify checked
`p_d⁻`/`p_d⁺`, and does not establish how the successor should derive its
effect ports. In particular, Oracle's four-child decomposition and its
`Never`/effect-row representation artifacts are not promoted to the successor
rule. No Oracle tests were run; the cited assertions are source characterization
at the frozen commit. No successor source, code, tests, or API/phase decision
changed.

### Sol identity lift candidate under the user's selected linked semantics (2026-10-03)

The user's explicit intended inequality and explanation select the projected
completion for the closed Pure-value lift: the `d` contribution from the
argument computation is linked to the positive complete-call row `[b,d]`.
This resolves whether that semantic link is wanted; it does not authorize
assuming the concrete inequality's success. The earlier `p_arg`/`p_call`
completion remains a model of the generic repository kernel only and is
excluded by the user's selected semantics.

Sol derived the identity-value execution independently from comparison
success. For an existing Pure `f = λx.x`, with §21 `Value(Int)` entry, the
actual invocation is

```text
J_call(D,C) = Force(D,C) >>= Return
```

The proposed checked complete relation composes the supplied argument relation
`Arg_d(ν)` with the reached body relation `Body_b(ν)`, retaining response,
state, pending continuation, and family constraints under one `ν,K,D`; it is
not a Cartesian product of row supports. The candidate assigns the same Force
event to the negative input position `p_d⁻` and its linked positive
contribution `p_d⁺`. Existing `View`/`Observe`, `Receive`, typed `Flow`,
`Path`/`Inc_C`, and event occurrence evidence can carry these two attachments
without a new carrier. The actual callback-value receipt remains distinct from
the later argument receipt, and the §21 force stays after receipt.

The compiler-referee review found no blocking or major defect in this
**conditional decomposition**: bind composition preserves the complete
identity execution, including responses, divergence prefixes, and continuation
suffixes. The spec-auditor confirmed conformance to the already selected user
intent and callback-delivery scope. Neither review certifies the concrete
inequality. Both retain these closure obligations:

1. Derive the actual and checked complete challenge domains from their
   role-derived interfaces and prove both universal inclusions in the same
   nonempty well-formed fiber, including future uses, resumed states, stores,
   responses, and pending suffixes. Two sample carriers or request-support
   containment do not establish this clause.
2. Derive admissible source-generated `View` occurrences at exact `p_d⁻` and
   `p_d⁺` from the original callback slot/profile, before inequality success;
   show both enclose the same emitted event and retain receipt, `ν,K,D`, and
   live-boundary evidence. `Observe` only consumes these decorations; it does
   not prove that they satisfy the slot contract.
3. Establish both request-carrier and pure-divergence challenge admission,
   and show `Return(Int)` belongs to the body relation at every reachable
   post-force state.

The exact next proof is a source-generated identity receipt/decorations
diagram using the existing profile and evidence, followed by the universal
domain check. No implementation, compiler API/phase, new carrier, tests, builds,
or Oracle work resulted from this proof candidate. Review scopes were bounded
to the identity witness and named source contracts; general Function cases,
escaped callbacks, and the Milestone-3 residual theorem remain outside.

### Sol identity receipt/execution diagram and remaining adequacy lemmas (2026-10-03)

Sol completed the bounded operational diagram for the already approved
callback-context delivery contract. Let `β, Γβ` be the original known slot
profile and `B` its live boundary. The flow is:

```text
Receive(r, slot, V_cb, χ_cb)
  -> inertly construct Delay(D_req)
  -> invoke existing Pure identity at §21 Value(Int) entry
  -> Receive(u, arg, V_arg, χ_arg)
  -> Force(D_req) >>= Return
  -> Observe/Path/Inc_C only after admissible source Views are supplied
```

The callback-value receipt and argument receipt are distinct. The argument is
not forced before invocation or receipt, and the actual identity invocation is
not reclassified as a Handler. Bind right-unit preserves the identity call's
request/response histories, state, pending continuation suffixes, repeated
resumptions, and divergence prefixes for the same live `CallView`.

Under the user's already selected linked-lifting semantics, the same Force
event is the intended negative `p_d⁻` contribution and positive `p_d⁺`
contribution. The positive complete-consumer mark is a source-decoration
obligation prescribed by that semantics; it is not derivable merely from
`Observe`, support membership, or the eventual success of `A <: B`. The
operation contract transfers compatible operation events but does not map
the executing argument position into the original slot profile.

Two lemmas remain distinct. First, a role-indexed invocation-position
adequacy lemma must derive the exact source-generated `View`s at the original
profile's `p_d⁻` and `p_d⁺`, with typed correspondence, live boundary, and
separate receipts. Second, a Value-entry domain-lifting adequacy lemma must
show that the role-derived actual interface admits the whole checked
challenge domain in a common well-formed `ν` fiber; operational identity
simulation for `A = Int` alone does not establish either universal inclusion.
The current core Function denotation quantifies over `x ∈ ⟦A⟧` and a candidate
`CallCfg`; its source context/Env denotation remains open. Thus it does not
prove inclusion of every admissible computation carrier and history.

The closure check must include request-carrier admission and pure divergence
(the body is unreachable there), response-dependent suffixes, mutable store
admission/transition closure, and repeated resumption/context closure. Empty
request support cannot stand in for divergence admission; compatible request
heads alone do not establish dependent response/history admission. Existing
`Rel_C`, `K,D`, occurrence/incidence, `View`/`Observe`, `Receive`, `Flow`,
`Path`/`Inc_C`, and subtraction evidence remain sufficient candidates; no
unrepresentable fact or need for a new carrier was found. No semantic choice,
API/phase ownership, implementation, tests, builds, or Oracle work was added.

### Sol source-clause audit of identity slot positions (2026-10-03)

A focused Sol audit checked whether the exact profile-position mapping can be
derived from existing clauses for the closed Pure identity callback witness.
It found no such clause. The approved callback expected-context contract
covers a *new literal* before body elaboration; its existing-Pure path keeps
the value's actual introduction and requires a separate concrete `A <: B`
adaptation. Core §9 supplies the complete `J_call` execution and dependency
interaction, while typed-boundary `Observe` and `Flow` consume already
supplied executable positions and correspondences. None equates those generic
positions with the original slot profile's exact `p_d⁻`/`p_d⁺`; deriving them
from an admitted adapter descriptor would assume the source fact at issue.

The minimal remaining role-indexed source adequacy lemma is:

```text
β, Γβ, received V_cb ⊢ the actual Value-entry Force(D_req) executes at p_d⁻
β, Γβ, received V_cb ⊢ that event's linked complete-invocation contribution
                         is exposed at p_d⁺
```

The second position is a direct complete-call contribution under the user's
selected linked-lifting intent, not an invented `Flow` edge between effect
positions. The derivation must retain the ordinary typed correspondence from
argument receipt to the input signature, distinct callback-value and argument
receipts, original `β/Γβ`, live boundary, and shared `ν,K,D`, all before using
comparison success. Existing boundary projection lemmas then compose the
observations once those premises exist. Separately, checked-domain inclusion
and joint observation inclusion still need proof over all admitted histories;
the concrete identity simulation does not establish those universal clauses.

Two independent bounded reviews (compiler_referee and spec_auditor) found no
new defect in the recorded conditional identity execution. Both confirm that
the owner/re-entry example refutes the superseded outward-only observation
projection, not `Force(D_req) >>= Return` for this fixed request/return
witness. The current pre-dispatch decorated kernel records enclosing views
before dispatch and preserves ambient views during borrowed-owner re-entry;
its theorem remains conditional on correct source decorations. Therefore this
example creates no new solver carrier or API/phase decision. The next gate is
the source-position adequacy proof, followed by the independent complete-domain
proof. No implementation, tests, builds, or Oracle work occurred.

### Correction: linked contribution needs profile-to-execution paths, not coordinate identity (2026-10-03)

A conformance review found that the previous gate wording was too strict when
it asked for executing `Observe` marks literally at the original slot's
`p_d⁻` and `p_d⁺`. Typed-boundary §6 `Path` starts at an original profile
position and follows matching typed-flow edges **toward** a current executing
position with an `Observe` mark and matching receipt; it does not require
coordinate identity. Direct original-coordinate execution remains one valid
presentation, but a transported current call position is also allowed when
its correspondence is independently source-admitted.

The corrected minimal source-admission lemma for one event `q` is:

```text
Flow*(β.p_d⁻, V_force.p_force)
Observe(q, V_force, p_force, o_force)
matching receipt correspondence from the original callback slot to V_force

Flow*(β.p_d⁺, V_call.p_call)
Observe(q, V_call, p_call, o_call)
matching receipt correspondence from the original callback slot to V_call
```

The flow direction is original profile → executing position on both signed
paths. The actual argument-force view must execute inside the complete-call
view at `q` emission, so both observations name the same event, operation
instance, family constraints, and shared `ν,K,D`. Core entry/bind supplies the
negative-input to positive-complete-invocation contribution as a relational
dependency. No `Flow` edge from `p_d⁻` to `p_d⁺` is warranted. The callback
value receipt `Receive(r, callback_slot, V_cb, χ_cb)` and invoked function's
argument receipt `Receive(u, argument, V_arg, χ_arg)` remain distinct; neither
substitutes for the source correspondence/receipt evidence that `Path` needs
for each executing view.

Given these source-generated flows, observations, nested scopes, and matching
receipts, the existing §6 rules derive `Path` and current `Inc_C`. Existing
FunctionView identity adaptation preserves the execution schedule but does
not instantiate these premises. The selected linked lift fixes the abstract
contribution but does not choose literal versus transported coordinates. The
source-admission lemma is still open, as are complete checked-domain and joint
observation inclusions.

The compiler-referee review confirmed that literal p+ coordinates are
unnecessary and emphasized the required flow direction. The spec-auditor
raised a major conformance finding on the earlier exact-coordinate wording;
this correction accepts and closes that finding. Neither review certifies a
complete raw-source model or inequality. No new semantic/API choice, carrier,
implementation, tests, builds, or Oracle work resulted.

### Candidate source-check schema for an existing Pure callback value (2026-10-03)

Sol advanced the gate from a named missing judgment to a proof-only
obligation-generating source-check schema. For an existing Pure value `f`
with actual interface `T_actual`, a supplied known instantiated callback
interface `F_cb` and original profile `(β,Γβ)`, and a same-activation
callback use, the source elaboration generates exactly the concrete query
`T_actual <: F_cb` under the one inequality solver. It also constructs a
candidate decorated consumer plan and attaches proof obligations. This is a
source rule that generates an `A <: B` task; it is not a second semantic
compatibility relation, a query success, a source acceptance claim, or an API/
phase selection.

The candidate plan keeps the callback-slot receipt
`Receive(r,slot,V_cb,χ_cb)` apart from the actual invocation's argument receipt
`Receive(u,arg,V_arg,χ_arg)`, and proposes:

```text
β.p_d⁻ → V_force.p_force
β.p_d⁺ → V_call.p_call
View(V_call,p_call,
  View(V_force,p_force,Force(D)) >>= typed rebind >>= Return)
```

Both paths are same-polarity typed correspondences from original profile to
current execution. The views must be nested at emission so the same event is
observed in both. The slot-owner receipt path needed by `Path` must be derived
from typed callback-view flow; the argument receipt by `u` does not imply
receipt of the callback's public view by `r` or authorize pasting it onto
private bindings. Core entry/bind relates the negative argument contribution
to the positive complete-call contribution without an effect-to-effect `Flow`.

The plan's arrows remain proposed obligations until independently justified by
source elaboration and the matching typed correspondence rules. The concrete
inequality resolver must validate the plan and both complete-domain clauses;
it cannot use the desired paths as an assumed result and then cite that result
to prove them. For the fixed identity, `FunctionView(Id,Id)` gives the
schedule-preserving operational realization but supplies neither boundary
authority nor typed-path/receipt admissibility. The compiler-referee found no
semantic contradiction in using the schema as an obligation generator and
confirmed that actual Pure role and §21 Value entry remain intact. The path
certificates, exact owner receipt join, and universal challenge/observation
inclusions remain open. Existing HIR has no application node or typed formal
input, so the schema is not yet an implementation design; API and phase remain
unselected. No code, tests, builds, Oracle work, or new carrier resulted.
