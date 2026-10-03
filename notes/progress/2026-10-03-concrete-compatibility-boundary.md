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
