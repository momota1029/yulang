# Finite guarded closure for endpoint-dependent inequality solving

Status: Draft; reframed after the user's 2026-10-03 clarification of one inequality judgment
Date: 2026-10-03
Scope: finite closure of internal solver states for a fixed finite endpoint-dependent inequality transition system
Approved-by: no solver semantics or implementation approved; the user's single-inequality direction is recorded in §1 of `2026-10-03-concrete-compatibility-boundary.md`
Reviewed-by: prior bounded reviews cover frozen-source facts and earlier abstract closures only; compiler_referee reviewed the §8.1 trace including the positive unique-cast path; architect pre-write and bounded compiler_referee review covered the §8.2 conditional template, with two minor branch/assignment-qualification repairs closed by primary inspection; no runtime execution was verified, and the local-exactness/descriptor premises remain unproved
Implementation authority: none
Supersedes: none

## 1. Purpose and limits

The [concrete compatibility boundary note](2026-10-03-concrete-compatibility-boundary.md)
records the user's direction: Yulang has one inequality query `A <: B`, whose
solver dispatches by endpoint form. Variable-edge propagation may be
transitive; concrete resolution is local and may yield cast/adapter evidence,
whose success cannot be composed into a third concrete inequality.

This note records a finite closure theorem for a fixed finite **solver
transition system** suggested by frozen lower/upper replay. Its `VarEdge`,
`LowerPayload`, `UpperPayload`, replay-route, and comparison-task records are
internal algorithmic states for the same inequality solver, not separate
semantic judgments. A selected replay creates another `A <: B` work item and
does not rely on successful concrete-resolution outcomes as premises.

The theorem proves termination, leastness and finite derivation provenance for
the stated state transitions only. It does **not** prove that replay is
source-mandated, that the transition system preserves source acceptance, that
its resulting constraints are principal, or that generated resolution
evidence has an executable source location. Those remain open. No compiler
change or new language behavior is authorized.

## 2. Fixed input and candidate solver-state transitions

Fix:

- a finite variable set `V` and a finite set of internal directed variable
  edge records `E`;
- finite lower- and upper-payload identities `I_L` and `I_U`;
- for each lower payload `i`, a fixed endpoint term `A_i`; for each upper
  payload `u`, a fixed endpoint term `B_u`;
- a finite context carrier `C` retaining source identity, lexical binder
  identity, scope-guard information and every finite route coordinate that
  can affect movement or replay admission;
- finite transition relations `Move_L`, `Move_U`, `ReplayCtx`, and
  `ReplayRouteAdmitted`; and
- a finite endpoint-term graph. Transitions in this theorem do not unfold
  terms or allocate new endpoint terms.

A comparison task is still an inequality query `A <: B` with its originating
context and consumer identity. `LowerPayload(i,X,A,c)` and
`UpperPayload(u,X,B,c)` are internal indexes of unresolved comparison tasks
at a variable endpoint; they are not propositions that concrete comparisons
succeeded. `VarEdge(X,Y,e)` indexes a variable-to-variable inequality and its
propagation context. Original source tasks and replay-generated tasks retain
distinct identities and derivation links.

`Move_L(c,e,c')` and `Move_U(c,e,c')` indicate that the corresponding
payload record may move across an internal variable edge with resulting
context `c'`. `ReplayCtx(c_L,c_U,X,c_R)` and
`ReplayRouteAdmitted(i,u,X,c_L,c_U,c_R)` are finite guards on a solver
transition. They are not source relations: their validity and completeness
must be derived from the source inequality-generation and replay rules.
Endpoint, weight or context values that can affect the transition must occur
in the finite state key or in these finite relations. This abstraction does
not assert that frozen `ConstraintWeights` or the full route machinery are
finite in this model.

The monotone candidate state transitions are:

```text
VarEdge(X,Y,e) + LowerPayload(i,X,A,c) + Move_L(c,e,c')
    -> LowerPayload(i,Y,A,c')

VarEdge(X,Y,e) + UpperPayload(u,Y,B,c) + Move_U(c,e,c')
    -> UpperPayload(u,X,B,c')

LowerPayload(i,X,A,c_L) + UpperPayload(u,X,B,c_U)
    + ReplayCtx(c_L,c_U,X,c_R)
    + ReplayRouteAdmitted(i,u,X,c_L,c_U,c_R)
    -> ComparisonTask(A <: B, c_R; parents i,u,X)
```

The final task enters the same endpoint-dependent inequality solver as any
source task. The rule does not claim that every lower/upper pair must replay;
that is what `ReplayRouteAdmitted` stands for in this fixed transition model,
and its source meaning remains unproved. The transition does not consume or
compose success evidence from earlier concrete comparison tasks. Structural
child tasks, adapter realization, and incremental row-residual routes are
outside this fixed-payload closure theorem and need their own finite transition
and source-preservation proofs.

## 3. Finite least-closure theorem

Let `S_0` be any finite set of input internal states. Let `R_Gamma` be the
closure operator that adds every conclusion of the three transitions in §2
using fixed finite background transition facts `Gamma` until no new state can
be added. Context transitions may be nondeterministic, but each relation,
including `ReplayRouteAdmitted`, is finite.

**Theorem (finite fixed-graph solver closure).** The closure process terminates
after finitely many state insertions and produces a unique least transition-
closed state set containing `S_0`. Every produced payload or comparison task
has a finite derivation from `S_0` and `Gamma` (the fixed `VarEdge`, `Move_L`,
`Move_U`, `ReplayCtx`, and `ReplayRouteAdmitted` facts). Conversely, every
state with such a finite derivation is present in the result. Any fair
worklist schedule reaches the same least closed set.

**Proof.** The state universe is finite. If `n_E = |E|`, `n_L = |I_L|`,
`n_U = |I_U|`, `n_V = |V|` and `n_C = |C|`, then there are at most

```text
n_E
+ n_V (n_L + n_U) n_C
+ n_V n_L n_U n_C
```

canonical variable-edge, propagated-payload and replay-task states,
respectively. Endpoint terms are fixed by payload identity. A replay task's
key contains its single result context; its lower and upper parent contexts
are premises in the finite provenance graph, not additional key coordinates.
This quotient is sound only if `c_R` retains all behaviorally relevant guard,
weight and resolution context; if distinct route witnesses with the same key
can generate different future tasks, the key must retain another coordinate.
The transitions only add states, so each insertion strictly increases a finite
set and saturation terminates. Induction on insertion round proves every
inserted state has a finite derivation. Induction on the height of a finite
transition derivation proves completeness. The result is the least fixed point
of the monotone consequence operator, independent of fair worklist order. A
cyclic variable graph can produce alternate derivations but cannot create
infinitely many states when canonical keys and contexts remain inside the
fixed finite universe. ∎

This state bound does not count derivation paths. Keep a finite provenance
graph keyed by canonical states and immediate transition premises; do not
allocate a fresh identity for every traversal of a cycle. If the system needs
path-specific guard behavior, that behavior must be represented in `C` and
proved equivalent for states sharing a key.

### 3.1 Source-preservation bridge remains open

Finite closure proves neither soundness nor completeness for source typing.
For each solver transition, a separate proof must show that it preserves the
source-generated inequality problem under one shared assignment, in both
directions where needed. In particular, the proof must establish which replay
tasks are mandatory, prove no source-required task is lost when a route is
suppressed, and show no extra rejecting task is introduced. Defining source
acceptance to require every generated replay task would assume the result to
be proved rather than establish the bridge.

## 4. No transitive composition of concrete resolution outcomes

A concrete comparison task `A <: B` is resolved locally by the endpoint-
dependent solver and may yield check, cast, adapter-selection, or realization
evidence. The finite transition theorem does not turn those outcomes into
variable edges or premises for later comparisons. In particular, it has no
rule

```text
success(A <: B) + success(B <: C) -> success(A <: C)
```

The user's optional-Record observations refute that rule: both
`{foo?: string} <: {}` and `{}` `<:` `{foo?: int}` resolve successfully,
while `{foo?: string} <: {foo?: int}` resolves unsuccessfully. If the solver's
internal replay route creates the latter comparison task from lower/upper
records, it is a fresh inequality query with its own parents and context; its
source justification is independent of the two earlier resolution successes.

The suspended-obligation example remains a warning against treating `A <: X`
and `X <: B` as independent concrete checks and assuming that their success
justifies a new `A <: B` task. It does not prohibit variable-edge propagation
or rule out source-justified replay. It requires replay admission and task
conservation to be proved without appealing to concrete-result transitivity.

## 5. Why the finiteness premises matter

Fixed finite state keys are essential. If the context records an unbounded
edge history, even a one-node cycle can generate infinitely many contexts:

```text
VarEdge(X,X,e), LowerPayload(i,X,A,c)
    -> LowerPayload(i,X,A,append(c,e))
    -> LowerPayload(i,X,A,append(append(c,e),e))
    ⇒ …
```

Likewise, if each replay traversal allocates a fresh boundary identity, a
single lower/upper pair can yield infinitely many distinct replay states.
These examples refute unconditional finiteness for those encodings; they do
not show that the successor source judgment requires either encoding.

This theorem also excludes dynamically generated variables, structural
decomposition that creates child bounds, changing equality quotients,
extrusion, recursive cast instantiation, generalization, freshening and SCC
intrusion. Each extension needs a finite-state and preservation argument of
its own. The full type-inference replacement objective remains active.

## 6. Frozen-source correspondence and unresolved bridge

At frozen commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`:

- `crates/infer/src/constraints/machine/propagate.rs::step_subtype` maps the
  already-normalized comparison orientations as follows:

  | Input comparison | Stored bound |
  |---|---|
  | `A <: X` | lower payload `A` owned by `X` |
  | `X <: B` | upper payload `B` owned by `X` |
  | `X <: Y`, `X != Y` | lower payload `X` owned by `Y`, and upper payload `Y` owned by `X` |

  Each ordinary insertion retains the source constraint and its weights as
  derivation data. Earlier bottom/top, stack, union and intersection handling
  can normalize or split a comparison before this variable dispatch; identical
  variables return without adding bounds. Effect-row upper bounds use a
  specialized route.
- `crates/infer/src/constraints/machine/bounds.rs::cpk_lower_bound_replay_actions`
  prepares routes from a new lower bound to existing uppers;
  `cpk_upper_bound_replay_actions` does the symmetric work. Eligible replay
  actions retain `BinaryReplayDerivation { pivot, lower, upper, rule }` and
  replay claim parents; routing can enqueue, deduplicate, or prefilter a route.
- These builders do not unconditionally enqueue every stored same-pivot pair.
  They require a prepared `pair_replay` route; lower insertion can instead use
  an incremental row-reduction route. The ordinary pair's weights compose in
  lower-to-upper order in either insertion order. The selected action can
  still be classified as ordinary, trivial, duplicate or evidence-only before
  worklist application. This source route motivates an explicit
  `ReplayAdmissible` premise; its proof-store admission policy is not itself
  successor language semantics. Incremental row residuals are outside the
  fixed-endpoint closure fragment above.
- `proof/mod.rs::compose_prepared_replay_route` further filters ordinary-pair
  parents using live coverage by each upper claim root. With a concrete lower
  endpoint and no incremental row route, no upper parents or any uncovered
  upper parent requires generic replay; when all existing upper parents are
  covered, the generic pair is suppressed. With a variable lower endpoint,
  covered parents remain in the pair unless a selected incremental route
  handles their representative claim. This is frozen proof-routing policy,
  not an approved source rule. A successor conservation proof must establish
  either why no source replay obligation is required or where any required
  obligation remains represented; it cannot count endpoint equality or
  successful concrete-resolution composition as that evidence.
- A semantically new lower insertion that reaches row routing at the same
  variable owner runs `row_effect.rs::unweighted_row_reduction_routes_for_new_lower`
  before ordinary replay preparation (`machine/bounds.rs::add_lower_bound`).
  Each unprocessed row state emits a route: a match generates child row-item
  constraints, advances its residual and routes against the original upper;
  an unmatched/ineligible lower routes against the current reduced upper.
  Incremental application retains the lower weights. This is operational
  evidence for a possible per-lower row derivation replacing the generic pair,
  not evidence that an inequality has been successfully resolved. `processed_lower_records`
  records visitation; it is not a success certificate, and the composer does
  not consult it. Guards, context and conversion-use correspondence remain
  unproved.
- That owner-local explanation is not universal. Frozen
  `constraints/tests/case_02.rs::unweighted_row_upper_cross_source_replay_inherits_covered_lineage`
  creates a covered row claim on `alpha`, derives a covered upper on `beta`
  through Function return-effect replay, and asserts that `beta` owns no row
  reduction state. A later concrete lower on `beta` gets no generic replay
  against that inherited covered upper and does not contaminate the residual.
  The case demonstrates cross-source inherited coverage without a local beta
  row router; it does not by itself prove the lower is transported to alpha
  and discharged there. Exact conservation therefore has to span variable
  edges, inherited claim lineage and row-state ownership, not just the local
  insertion call.
- A bounded call-path trace reconstructs that route for this fixture. The
  ordinary `beta <: alpha` upper on `beta` still admits a lower/upper replay
  for `late_family <: alpha`; the distinct inherited covered upper on
  `beta` for the residual suppresses its own generic pair. The new lower on
  `alpha` then enters alpha's row state, matches against `original_items`, and
  routes to the original `{f | residual}` upper while leaving the reduced
  residual materialization unchanged. The test directly asserts the beta
  suppression and lack of residual `f`, but does not assert this later alpha
  replay or its row derivation; those links are reconstructed from the frozen
  call path. This fixture uses constructor heads with no arguments, so the
  row-item match generates no child-argument subtype obligations. It is a
  useful concrete trace, not a general conservation theorem.
- The restricted upstream-spine lemma is closed at this frozen operational
  scope. An ordinary source comparison `Var(v_i) <: Var(v_{i-1})` installs both the lower
  `v_i` on `v_{i-1}` and the mirrored upper `v_{i-1}` on `v_i`. At each hop,
  insertion of the same already-normalized positive endpoint `C` must be
  semantically new and reach replay preparation. `C`'s outer head must not be
  `Bot`, `Var`, `Stack`, `NonSubtract` or `Union`: `step_subtype` exits or
  rewrites those before the `Neg::Var` branch, so exact endpoint preservation
  would otherwise be false. The projected mirrored upper record must have
  endpoint `Var(v_{i-1})`; its prepared claim entries must be empty or include
  an uncovered coverage root at preparation time. CPK then retains a generic
  pair with `C` as its lower endpoint. With empty weights, identity-preserving
  extrusion, successful preparation/admission, and eventual processing of
  that canonical pair without terminal failure, `C` is inserted on
  `v_{i-1}`. Repetition requires a semantically new insertion at each next
  hop with its mirrored upper already eligible then, or independent evidence
  that this exact replay obligation was already admitted and processed.
  Equivalent lower insertion returns before replay; duplicate canonical replay
  merges evidence without enqueueing another work item. This is a frozen
  operational lemma, not successor semantics. A fully covered connecting
  upper can stop concrete transport; mixed coverage carries only uncovered
  roots on the retained pair. The environment-gated evidence-only replay path
  applies only to Var-to-Var endpoints, not this concrete-to-variable pair.
  A raw multi-hop bound test does not install mirrored uppers, while the
  neighboring `var_var_replay_materializes_transitive_edges` test installs
  source subtype edges and checks an empty-weight `int` lower at the far end;
  that fixture supports the normalized-constructor case, not the broader
  lemma. Cycles, weights, filters, variable-changing extrusion, guards and
  consumer conversion remain outside this fragment.
- `crates/infer/src/constraints/tests/case_01.rs::var_bound_addition_replays_against_opposite_bounds_with_union_weights`
  asserts a composed-weight lower/upper endpoint constraint. The neighboring
  `var_var_replay_materializes_transitive_edges` case asserts propagation of
  variable edges and a concrete lower bound along the chain.

These are source and test-contract evidence for the frozen operational route,
not proof that candidate lower/upper payload records or replay-route admission
are successor semantics.
The frozen machinery additionally has constraint weights, route admission,
extrusion, incomplete/evidence-only replay and detailed provenance rules that
the finite theorem abstracts away. No tests were executed for this note.

Before extending structural residual factorization, close the following
successor obligations:

1. Prove which internal endpoint transitions preserve the source-generated
   inequality ledger in both directions, including which replay tasks are
   required and which can be represented by row/residual routes.
2. Preserve each task's context, guard and shared witness/evidence references
   through aliases, structural children, replay and variable-edge propagation.
3. Show that a failed generated replay cannot reject a source problem unless
   it is a proved consequence of the original inequalities.
4. Define context/guard combination and prove equal canonical keys have equal
   guard and conversion-selection behavior.
5. Bridge original source boundaries and replay derivations to specialization
   queries without losing either logical provenance or the eventual execution
   site for a selected conversion.
6. Extend the finite carrier through recursive structural children, symbolic
   effects, generalization, freshening and SCC intrusion.

The restricted eligible-edge spine is supported for normalized constructor
payloads and refined above with an outer-head and work-item premise. Next
account for covered-only connecting edges, mixed coverage roots and cycles in
a graph-wide conservation theorem: each suppressed source-required
lower/upper interaction must have an identified row derivation or transported
obligation. Distinguish route creation, row children, residual queries,
worklist completion and consumer conversion; neither local row-state
visitation nor transitivity of concrete resolution outcomes can stand in for
those links.

No source syntax, acceptance behavior, cast-selection policy, runtime adapter
rule, resource limit, or implementation representation is selected here.

## 7. Source-meaning obstruction and a conditional port hypothesis

A bounded architecture audit identified a necessary distinction for any
source-preservation proof. Suppose a lower and upper payload were interpreted
only as two independent suspended local checks:

```text
The unresolved inequality A <: X is stored with lower payload A at X.
The unresolved inequality X <: B is stored with upper payload B at X.
```

For `A = {foo?: string}`, `X = {}`, and `B = {foo?: int}`, both suspended
inequalities resolve at the chosen `X = {}` endpoints under the user's Oracle
observations, but a direct `A <: B` query fails. Thus those two independent
resolutions do not entail creation or success of a replay query. This does not
contradict the frozen Oracle route; it rules out using comparison-result
composition as its source justification.

One conditional explanation is to treat an inference variable as a
transparent interface port between producers and consumers. A lower payload
would retain a producer contract and its typed view at the port; an upper
payload would retain a consumer demand. Variable-bound transport would move
those contracts without inserting a conversion. If the port is transparent,
each admitted producer must safely reach each admitted consumer, so a
source-justified lower/upper replay may create a new `A <: B` task. That task
is resolved afresh by the same endpoint-dependent inequality solver. This can
explain replay without composing successful resolution evidence.

An actual source compatibility boundary might break transparent transport by
establishing a new consumer-facing contract, but need not emit a data
conversion. For example, a shape check could seal the exposed view to `{}`
while runtime preserves the original Record with its extra fields. Conversely,
a selected and emitted adapter could materialize a target-facing value. These
are separate questions: whether the source boundary starts a new typed
contract, and whether its runtime realization changes the value. Successful
resolution of an arbitrary inequality does not by itself establish such a
contract boundary; nor does an emitted adapter by itself explain which source
obligations are discharged. In schematic form:

```text
producer A → transparent X → consumer B
    requires a justified local A-to-B query

producer A → source boundary exposing {} → producer-view {} → consumer B
    keeps the two boundary queries separate; realization may retain or adapt data
```

The common inequality entry under consideration can dispatch each justified
query to Record checks, nominal-cast resolution or adapter resolution while
retaining their evidence as distinct derivations. Its result must distinguish
a successful check from selected conversion evidence and from an adapter
actually emitted. Source elaboration
must also say whether a particular check establishes a new consumer-facing
contract. The resolver cannot decide by itself whether a variable path is
transparent or whether a source operation created such a boundary. Execution
must preserve the producer view and place any selected conversion at the
correct consumer boundary; a check-only identity realization may still carry
a distinct typed view if the source contract requires it.

The frozen source provides a grounded transport example and a more precise
boundary locator. In `lowering/expr/block_local.rs::lower_local_binding_stmt`,
the local's public value is the body value; `connect_local_binding_annotation`
adds annotation constraints to that same value slot. During specialization,
`specialize2/task_solver/control.rs::local_let_binding_type` gives a
non-lambda local a fresh open variable, even when annotated. Its initializer
supplies lower information and a later consumer supplies upper information.
So a local annotation does not itself establish a converted port.

By contrast, `specialize2/task_solver.rs::apply_type` and
`consume_expr_value` record a function argument's actual/expected pair against
a materialized signature. When a registered cast is selected,
`specialize2/emit.rs::emit_expr_with_boundary` and
`boundary_expr_with_argument_contract` emit it at that argument expression
boundary through `cast_boundary_instance`. The emitted cast is evidence of
runtime conversion at that site, while the source comparison identity and
consumer view establish the logical boundary. This is frozen-source
characterization, not a successor rule: whether check-only Record boundaries
seal a typed view, and where optional-Record adapters execute, remain
unresolved.

This port account is an unverified hypothesis, not a source rule or approval.
Frozen bound replay establishes the operational route and its logical bound
parents; it does not establish that every eligible pair is a source-level
producer/consumer interaction. The hypothesis fails if substitution loses a
producer view, replay crosses a source boundary that seals a new
consumer-facing contract, or any generated rejecting pair lacks a
source-contract justification. Before adopting it,
trace supported producer-to-local-to-consumer and cast-at-consumer examples
through source generation, specialization and emission, including aliases,
multiple consumers and incompatible guards; then prove replay conservation in
both directions for the resulting source-bound and replay ledgers. A local
type annotation must not serve as the distinguishing example unless its
conversion behavior is separately established.

## 8. Partial frozen source-origin ledger

The ledger below is a bounded trace through the frozen implementation at the
commit named in §6. Its identities describe that implementation only; it does
not assert a successor representation.

| Stage | Evidence and identity | Established relation | Missing bridge |
|---|---|---|---|
| Literal producer | `lowering/expr/block_local.rs::lower_number` creates an expression and fresh `TypeVar`; `expr/constraints.rs::constrain_lower_with_origin` and `constrain_upper_with_origin` emit concrete-to-variable and variable-to-concrete constraints. | A source value can contribute concrete lower and upper payloads. | The origin is not a complete source-location identity for every payload. |
| Local binding and use | `lower_local_binding_stmt` keeps the initializer's value slot as the local public value. `lower_local_name` records a `RefId` targeting the local `DefId`; local references reuse that value unless scheme instantiation creates a fresh variable with witness routes. | Local transport and alias targets retain source binding identity. | Preservation of a semantic producer view across aliases, generalized uses and intrusion is unproved. |
| Local annotation | `connect_local_binding_annotation` reaches `annotation/constraints.rs::connect_value_detailed`, which constrains both directions between the annotation and the existing slot under annotation provenance. | Annotation contributes lower/upper constraints on the local value. | This alone does not show a new value slot, a runtime conversion, or a separately sealed consumer-facing contract. |
| Application demand | `make_source_app` allocates an `ApplicationArgument` `SourceBoundaryId` and source spans. `make_app_with_origins` relates the callee to a Function demand carrying the argument variable; Function decomposition derives the argument comparison. | The expected argument type has a source-owned application boundary and a derivation from the callee constraint. | The inferred constraint is not itself an executable cast placement. |
| Specialization local slot | `specialize2/task_solver/control.rs::local_let_binding_type` gives non-lambda locals a fresh `Type::OpenVar`; `block_type` consumes the initializer into it. `var_type` retrieves the stored slot for local uses. | A producer can flow through one specialization slot to multiple consumer expressions. | This reconstruction is separate from the inference `TypeVar` and does not itself prove which pairs are admissible for replay. |
| Materialized consumer | `consume_expr_value` constructs actual/expected materialized endpoints by looking up `TypeOccurrenceKey`s owned by the argument `ExprId`; each call submits its endpoint comparison to `constrain_materialized_subtype`. The type graph may discard equal endpoints or deduplicate equal semantic keys, merging positions and provenance. Surviving records carry endpoint types with `SpecializeSubtypeProvenanceRecordId`s and available source anchors. Endpoints may still contain `Type::OpenVar`. | Each consumption presents a local comparison obligation; concrete compatibility resolution happens only if solving exposes concrete endpoints. Repeated uses can retain separate consumers. | A submitted comparison does not guarantee a distinct stored graph constraint or provenance identity. Materialized record IDs do not map one-to-one to inference constraint or source-boundary IDs; provenance may be incomplete. |
| Repeated consumer accumulation | `add_expr_consumer` combines consumers for one `ExprId` using `Intersection`; each `consume_expr_value` call separately submits its particular expected endpoint comparison. Equal endpoints can be elided and equal semantic keys can share merged graph/provenance records. `finish` resolves one `SolvedExprType.actual` and one aggregate `consumer` for that expression. | The logical comparisons are submitted per consumption, while the solved expression view may represent several consumers together. | There is no direct identity from a replayed lower/upper pair to one member check or to the aggregate solved view. A one-consumer argument is only a narrower case, not a general conservation proof. |
| Inference replay | `step_subtype` stores variable-edge and bound records. `cpk_lower_bound_replay_actions` / `cpk_upper_bound_replay_actions` pair same-pivot records; `BinaryReplayDerivation` retains the pivot plus both `BoundRecordId`s. | Frozen inference explicitly retains the logical replay parents. | Those parents do not identify where a selected runtime conversion executes. |
| Specialization replay | `TypeGraph::constrain_open_var_bound_pair` adds `OpenVarBound { parents }` with lower-side and upper-side positions from separate specialization records. | Specialization has a second replay route with whatever parent provenance is available. | Its record IDs are not the inference replay IDs; this carrier has no explicit pivot field, and some routes have incomplete provenance. |
| Cast emission | `emit_expr_with_boundary` wraps an application argument; `wrap_expr_boundary` reads `SolvedExprType.actual` and `consumer`; `boundary_expr_with_argument_contract` selects through `cast_boundary_instance` using those solved endpoints and emits an instance application around the argument expression. | A registered nominal cast can execute at the consuming argument. | Selection is endpoint/rule based, not keyed by the inference binary-replay identity. When consumers accumulated, the emitter sees their aggregate rather than a selected individual check. The exact discharged-constraint-to-emitted-cast link is absent from this trace. |

The frozen emitter also has an identity-style Record path: when
`same_record_boundary_shape` finds equal field counts and names,
`ensure_emitted_value_with_argument_contract` keeps the expression and changes
its computation metadata to the expected type. Separately, supported generic
`RecordFields` coercion can lower to a runtime alias. These paths show why a
consumer-facing typed view and a data adapter cannot share one evidence bit.
They do not establish that a check-only Record boundary seals transport or
that it discharges a later bound replay. The frozen specialization Record
branch checks required-field presence and matching child types, but does not
settle optional-Record runtime realization.

Accordingly, frozen source evidence currently connects source origins to
inference bounds, connects replay to its two logical parents, reconstructs
materialized consumer checks with separate provenance, and places nominal
casts at argument expressions. It does **not** provide a single identity chain
from an original source boundary through bound replay to the emitted
conversion, or a proof that the conversion discharges exactly that replay.
The cross-stage conservation relation remains the proof obligation, but the
current evidence supports a smaller first subgate than a universal identity
chain.

### 8.1 Candidate subgate: one ordinary application argument

The frozen ordinary-cast characterization provides a concrete starting
fixture at
`crates/infer/src/lowering/tests/ordinary_cast_characterization.rs::live_application_cast_diagnostics_follow_zero_one_two_cardinality`:

```yu
cast(x: int): bool = false
my f(x: bool): bool = x
f(42)
```

The frozen test contract already establishes one inference-side witness:
without a cast it reports `int -> bool` as `OneSidedReplayPair`, owned by the
`f(42)` application boundary, with related source sites `42` and `f`; the
provenance test classifies the one replay parent as the required upper. Adding
one cast removes the error, while two candidates produce an ambiguity. This
is exact fixture evidence for that error/eligibility path, not a general
source-conservation theorem. The lowering test does not itself run
specialization; the source path from the same argument endpoints to emitted
cast application is traced below.

The source lowerer allocates an application-argument boundary, relates the
callee to a Function demand carrying the argument value variable, and derives
an argument comparison through Function decomposition. Inference stores the
literal's concrete lower and upper payloads on that variable and may generate
a selected same-pivot replay. Specialization separately materializes the
argument's actual/expected pair from the known parameter type; the emitter
then selects any cast from the resolved actual and consumer endpoints and
wraps the argument expression. The replay identity is not passed to cast
selection. This is a pair of connected source paths, not proof of a conserved
replay identity.

For this fixed shape, one monomorphic callee scheme instantiation gives the
callee slot `C` its known Function lower view. The argument/replay endpoint
trace is:

```text
callee slot C:         Fun(bool, ..., result) <: C
application demand:   C <: Fun(X, ..., result)
callee-pivot replay:  Fun(bool, ..., result) <: Fun(X, ..., result)
Function argument:    X <: bool                 (contravariant child)
literal value slot X: int <: X, X <: int
argument replay:      int <: bool               (lower int, upper bool at X)
```

The existing missing-cast expectation and provenance assertion identify that
`int <: bool` replay with the `ApplicationArgument` boundary and the `42`/`f`
source sites. This gives one concrete witness that the replay task is generated
from the bound records and is surfaced at the consuming call. It does not
compose the successes of `int <: X` and `X <: bool`: the endpoints remain
variable-bound payloads until a fresh `int <: bool` task is resolved. In
specialization, `apply_type` obtains the known parameter `bool`,
`consume_expr_value` obtains literal actual `int` and submits that ordered pair,
and the emitter looks up the cast from the solved actual/consumer pair at the
argument expression. This establishes endpoint correspondence in this fixed
source shape by source-path inspection, but not equality of inference and
specialization derivation identities or a runtime result.

For the unique-cast variant in the same fixture, the positive specialization
path is direct under the one-consumer, literal-leaf assumptions:

1. `apply_type` obtains the known callee Function parts and calls
   `consume_expr_value(argument, bool)` for a pure argument effect.
2. The literal's actual type is `int`; `consume_expr_value` records actual
   `int`, consumer `bool`, and submits that materialized inequality.
3. `apply_type` also submits a callee comparison. For this closed
   non-Record signature, `callee_arg_shape_from_actual` keeps the expected
   argument `bool`. Inference represents an ordinary annotated parameter's
   argument effect as `Neg::Bot`, which specialization materializes as
   `Never`; the pure apply path sets the target argument effect to
   `EffectRow([])`. A source trace through annotation connection, SCC
   compaction and scheme publication derives the stored scheme with no
   quantifiers, role predicates, recursive bounds or stack quantifiers and
   predicate `Fun(bool, Never, Never, bool)`. The diagnostic fixture does not
   directly assert this scheme. In the actual TaskSolver variable path,
   principal inference materialization preserves the negative argument
   effect as `Never` but materializes positive bottom return effect as
   `EffectRow([])`. Thus the callee type is
   `Fun(bool, Never, EffectRow([]), bool)`. The intended query must be
   re-derived from the user's coupled Function inequality while keeping value
   `Never`, empty effect row, and polarized solver bottom distinct. Frozen
   specialization currently reaches success by
   independent Function decomposition and a non-fixed-head fallback for
   `EffectRow([]) <: Never`; this is characterization of the old
   implementation, not the semantic justification for the intended rule.
   The scheme derivation follows frozen commit
   `a58eefc31e22141574b6f20c6a5748151c6d79f1`: builtin annotations add both
   bounds (`infer/src/annotation/constraints.rs:124–137,303–308`); ordinary
   parameter effect uses `Neg::Bot` (`infer/src/lowering/expr/lambda.rs:1344–1353`);
   the public lambda is assembled from the annotated parameter and body
   (`infer/src/lowering/expr/lambda.rs:946–975`); compact simplification
   removes one-polarity slots and exact opposite co-occurrences
   (`infer/src/compact/analysis/mod.rs:41–57,163–201`,
   `infer/src/compact/analysis/occurrence/mod.rs:359–397`); SCC publication
   stores the finalized scheme (`infer/src/analysis/session/instantiate.rs:19–82`,
   `infer/src/generalize/finalize.rs:16–25`). The two empty-bound
   representations resolve differently in principal materialization:
   `specialize/src/types/setup.rs:37`,
   `specialize/src/types/materialize.rs:68,139,276–279`. Function child
   generation and fallback acceptance are in
   `specialize/src/specialize2/type_graph.rs:593–611,886–894,978–992`.
4. `finish` resolves the literal's actual/consumer pair. Emission of the
   application argument wraps the literal at that consumer boundary.
5. With exactly one `int -> bool` rule in the arena,
   `boundary_expr_with_argument_contract` obtains that rule through
   `direct_cast_rule` and emits `Apply(InstanceRef(cast), argument)`.

The bounded two-lane ledger for this fixture is now explicit:

| Source/inference task | Specialization task/evidence | Relation in this fixture |
|---|---|---|
| The application stores the callee Function demand with argument slot `X`; the known callee Function lower view and that demand prepare `Fun(bool, ...) <: Fun(X, ...)`. | TaskSolver submits the callee-value-to-callee-consumer Function inequality. | Its intended success still needs kind- and polarity-sensitive derivation from the coupled Function inequality. The frozen separate-child/fallback behavior is historical characterization only. |
| Function decomposition gives the argument bound `X <: bool`; the literal contributes `int <: X` and `X <: int`. | `consume_expr_value(argument, bool)` submits the consumer inequality `int <: bool`. | The application boundary and ordered concrete endpoints agree. At inference, `int <: int` is reflexive; the selected nontrivial lower/upper replay is `int <: bool`. |
| The selected replay is owned by the `ApplicationArgument` source boundary and reports the literal/callee sites. | The argument actual/consumer pair carries the expression occurrence and application argument contract. A unique cast lookup emits the cast application around the literal. | This is endpoint/boundary correspondence, not replay-ID identity. The conversion is evidence/realization of the local concrete inequality; neither earlier bound comparison's success is composed to establish it. |
| The application source obligation is still `int <: bool`; the registered cast declaration separately supplies the candidate evidence. | `TypeGraph::constrain_direct_cast` instantiates the single `int -> bool` cast scheme and submits it against `Fun(int, bool)`. The source-derived cast predicate is `Fun(int, Never, Never, bool)`; principal materialization gives `Fun(int, Never, EffectRow([]), bool)`, while the expected signature is `Fun(int, EffectRow([]), EffectRow([]), bool)`. Its intended derivation must preserve value/effect kinds and polarized endpoints; this source trace does not establish that derivation. Frozen independent-child/fallback behavior is historical characterization only. Emission creates the cast instance at `Fun(int, EffectRow([]), EffectRow([]), bool)`; `solve_def_body` specializes the lambda with that signature, making body/definition checks reflexive for this fixture. | These are resolver-local witness and instance checks attached to resolving the concrete query, not a separate cast relation. Under the one-candidate scheme, they add no rejection in the frozen implementation. They do not compose prior concrete successes to establish `int <: bool`; that query is still resolved directly. |

For this fixed fixture, source-to-specialization direction has a concrete
inference replay witness and a separately traced materialized query with the
same ordered endpoints and consumer boundary. In the reverse direction, the
application's nominal argument query is that same `int <: bool` pair; the
separate callee query is an intended instance of the coupled effect-lifting
rule whose kind/polarity derivation remains open. Cast-candidate
signature and body checks remain resolver-local subqueries attached to
resolution evidence; their fixed-fixture source trace does not establish the
intended effect-lifting derivation. The
operational crosswalk still does not prove a general source obligation
theorem, guard/witness conservation, general replay completeness, or runtime
execution.

The resolver-local path is `TypeGraph::constrain_direct_cast`, followed by
`Specializer::cast_boundary_instance` / `ensure_def_instance`, then
`drain_pending_instances` calling `TaskSolver::solve_def_body`. The selected
cast lambda is specialized with its pure `Fun(int, bool)` signature; its
literal `false` body and matching definition boundary produce equal bool and
Function endpoints, which the weighted-subtype interner omits reflexively.
The candidate signature check is still a fresh inequality under the same
endpoint-dependent solver. Its intended explanation is effect lifting, not
independent Function-field decomposition; the latter and its
`EffectRow([]) <: Never` fallback remain frozen characterization.

This is a source-code path derivation, not an executed end-to-end witness. The
lowering fixture separately asserts that one cast candidate avoids the
missing-cast error. Neither path sends the inference replay identity to the
emitter; their link is the ordered `int <: bool` endpoints and the same
application argument boundary. The code evidence does not prove universal
replay conservation or the successor's cast policy.

The scheme and callee-query shape above are source-derived, but the diagnostic
fixture does not directly assert the stored `poly::Def.scheme`. The zero-cast
fixture is rejected during inference, so it is not an executed successful
specialization witness. Treat the unique-cast emission path as a source-path
derivation, not as an executed end-to-end specialization result.

A useful bounded lemma would fix one monomorphic closed Function signature,
one monomorphic callee scheme instantiation with no quantified variables, one
ordinary argument that is a literal leaf (with no block/tail subexpressions),
closed non-Record constructor endpoints, empty weights, one consumer, no
aliases or cycles, and no row reduction. Project explicitly to the argument
lane: `consume_expr_value` materializes the literal's actual/expected
comparison, while `apply_type` separately submits a callee Function check.
Record endpoints are excluded because `callee_arg_shape_from_actual` can
change the callee consumer to the actual Record shape; a later Record subgate
must retain that additional comparison. The source-derived scheme and
coupled effect-lifting rule account for the fixed non-Record fixture's
additional comparison. The fixture has no direct stored-scheme assertion and
no executed successful specialization witness; whole-application
conservation remains open until both inequality lanes and their evidence are
related in both directions.
A later extension to block arguments must likewise retain the separate root
and tail comparisons and their boundary correspondence. The remaining lemma
is a two-direction result for this source shape. Define the source obligation
from that application and parameter contract. Then prove or refute that it
corresponds exactly to the Function-derived argument task plus any mandatory
same-pivot replay: ordered endpoints must agree, the consumer must remain the
application boundary, and no extra rejecting inequality may be introduced.
Relate the one materialized specialization comparison to the emitter's one
actual/consumer pair. Treat nominal cast resolution only as a tagged outcome;
this lemma chooses no successor cast-selection policy.

This subgate deliberately does not require a single provenance ID to survive
all stages. Frozen Function-child specialization constraints can have empty
anchors or incomplete parent positions, while endpoint deduplication,
consumer aggregation, and endpoint-based emission also merge identities.
Therefore any successful proof must state the correspondence relation it
uses, rather than infer identity preservation from matching endpoint pairs.
This fragment can establish neither covered-row conservation nor full source
comparison completeness. A successor may choose a different topology, but it
must prove the same logical and execution correspondence before using replay
to justify a local resolver result.

### 8.2 Conditional boundary/witness conservation template

This is a candidate proof obligation for the fixed one-consumer `f(42)` lane,
not an established theorem or a source cast policy. It relates source roots
and solver work by their obligations and contexts, not by equality of
inference and specialization IDs. Write an original source task as

```text
j = (origin, ordered endpoints A <: B, lexical/symbolic context Γ, consumer u)
```

A correspondence `ρ` maps each solver task to an original source task, or to
a subtask of a particular source-resolution branch. It must preserve the
ordered endpoints, context, symbolic coordinates, consumer and branch
ownership. Endpoint equality alone does not establish `ρ`.

The application contributes distinct source roots. In the fixed fixture they
include:

```text
j_arg       int <: bool                  application argument boundary
j_callee    Fun(bool, Ncal, Pcal, bool)
              <: Fun(bool, Ndemand, Pdemand, bool)
```

The admitted resolution branch for `j_arg` then has these branch-specific
subtasks:

```text
j_candidate(k) Fun(int, Ncast, Pcast, bool)
                 <: Fun(int, Nrequired, Prequired, bool)
j_body(k)   selected candidate-k body-instance checks within that branch
```

`j_callee` is nonreflexive and is rooted in the application contract; it is
not a child of nominal `int <: bool` absent a source derivation. `j_arg` is
owned by the application argument boundary. `j_candidate(k)` and `j_body(k)`
belong to an admitted cast-resolution branch. The fixed fixture's
single-matching-candidate condition can use one branch; it does not require
conjoining failed or unselected candidates in a general resolver. Only
independently established equal endpoints, such as the fixed selected-body
checks, may be discharged by reflexivity.

Each nonreflexive Function task requires a joint descriptor witness of the
form below. This is metatheoretic proof notation for views into already
existing inequality, coupled-interface, and directed-weight/subtraction
evidence. It is not a proposed solver record, separately allocated witness
bundle, or second correspondence/attachment/provenance mechanism. Each item
must be derived from the existing evidence for this comparison; if a required
fact cannot be derived, identify that exact gap before proposing any new
representation.

```text
W_j = (
  value-endpoint evidence,
  shared abstract-component correspondence θ,
  contravariant meet or attachment-descriptor normalization N⁻,
  covariant flat normalization and transport N⁺,
  concrete matches and dependent type constraints M,
  witnessed partial reverse-addition steps S (a proof projection of existing
    subtraction history, not new state),
  correlated residual obligations R,
  original terms, context, symbolic constraints and consumer ownership Ψ
)
```

`N⁻` distinguishes an abstract-only row normalized to its meet `[]` from a
concrete-bearing attachment descriptor. `S` states the proof obligation that
an existing source-supported accumulation and its existing subtraction
evidence identify a contribution and justify reversing it. It is not a total
subtraction operation and does not introduce attachment state. `N⁺` states
the preservation obligation for shared identities and correlations through
canonical flat normalization; those identities remain in existing
constraints/evidence. `Never`, `Any`, polarized sentinels, and the frozen
`EffectRow([]) <: Never` fallback provide no descriptor elaboration.
Any effect-position spelling that does not yet have an admitted descriptor
interpretation remains an explicit open premise.

For a source resolution rule `r`, the required **local exactness** premise is
independent of which transitions an implementation happens to generate:

```text
root evidence for j is admitted under η
  iff
there is a source-admitted alternative b such that
  the permitted child obligations Child(r,j,b) are admitted under η,
  and the rule's constraints/context/ownership transport holds under η
```

For a fixed candidate branch, its candidate signature and selected-instance
checks form that branch's child family. For general cast resolution, the
source-defined alternatives and selection policy must be supplied; a failed
unselected branch cannot reject the root by default. The current documents
do not prove local exactness for the application rule, literal-slot
transport, either nonreflexive Function descriptor check, candidate checking,
or selected-instance checking.

**Conditional fixed-lane result.** If (i) every source root and required
child task is covered by `ρ`, (ii) each used rule satisfies local exactness,
(iii) one shared assignment `η` satisfies the shared source-root context
constraints and every selected/active branch's transported constraints,
while constraints from unselected alternatives remain guarded rather than
conjoined, (iv) all
source-admitted alternatives and their branch ownership are represented,
and (v) processing is finite and fair, then source-root resolution and solver
resolution coincide up to the stage-local representation recorded by `ρ`.
Forward completeness expands each admitted source witness using local
exactness. Reverse soundness reconstructs a source witness through the reverse
implication of local exactness. This does not require replay-ID identity or
allow concrete-success composition. It remains a conditional template until
the premises, especially the two Function witnesses' kinded descriptor
elaboration and local exactness, are proved.

This lane does not justify general same-pivot replay. The first broader gate
is an independent source-admission rule for each replay; optional Record
successes on either side of `{}` do not authorize their composite comparison.
Guard inheritance, row/residual alternatives, schemes, aliases, and
occurrence-specific multiple-consumer ownership need corresponding
source-preserving context and branch mappings. This template narrows those
proof obligations without closing them.
