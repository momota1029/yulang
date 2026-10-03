# One inequality judgment with endpoint-dependent resolution

Status: Draft; records user-directed single-inequality, Function effect-descriptor, and mixed-row directions; merge semantics, complete resolver semantics, and implementation authority remain open
Date: 2026-10-03
Scope: one inequality judgment with endpoint-dependent solving and local concrete cast/adaptation resolution
Approved-by: user for the single inequality judgment, endpoint-dependent resolution direction, concrete-success non-composition, polarity-indexed Function effect descriptors, mixed abstract/concrete type components, canonical-flat covariant rows, abstract-only contravariant meet normalization, and concrete-bearing attachment descriptors for witnessed partial reverse-addition; component classification, co-occurrence consolidation, the component-to-existing-carrier bridge, proof that existing evidence licenses a particular reversal, replay eligibility, and implementation remain open
Reviewed-by: prior compiler_referee/spec_auditor reviews cover frozen-source facts and earlier Record/replay candidates; 2026-10-03 compiler-referee delta reviews of the Function descriptor and mixed-row candidate found no blocking/major issues, with minor wording repairs closed; general-component, polarity-specific reverse-addition, and abstract-only contra-meet wording delta reviews found no blocking/major/minor issue; the full witness calculus remains unreviewed
Implementation authority: none
Supersedes: none; narrows source applicability of structural relation candidates without invalidating their fragment theorems

## 1. Governing semantic decision

The user clarified on 2026-10-03 that Yulang has one basic inequality query,
`A <: B`. Its solver dispatches by endpoint form; this is not a semantic split
into a `Bound` relation followed by a `Compat` relation and a separate cast
relation:

1. `X <: Y` may be stored as a variable edge and propagated transitively.
2. `A <: X` or `X <: B` may be stored as oriented lower/upper payloads of the
   same inequality and propagated or replayed as needed.
3. Concrete `A <: B` is resolved locally. Endpoint-directed resolution may
   structurally decompose it, check optional Record fields, resolve a
   registered cast, or select an adapter. A selected cast or adapter is
   evidence/realization produced while resolving this inequality, not a
   separate semantic relation.

Internal variable edges, lower/upper records, replay routes, phases, and
evidence structures are compatible with this direction. They are solver
machinery for the one inequality judgment, not independent source judgments.
The overall solver is not a transitive concrete subtyping relation: variable
edge propagation may use transitivity, while success of one concrete
resolution cannot be composed with another concrete success to establish a
third inequality.

### User-directed Function effect comparison

Function effect ports are not independent general-`Type` subtype checks. The
user directs the endpoint-dependent `A <: B` solver to represent and resolve
the two effect polarities through effect descriptors:

| Function effect position | Descriptor contents |
|---|---|
| Contravariant | abstract type components plus concrete type components; eligible concrete components may be subtracted, so needed structure may be retained |
| Covariant | abstract type components plus concrete type components in canonical flat form |

Effect expressions need no privileged `body ; tail` syntax. The candidate
representation is polarity-indexed:

```text
E⁺ ::= flat-row{abstract-type-component Aᵢ, concrete-type-component Cⱼ}
E⁻ ::= AbstractMeet{Aᵢ, …, Aₙ}
     | AttachedDescriptor{abstract components, concrete components, attachments}
```

Here `attachments` means references/views into the existing occurrence,
ownership, and directed-weight evidence. It does not prescribe a second
attachment table or independently allocated provenance identity.

Effect variables are a typical abstract component, and concrete effect
records are typical concrete components; neither example exhausts its class.
The admitted interpretation determines the classification, which is not yet
defined as a new source type constructor. These are candidate internal forms,
not syntax. Covariant rows always normalize to a canonical flat form; any
correlation, co-occurrence, original-term identity, or ownership needed after
flattening lives in constraints/evidence, not in a covariant row tree. Thus
`[['a, write], read]` normalizes to `['a, write, read]`, and even a distinct
abstract component in a source nested row does not preserve that tree on the
covariant side.

When a contravariant row contains only abstract components, it may normalize
to their meet, written `[]` (the abstract-component meet, not an empty-effect
value). A row containing any concrete component is not
that meet: it is an attachment-preserving descriptor for reverse addition.
Its structure is retained only as needed to identify how concrete
contributions attach to the abstract components and to one another. For
example, `['a, ['b, write], read]` may keep grouping needed to identify the
attachment to reverse; the correlation and source witnesses remain explicit
in evidence. Collecting common variables is an auxiliary view of abstract
components and does not replace general abstract components or equate
original terms. Co-occurrence consolidation remains distinct from witness
equality.

Contravariant handling is not a total subtraction algebra. “Reverse addition”
is currently only a possible conceptual reading of existing subtraction
evidence, not a new operation or evidence system. A reverse step is justified
only where existing evidence identifies the concrete contribution and its
attachment in the accumulated effect. The frozen directed-stack-weight spec
already carries scoped subtraction identities, ordered push/pop history,
family budgets, residual weights, and the row-split provenance needed by its
own subtraction rule. Do not add parallel attachment/provenance records under
new names. The successor must first show how a proposed reverse step is a
projection/reformulation of that existing evidence, or identify a concrete
missing fact that the existing evidence cannot express. Without that proof,
no reverse step is licensed.

For a concrete Function inequality, compare both descriptors jointly inside
the same inequality resolution. Do not introduce a new tuple of abstract
correspondence, family ownership, attachment, residual, and provenance
fields: the existing coupled interface candidate already carries the shared
assignment, source-owned family identities/incidence, `K,D`, and their
transport. Existing subtraction evidence remains the source for its scoped
push/pop and residual facts. The only additional local evidence needed here
is proof that the polarity-specific row views normalize/transport correctly
and that concrete matching preserves its dependent constraints. Any partial
reverse step must be entailed by the source-supported accumulation and
attachment represented in the existing carriers. If they do not entail that
fact, record the exact missing source fact before adding any representation.
Unmatched contributions remain in their existing correlated
relation/residual context. Neither normalization may silently identify
distinct original terms or detach a concrete component from its context.
No effect port is decomposed as an unrelated `Type` inequality, and the
result of one concrete Function comparison cannot be composed with another
concrete success to establish a third inequality.

The existing directed-stack-weight/effect-subtraction specification is prior
art, not successor authority: its exact `StackWeight`, `SubtractId`, `take(F)`,
`Common(L)`, `K ∩ Common(L)`, `L - J`, W-Mix, replay, and residual-hash-cons
rules must not be imported as successor semantics without the declarative
source proof already required by the effect-design gate. The reuse boundary is:

| Needed fact in a Function inequality | Existing carrier to reuse | Remaining proof question |
|---|---|---|
| Which handler boundary may consume a concrete contribution | Directed left-weight path and scoped `SubtractId` in the old calculus; source handler/activation relation in the coupled-interface candidate | Derive the successor eligibility condition and show the edge/path witness denotes it |
| What was consumed and what remains | Old row-head split `J = H ∩ Common(L)` and residual `L - J`; relational handler image and residual support projection | Prove the mapping from typed concrete row components to `J`, preserving dependent arguments and shared assignment; `H` here is the old calculus's concrete head set, not relational predicate `K` |
| Which symbolic family arguments remain coupled | Existing source-owned `g(o)`, occurrence incidence, shared `ν`, and symbolic `K,D` in the coupled relation | Show a Function effect component occurrence maps to those existing owners; do not add a duplicate ownership map |
| How constraints survive transformation | Existing replay / variance transport and relational reindexing laws | Prove covariant flat normalization and contravariant descriptor construction preserve the same solution fiber |

The genuinely new obligation is the bridge between Function effect-row
syntax/components and those existing carriers. A general abstract component
may denote an entire correlated row view, and a concrete component may
contribute multiple typed request occurrences. Thus neither maps one-to-one
to `g(o)`. The source elaboration must map a component to the appropriate
complete interface under the same `ν`, then identify the occurrence incidence
and directed-weight path/split that account for it. It must prove the old
subtraction evidence denotes the source-supported partial reversal when used
by the single `A <: B` resolver. The directed-weight specification alone does
not supply that theorem.

The coupled-interface candidate defines handler subtraction as residual
support of the full handler image, not set difference: a handled request may
be emitted again by its raw continuation, so the request can remain in the
outward support. The old row split's `L - J` residual is therefore not itself
the semantic proof that a concrete contribution disappears from outward
support. Whenever a proposed reverse step claims that a family/key disappears,
the bridge must establish the corresponding output-absence condition through
the full handler image. A reverse step that recovers some other source
accumulation must be justified by that source rule; it should not be forced
into handler subtraction. If this bridge follows from existing
occurrence/incidence and weight facts, no extra attachment/provenance datum is
needed. If not, identify the exact lost source fact before proposing a field.
Covariant flat-row normalization and the joint two-port Function rule remain
integration proofs; neither licenses a parallel row-subtraction algebra. No
new total cancellation algebra, shared-correspondence map, family-ownership
ledger, or parallel regional/attachment/provenance calculus is proposed.

The intended coupled cases remain:

```text
Fun(a, never, b, c) <: Fun(a, d, [b,d], c)
Fun(a, never, never, b) <: Fun(a, e, e, b)
```

The same target variable `d` remains one shared term across both target ports
under the existing assignment and ownership relation; the source contribution
`b` remains present in the output descriptor. There is
no independent `d <: never` obligation. For the second case, the intended
effect evidence connects target input `e` with target output `e`; whether the
two source `never` spellings elaborate to descriptors with no concrete
contributions is not yet defined. More generally, the descriptor elaboration
of `never` in these examples is open. It must not be obtained from a global
`Never`, `Any`, empty-row, or polarized-sentinel alias. The value-type
meanings of `never` and `Any` remain distinct from the effect descriptor
language; no lattice account is needed for this Function rule. The value
endpoints `a` and `c` remain part of this same Function resolution and its
retained family equations.

This is an endpoint-dependent resolution rule of the single query
`A <: B`; it is not a second effect relation and its successful result cannot
be transitively composed with another concrete Function comparison. Variable
endpoints may retain the same inequality and dispatch through this resolver
when the Function shape is known. The denotation and normalization of
`[b,d]`, descriptor elaboration, subtraction eligibility, variable
correspondence, residual routing, context/Stack preservation, typed-family
transport, and generalization beyond the displayed cases remain proof
obligations. The displayed rules are the user's intended cases; no broader
four-field subtyping rule is approved here.

#### Source-call evidence for the coupling

The coupled shape has a source-level explanation independent of the frozen
Oracle subtype implementation. Under the selected source rules, an ordinary
value parameter has role `Value(a)`. A call reifies the complete argument as
one computation, enters the same receiver activation, forces that carrier at
entry, rebinds its result, and then runs the body. The source continuation
sequences argument execution before the body; if forcing diverges the body
may never run, and if it suspends the body remains its pending suffix. For an
argument computation `D` and body `B`, the source transition has the shape
`Force(D) >>= (v => B(v))`. Bind preserves the ordered trace prefix from `D`
and then the trace from `B(v)`; hence the support of the complete call is
included in `supp(D) ∪ supp(B(v))`. If `d` bounds `supp(D)` and `b`
uniformly bounds `supp(B(v))` for values admitted by `a`, the call has a
combined support bound; if `[b,d]` soundly presents that combination, it
bounds the call. This is why the same `d` appears at
the input and in the output bound: it is one carried computation executed at
entry, not two independently compared Function fields. The common value
endpoints `a,c` preserve the argument and result path in this rule.

This source transition explains why an argument effect bound remains
observable through a value-parameter call and why the intended output bound
must account for both argument and body execution. It is supporting
source-semantic evidence for the coupling, not the Function descriptor
comparison rule and not an explanation of how `never` elaborates. The
selected source rules for parameter roles and call entry are in redesign
charter §21 and ordinary-computation package §§3–4.

The compact signature `'a ['b, write int] -> ['b] int` places `'a` in the
value-input position and shares effect variable `'b` between input and result
descriptors. `write int` is subtractive in the contravariant descriptor;
removing it requires concrete-family match evidence and its type-argument
equations, while the shared `'b` survives in the result descriptor. This
fixes the intended notation, not the equality semantics of co-occurrence
merging or a complete subtraction algorithm.

Frozen-source characterization supports the coupling but does not define its
successor meaning. `infer/.../propagate.rs` detects a negative `Neg::Bot`
argument effect and routes both the target argument effect and source return
effect to the target return effect. The frozen specialization `TypeGraph`
instead decomposes independent Function components; for pure callee/cast
fixtures it reaches `EffectRow([]) <: Never`, which current code happens to
accept through a fallback. That fallback is not authority for the intended
rule and must not be used as its semantic explanation.

The frozen inference branch is specifically: when the lower Function's
argument-effect endpoint is `Neg::Bot`, enqueue the upper argument effect
below the upper return effect (after stripping target-return Stack wrappers)
and enqueue the lower return effect below that same upper return effect. This
is evidence for coupled effect flow. It does not yet prove that the source
algorithm implements the exact user rule for arbitrary `b,d`, because the
source code constrains two contributions into a target effect endpoint while
the rule writes their combination as `[b,d]`. Their equivalence, join/row
normalization, shared-witness transport, and Stack behavior remain explicit
proof obligations. The frozen specialization's four-child decomposition is
not a valid successor rule for this branch.

Optional Record comparisons are the discriminator. Oracle accepts each of

```text
{} <: {foo?: string}
{foo?: string} <: {}
{} <: {foo?: int}
```

and accepts the chain

```text
{} <: {foo?: string} <: {} <: {foo?: int}
```

while rejecting the direct comparison

```text
{foo?: string} <: {foo?: int}
```

Therefore the endpoint-dependent inequality solver cannot transitively
compose concrete resolution successes. Optional Record checking is a local
rule for resolving a concrete inequality; it must not be added to a global
structural relation and transitively saturated.

The examples are user-supplied Oracle observations, not new successor source
fixtures or a complete operational account of the evidence. They do not
yet determine which fields are materialized, dropped, defaulted, or converted;
whether a concrete adapter is required at each site; or how ambiguous
adaptation is selected.

## 2. Candidate endpoint-dependent solver organization

Use one comparison entry with its source context, endpoint pair, and the
consumer/source identity to which evidence will attach:

```text
Gamma; j |- A <: B  ==>  unresolved | success(evidence) | failure
```

`j` retains the originating source boundary, lexical openings, shared
declaration/request witnesses, typed evidence and joint symbolic coordinates.
The result records whether resolution only checked the endpoints, selected a
cast/adapter, or constructed executable realization. These are outcomes of
solving `A <: B`, not additional input relations.

The endpoint-directed transitions below are an unapproved solver candidate:

| Endpoints | Internal solver work |
|---|---|
| `X <: Y` | retain an oriented variable-edge record and propagate variable-bound information transitively, carrying source and guard context |
| `A <: X` | retain a lower-payload record for the unresolved inequality at `X`; move it along admitted variable edges |
| `X <: B` | retain an upper-payload record for the unresolved inequality at `X`; move it along admitted variable edges |
| concrete `A <: B` | resolve locally by structural decomposition, optional Record checks, registered cast resolution, or adapter resolution; attach child results/evidence to this query |

The frozen Oracle maps those endpoint forms to the listed lower/upper
orientations. When payloads share a pivot, the frozen machine can prepare a
replay query; its builders select eligible routes, retain the pivot and both
record identities, and compose inherited weights. They do not enqueue every
raw same-pivot pair. Lower insertion can also use an incremental row-residual
route. This is characterization of internal solving machinery, not a
successor semantic rule.

If source preservation admits a replay, it creates another inequality task
`A <: B` with the two payload records, shared pivot and inherited guards
attached as derivation data. The same endpoint dispatcher resolves it. The
exact source condition for creating that task remains open: same-pivot
coexistence and two independently successful endpoint resolutions do not by
themselves authorize it. Until the source bridge proves a replay mandatory,
failure of a candidate replay does not prove that the original source
constraints are unsatisfiable.

Keep original source comparison tasks and generated replay tasks separately
identified. An unresolved task can be suspended and resumed under the same
context after endpoint substitution. Variable reachability alone cannot
invent a new comparison task. Every original or replay-derived task re-enters
the selected generation-time scope guard before committing specialization.
The source-preservation and conversion-placement rules remain open.

Successful concrete resolution and its cast/adapter evidence stay attached to
their own source or generated task. They do not become variable edges or
premises for a third concrete comparison. In particular, success of `A <: B`
and `B <: C` does not discharge `A <: C`; the latter query must be resolved
directly if it is a source obligation. A replay query, if independently
justified, is likewise resolved afresh. Optional Record behavior supplies the
concrete witness to this non-composition requirement:

```text
{foo?: string} <: {}          succeeds
{} <: {foo?: int}             succeeds
{foo?: string} <: {foo?: int} fails
```

The `X = {}` example also shows why lower/upper storage must not be
misinterpreted as two successful concrete checks whose results compose. It
does not settle whether a source-preserving solver requires replay for any
specific pair; that is a separate proof obligation.

The index `j` stands for the originating source boundary, lexical opening,
retained typed evidence and applicable scope context. Every derived task still
passes the selected generation-time scope guard before resolution. This is a
candidate algorithmic organization, not a chosen data structure or a proof
that all source sites generate finitely many contexts.

For unresolved or variable endpoints, the solver may suspend the same
inequality task. Its endpoints, context and eventual resolution evidence must
remain correlated through aliases, replay, generalization and SCC intrusion.
The candidate mechanism and its finiteness are open.

## 3. Relation to reviewed structural results

The following results remain valid within their declared mathematical
fragments:

- `2026-10-03-scoped-structural-projection.md` proves properties of a
  transitive greatest structural simulation over mandatory Records,
  Functions and declared-variance constructors. Its theorem does not model
  local cast/adaptation resolution or optional Record fields.
- `2026-10-03-scoped-constraint-solving.md` decides closed comparisons in
  that same structural fragment. Its regular equality quotient and permission
  propagation remain separately useful, provided adaptation compatibility
  does not stand for `Eq`.
- `2026-10-03-open-residual-factorization.md` proves a conditional
  factorization for bounds interpreted in the greatest structural relation.
  Its pair normalization and §4.1 equivalence cannot be applied to general
  concrete compatibility until preservation of both compatibility and
  conversion evidence is proved.
- `2026-10-02-typed-boundary-realization-draft.md` gives a conditional
  operational realization for fixed-shape Function/Thunk adapters. It is not
  a general concrete-compatibility oracle and does not cover optional Records.

These fragment theorems are not refuted. Their source applicability is
narrower than treating their `<=` as the one relation used at every concrete
boundary.

## 4. Current source evidence and limits

The current successor solver represents polarized Function terms and
variable bounds, but its term algebra has no Record or cast/adapter node:
`crates/yu-solver/src/term.rs::TermView` and
`crates/yu-solver/src/lib.rs::InferenceSession::constrain_live` are the
owning comparison surface. Closed types in `crates/yu-types/src/lib.rs`
likewise have no Record or adapter constructor. This is research/feasibility
evidence; the current task still authorizes no compiler implementation.

The successor HIR does not admit cast declarations into its resolved
expression envelope (`crates/yu-hir/src/module.rs`). The parser owns
`cast` declarations, and the stable-core example
`tests/contracts/stable-core/v0/run/vm/pass/example_cast/main.yu` demonstrates
implicit value casts in that contract corpus. The typed-computation design
also records frozen evidence for registered field casts, while explicitly
not establishing general whole-Record adaptation.

The frozen Oracle implementation has two distinct routes that a successor
could place behind one compatibility interface, but they should not be
conflated as existing evidence of one adapter mechanism:

- For Record-to-Record constraints,
  `a58eefc3:crates/infer/src/constraints/machine/propagate.rs` visits upper
  fields in `enqueue_record_fields`, skips absent lower fields, skips the
  lower-optional/upper-required case, and otherwise emits a field-type
  comparison. Frozen specialization separately rejects a missing *required*
  upper field and recursively checks matching fields at
  `a58eefc3:crates/specialize/src/specialize2/type_graph.rs`.
- For different nominal constructor paths, constraint propagation emits
  `NominalCastNeeded`. `AnalysisSession::constrain_nominal_cast` eagerly adds
  constraints for exact-path cast candidates; eligible source-boundary
  diagnostics later use `CastTable::resolve_value` to classify missing,
  unique, or ambiguous candidates. This route is implemented in the frozen
  `crates/infer/src/analysis/session/{generalize,ocast_activation}.rs` and
  `crates/infer/src/casts.rs`.

Consequently the optional-Record examples do not show that Oracle routes those
checks through its registered nominal cast table. They show why successor
concrete compatibility cannot be the transitive closure of every local
structural/adaptation success. The user-selected direction remains to
investigate one local compatibility/adaptation boundary; a candidate resolver
may dispatch to Record adaptation and nominal cast rules while retaining
distinct derivations and evidence. Whether that unification is sound and
operationally faithful is open; it must not silently turn Record checking into
registered nominal casts or compose boundary successes.

The frozen specialization and runtime paths add a useful boundary distinction.
`specialize2/task_solver.rs` reconstructs materialized actual/expected pairs
for expression consumption, function-body checking and computed definition
signatures, then sends those pairs to `TypeGraph::constrain_materialized_subtype`.
That entrypoint interns an individual source-derived comparison with provenance;
`TypeGraph::process_subtype` propagates variable-to-variable comparisons as
edges and stores variable-to-concrete comparisons as bounds, while concrete
Record pairs take the local field/presence branch described above. This is
evidence for rechecking concrete boundaries during specialization rather than
assuming that a propagation skip permanently discharged them. It does not
prove how every original inference obligation is transported, nor authorize
the successor to reproduce this implementation topology.

The frozen inference machine also explicitly combines lower and upper bounds
stored on one variable. In `crates/infer/src/constraints/machine/bounds.rs`,
`cpk_lower_bound_replay_actions` pairs a newly added lower bound with existing
upper records; `cpk_upper_bound_replay_actions` performs the symmetric
pairing. Eligible pair replay actions carry the endpoint comparison,
`BinaryReplayDerivation { pivot, lower, upper, rule }`, and replay claim
parents. Prepared route evidence selects the ordinary pair; lower insertion
may instead use a row-residual route. A selected action can be trivial,
duplicate or evidence-only and be prefiltered from new worklist execution.
Thus Oracle has a bound-derived concrete comparison route in addition to
direct source-derived boundaries. This is narrower than closing all
successful concrete comparisons transitively, but the successor proof must
establish why each replay task follows from the originating inequalities.
The frozen derivation records lower/upper payload parents; it does not by
itself locate the runtime expression boundary where a resulting conversion
should execute.

Runtime realization is also split across paths. In the frozen
`crates/mono/src/boundary.rs`, Record boundary support checks required-field
presence and recursively asks whether shared field boundaries are supported;
it does not select nominal cast rules. The emitted generic `Coerce` for
`RecordFields` is lowered by `crates/evidence-vm/src/runtime.rs` to an alias,
so that node alone does not materialize a Record adapter. Separately, the
Evidence VM's `adapt_value_result` has a Record branch which calls
`adapt_record_value_result`: when that adapter branch is reached after the
runtime-equivalence shortcut, it visits target fields, omits a target-optional
field absent from the source shape, recursively adapts matching field values,
and reconstructs the target Record (extra source fields are not copied on this
path), except that source-Thunk to non-Thunk field boundaries retain the value
without recursive adaptation. Missing runtime values for declared matching
fields fail. This recursive adapter does not dispatch registered nominal
casts for child `Con` pairs.
An earlier directional runtime-equivalence shortcut can return the original
Record unchanged, preserving extra fields; rebuilding is therefore not an
invariant of every successful Record boundary. The older mono runtime also
returns Record values unchanged for supported Record boundaries, unlike the
Evidence VM adapter path.
Explicit Record literals can instead consume a field under its expected type
and materialize a direct nominal cast there; spreads and width changes remain
on the whole-Record boundary path. The frozen system therefore has reusable
local structural adapters and registered nominal casts, but not one shared
runtime resolution mechanism. A common successor inequality solver is a plausible entrypoint whose
concrete endpoint branch distinguishes a supported shape check from selected
conversion evidence and from an adapter actually emitted. In particular, source acceptance, identity preservation versus
projection, missing-field behavior and nested registered-cast realization
remain path- and stage-dependent questions.

The frozen nominal-cast route is not yet a uniform resolver either:
`TypeGraph::constrain_direct_cast` adds constraints for every exact-path Value
cast candidate, while specialization emission's `direct_cast_rule` selects the
first exact-path match. The separate `CastTable::resolve_value` API classifies
missing, unique and ambiguous cases. Any successor unification must decide
which stage resolves candidates and retain that decision with the originating
boundary; the historical paths are evidence for the problem shape, not an
approved policy to copy.

Successor named-Record type syntax currently requires `name: Type` fields;
the optional Record pattern syntax concerns pattern defaults and named
arguments, not optional fields in type declarations. Thus the user's
optional-Record observations are a semantic constraint on the successor
design, not evidence that this branch already parses or implements those
types.

## 5. Candidate Record-local checking derivation

The frozen concrete Record checker suggests a local presence-and-child
derivation for closed shapes. This is a candidate compatibility rule, not an
adopted source rule or a runtime adapter specification:

| Lower/actual field | Upper/expected field | Inference propagation | Concrete validation |
|---|---|---|---|
| absent | optional | no child comparison | absence is permitted |
| absent | required | no child comparison | reject missing required field |
| present, required | absent | no comparison | ignore extra lower field |
| present, optional | absent | no comparison | ignore extra lower field |
| present, required | present, optional | compare field types | validate child comparison |
| present, required | present, required | compare field types | validate child comparison |
| present, optional | present, optional | compare field types | validate child comparison |
| present, optional | present, required | defer the child comparison | validate child comparison; source-level acceptance and runtime presence guarantee remain unverified |

The last row matters: propagation skips the optional-to-required child pair,
but concrete specialization still checks matching field types. That skip is
not a permanent success. For the user-supplied discriminator, empty-to-optional
uses permitted absence, optional-to-empty has no upper fields to inspect, and
optional-string-to-optional-int reaches the incompatible child comparison.
This matches the stated pairwise outcomes as endpoint-specific inequality
resolution without adding optional Records to a transitive structural relation.

A candidate local derivation is:

```text
ResolveRecordInequality_j(L, R)
  = required-upper-name checks
    + one child inequality L.label <: R.label for each shared label
```

Its evidence retains the original boundary, label correspondence, permitted
absence, ignored extra fields, deferred child obligations and every child
compatibility/conversion result. The inequality solver's concrete endpoint branch could return distinct tagged
derivations for Record checks, ordinary structural checks and exact-path
nominal cast resolution while preserving one boundary context. At a shared
Record field it creates a child inequality task under the same solver entry,
allowing a registered conversion only when that child pair independently
resolves. This is a candidate rule shape; it does not identify checking
evidence with an executable whole-Record adapter, nor show that Oracle routes
optional Record comparisons through its nominal cast table.

Executable Record realization remains a separate gate. In particular, evidence
is still missing for how omitted fields, extra fields and optional-to-required
fields behave at runtime, and whether a selected field adapter can be embedded
in an aggregate adapter. No composition law may be inferred from successful
boundary checks.

### 5.1 Candidate concrete endpoint branch of the inequality solver

The user's requested direction is one inequality solver whose concrete
endpoint branch dispatches to structural checks, Record rules, registered cast
resolution or adapter resolution, with tagged derivations and realization
evidence. These are solver steps and outcomes for `A <: B`, not separate
semantic judgments or an adapter relation chained after compatibility. This
does not claim that optional Records use the registered nominal-cast table, or
that the frozen routes already share an implementation. This is a documentary
candidate only.

```text
InequalityTask_j = {
  boundary_or_replay_id,
  actual,
  expected,
  scope_guard,
  retained_typed_context
}

InequalityOutcome_j =
    Suspended { dependencies }
  | Rejected { reason, resolution_evidence }
  | Accepted {
      resolution_evidence,
      realization_evidence
    }

resolution_evidence =
    StructuralCheck
  | RecordCheck { presence, shared_field_inequality_tasks, ignored_extras }
  | RegisteredCastResolution { candidate_resolution }
  | AdapterResolution { plan }

realization_evidence =
    Unresolved
  | ProvenIdentity
  | GenericAdapterPlan { child_evidence, runtime_requirements }
  | SelectedNominalCast { rule, instantiated_constraints }
```

The names above are placeholders for separate evidence kinds, not source rules.
In particular, `ProvenIdentity` requires an independent source/runtime proof;
it cannot be inferred merely from `Accepted`. A resolver result also does not
show that an operation was emitted. A separate execution correspondence must
connect query identity, selected evidence, consumer boundary and emitted
operation. Different boundary contexts sharing the same endpoint pair must
remain distinguishable, while variable-bound replay remains the only source
of generated replay queries.

For a Record inequality, the outer `RecordCheck` records presence/extra-field
facts and issues a child inequality task for each shared field. A child
nominal cast may supply child selection evidence, but an aggregate adapter
cannot be constructed from those successes until runtime composition is
specified and proved. Likewise, two accepted local queries never entail a
third query: check evidence stays attached to its own boundary or replay id
and never becomes a concrete reachability edge.

This shape gives one inequality-solving entry where endpoint rules can invoke
structural checking, Record adaptation planning, and nominal cast resolution,
while keeping check success, candidate selection, adapter planning, and
execution as evidence stages of that same query. It does not
settle optional-to-required acceptance or presence guarantees, omitted/extra
field realization, cast ambiguity or selection timing, nested casts, effects,
or the location where replay evidence executes. The existing gate remains
bound-replay conservation first, followed by selection/conversion preservation
and executable realization; this dispatcher cannot shortcut those proofs.

## 6. Next theorem gate: inequality-task conservation

Do not extend structural residual normalization yet. The source judgment is one
inequality `A <: B` with endpoint-dependent solver rules. First prove that the
internal solver transitions preserve the source comparison ledger in both
directions for a fixed finite source elaboration. Each original inequality
task retains its identity, ordered endpoints, scope context, symbolic
coordinates and consumer. Each replay-generated inequality task retains its
pivot, lower/upper record identities and inherited guard/context.

Under one admissible shared assignment, variable-edge propagation may use
transitivity. Lower/upper records are internal indexes of unresolved inequality
tasks. A selected replay is another inequality task; its source derivation must show
why that task is required.
The conservation proof must show that no original guarded task is lost, every
mandatory replay is generated or represented by an identified row/residual
route, and no extra rejecting task is introduced. Each task re-enters the same
endpoint-dependent solver. Concrete resolution outcomes and cast/adapter
evidence remain attached to their task and are never premises for a third
concrete comparison. This is a target statement, not an established theorem.

The first proof fragment can fix closed Record shapes and treat nominal cast
resolution as a tagged solver outcome. It should preserve distinct contexts
for equal endpoint pairs, recheck scope guards on generated tasks, and connect
replay parents to the actual consumer boundary for any emitted conversion.
Same-pivot presence alone does not prove replay admission. Frozen proof
coverage and queue policy are characterization evidence, not source criteria.
Finite provenance and source-wide context closure remain premises to prove.

After task conservation, prove that concrete endpoint resolution retains
selected check/cast outcomes and realization evidence without composing
independent successes. Then extend residual factorization to preserve equality,
original inequality provenance and joint symbolic coordinates under one
assignment. Effectful interfaces, unknown Record shapes, lifecycle, and
implementation remain open. No optional-Record grammar, acceptance surface,
conversion-selection policy, resource limit, or implementation representation
is approved here.
