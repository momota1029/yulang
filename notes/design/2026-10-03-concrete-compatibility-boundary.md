# Concrete compatibility boundaries and variable bound propagation

Status: Reviewed; records the user's 2026-10-03 semantic decision; operational rules and implementation authority remain open
Date: 2026-10-03
Scope: separate transitive variable-bound propagation from local concrete compatibility and adaptation resolution
Approved-by: user for the relation distinction and Oracle observations recorded in §1 only
Reviewed-by: compiler_referee and spec_auditor §§1–5, 2026-10-03; architect pre-write audit plus fresh compiler_referee/spec_auditor review of §5; architect pre-write audit plus compiler_referee/spec_auditor review of §§2/6 boundary-conservation and bound-replay clarifications; architect pre-write audit plus compiler_referee/spec_auditor review of §5.1 shared-dispatcher candidate, all clean within bounded scopes after factual qualification
Implementation authority: none
Supersedes: none; narrows source applicability of structural relation candidates without invalidating their fragment theorems

## 1. Governing semantic decision

The user's 2026-10-03 decision distinguishes two operations:

1. Bound propagation among type variables may use transitivity.
2. A comparison whose endpoints are concrete types is a local compatibility
   judgment. It may resolve a cast or adapter at that boundary. Its success is
   not an edge in a single transitive concrete subtype relation.

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

Therefore local concrete compatibility is not closed under transitivity. In
particular, optional Record comparison must not be added to ordinary
structural subtyping and then transitively saturated.

The examples are user-supplied Oracle observations, not new successor source
fixtures or a complete operational account of the conversions. They do not
yet determine which fields are materialized, dropped, defaulted, or converted;
whether a concrete adapter is required at each site; or how ambiguous
adaptation is selected.

## 2. Candidate responsibility split

Keep these obligations distinct in any successor presentation:

```text
Eq(A, B)                         regular constructor equality
Bound(X, Y)                      variable-to-variable bound edge
Compat_j(A, B)                   local concrete compatibility query
Resolve(Compat_j(A, B))          selected conversion evidence / adapter
```

`Eq` identifies regular constructor unfoldings and retains its original
endpoints. Compatibility does not merge equality classes.

The bound graph may propagate relations between type variables transitively.
That permission alone does not establish which queries an arbitrary path with
concrete endpoints must generate; the source meaning of concrete-to-variable
bounds and suspended checks must first be specified. The frozen Oracle does,
however, contain a specific lower/upper replay rule: when bounds share a pivot
variable, adding a lower bound prepares routes against existing uppers, and
adding an upper bound prepares the symmetric routes. Eligible pair replays
carry the pivot and both bound-record identities in the replay plan; routing
may enqueue, deduplicate or prefilter them. This is candidate evidence for an
admissible bound-propagation derivation that generates a new concrete query;
the resulting pair still needs its own local check and conversion resolution.
It does not compose two previously successful `Compat` results.

Keep original source-boundary obligations and generated replay obligations
separately identified. An unresolved source boundary can remain suspended
with its context and later be checked on its substituted endpoints. A replay
query needs its own derivation from the relevant lower/upper bound records,
pivot, and inherited guards; variable reachability alone cannot invent one.
The replay rule's source preservation and conversion placement remain to be
proved for the successor.

One candidate separation for a successor constraint judgment is:

```text
Bound(X, Y) ∧ Lower_j(A, X)       ⇒ Lower_j(A, Y)
Bound(X, Y) ∧ Upper_k(Y, B)       ⇒ Upper_k(X, B)
Lower_j(A, X) ∧ Upper_k(X, B)    ⇒ Compat_ρ(j,k,X)(A, B)
```

Here `Lower` and `Upper` are variable-bound payloads, not assertions that the
two endpoints already passed a source-local `Compat`. The replay context `ρ`
retains both parent-bound identities, the pivot and both applicable scope
guards. The generated `Compat` result is local to that replay; its success
does not become a concrete reachability edge. Any further child bounds must
come from the selected compatibility derivation and retain this replay as
their parent. This separates bound transitivity from compatibility-result
composition, but is only a candidate factoring of the judgments: source
typing, guard combination, principality and runtime conversion placement are
unproved. In particular, the conditional `X={}` counterexample applies only
when the original obligations are interpreted as independent local `Compat`
checks, rather than these stronger bound payloads plus the replay rule.

For example, if two suspended obligations are interpreted as nothing more
than `Compat_j({foo?: string}, X)` and `Compat_k(X, {foo?: int})`, then both
pass for `X = {}` while direct `Compat_l({foo?: string}, {foo?: int})` fails.
This conditional counterexample shows that independent local compatibility
checks alone do not justify or account for the frozen lower/upper replay rule;
it does not refute a distinct variable-bound judgment that explicitly
generates that replay query.

Successful compatibility and its conversion evidence stay attached to their
own source or generated boundary query; they are not inserted into variable
reachability as concrete edges. In particular, successful
`Compat_j(A, B)` and `Compat_k(B, C)` do not discharge `Compat_l(A, C)`.
Any concrete query generated by bound replay needs the replay derivation and a
separate operational-validity argument for its conversion evidence.

The index `j` stands for the originating source boundary, lexical opening,
retained typed evidence and applicable scope context. Every derived query
still passes the selected generation-time scope guard before resolution.
This notation is a candidate separation, not a chosen data structure or a
proof that all source sites generate finitely many contexts.

For unresolved or variable endpoints, the solver may need to retain a
suspended compatibility obligation. Its endpoints, context and eventual
conversion evidence must remain correlated through aliases, replay,
generalization and SCC intrusion. The candidate mechanism and its finiteness
are open.

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
parents. Replay routing may enqueue or classify a route as trivial, duplicate,
or evidence-only and prefilter it. Thus Oracle has a bound-derived concrete
comparison route in addition to direct source-derived boundaries. This is narrower than closing
all successful concrete comparisons transitively, but the successor proof
must establish why each replay is part of its variable-bound judgment. The
frozen derivation records logical bound parents; it does not by itself locate
the runtime expression boundary where a resulting conversion should execute.

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
runtime resolution mechanism. A common successor compatibility dispatcher is
plausible as a local query interface; its result must distinguish a supported
shape check from selected conversion evidence and from an adapter actually
emitted. In particular, source acceptance, identity preservation versus
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
This matches the stated pairwise outcomes without adding optional Records to
the transitive structural relation.

A candidate local derivation is:

```text
RecordCheck_j(L, R)
  = required-upper-name checks
    + one child Compat_(j, label)(L.label, R.label) for each shared label
```

Its evidence retains the original boundary, label correspondence, permitted
absence, ignored extra fields, deferred child obligations and every child
compatibility/conversion result. A compatibility dispatcher could return
distinct tagged derivations for Record checks, ordinary structural checks and
exact-path nominal cast resolution while preserving one boundary context.
At a shared Record field it can ask the same local child resolver, allowing a
registered conversion only when that child pair independently resolves. This
is a candidate API shape; it does not identify checking evidence with an
executable whole-Record adapter, nor show that Oracle routes optional Record
comparisons through its nominal cast table.

Executable Record realization remains a separate gate. In particular, evidence
is still missing for how omitted fields, extra fields and optional-to-required
fields behave at runtime, and whether a selected field adapter can be embedded
in an aggregate adapter. No composition law may be inferred from successful
boundary checks.

### 5.1 Candidate shared local-query boundary

The user's requested direction can be explored as one dispatcher for local
concrete queries, with distinct tagged derivations and realization evidence.
This unifies where checks and adaptation resolution are requested; it does not
claim that optional Records use the registered nominal-cast table, or that the
frozen routes already share an implementation. This is a documentary candidate
only.

```text
LocalQuery_j = {
  boundary_or_replay_id,
  actual,
  expected,
  scope_guard,
  retained_typed_context
}

LocalOutcome_j =
    Suspended { dependencies }
  | Rejected { reason, check_derivation }
  | Accepted {
      check_derivation,
      realization_evidence
    }

check_derivation =
    StructuralCheck
  | RecordCheck { presence, shared_field_queries, ignored_extras }
  | NominalCastCheck { candidate_resolution }

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

At a Record boundary, the outer `RecordCheck` records presence/extra-field
facts and issues a distinct local child query for each shared field. A child
nominal cast may supply child selection evidence, but an aggregate adapter
cannot be constructed from those successes until runtime composition is
specified and proved. Likewise, two accepted local queries never entail a
third query: check evidence stays attached to its own boundary or replay id
and never becomes a concrete reachability edge.

This shape gives one local place to request structural checking, Record
adaptation planning, and nominal cast resolution, while keeping check success,
candidate selection, adapter planning, and execution separate. It does not
settle optional-to-required acceptance or presence guarantees, omitted/extra
field realization, cast ambiguity or selection timing, nested casts, effects,
or the location where replay evidence executes. The existing gate remains
bound-replay conservation first, followed by selection/conversion preservation
and executable realization; this dispatcher cannot shortcut those proofs.

## 6. Next theorem gate: bound-replay conservation

Do not extend structural residual normalization yet. First specify the source
meaning of concrete-to-variable bounds and suspended compatibility obligations.
Then prove a bound-replay conservation claim for a fixed finite source
elaboration. Each original source comparison has an identity, ordered
endpoints, scope context and symbolic coordinates. Each admissible replay has
its pivot and lower/upper premise identities. Under an admissible shared
assignment, propagation, alias substitution and specialization must preserve
all original guarded boundaries and generate exactly the concrete checks
required by the source bound judgment: no original obligation is lost, no
mandatory replay is omitted, and no extra rejecting query is introduced.
Each replay query is locally checked with its derived guard/context, and its
conversion evidence remains attached to that replay derivation. Successful
local compatibilities do not create replay premises. This is a target
statement, not an established theorem.

The first proof fragment can fix closed Record shapes and treat nominal cast
resolution as an uninterpreted tagged result. It should prove both directions
between the source-bound and replay ledger and the propagated representation,
preserve different contexts for equal endpoint pairs, and recheck scope guards
on generated comparisons and replay. A replay is admissible only when its
bound premises and pivot derive it; arbitrary paths of successful local
compatibilities cannot substitute. It must also explain how logical replay
parents connect to executable conversion boundaries. Finite semantic
provenance and source-wide context closure remain premises to prove, not
implementation details to assume.

After boundary conservation, prove that compatibility normalization retains
selected check/cast outcomes and conversion evidence without composing
independent successes. Only then extend residual factorization to preserve
equality, original bound provenance and joint symbolic coordinates under one
assignment. Effectful interfaces, unknown Record shapes, lifecycle, and
implementation remain open. No optional-Record grammar, acceptance surface,
conversion-selection policy, resource limit, or implementation representation
is approved here.
