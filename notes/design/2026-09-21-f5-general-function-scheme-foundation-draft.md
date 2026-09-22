# F5 general Function scheme foundation

Status: Authoritative; implementation in progress
Scope: canonical one-parameter Function source/HIR, live inference variables,
polarized closed schemes, quantification, recursive bounds, and fresh incoming
instantiation
Approved-by: user
Approved-at: 2026-09-21
Drafted-by: architect and primary agent
Reviewed-by: architect, compiler_referee, spec_auditor, performance_auditor
Supersedes: only the enumerated F4 closed-scheme, fixed-row,
Name-body shortcut, and structured-endpoint exclusions

## 1. Purpose and completion boundary

F5 replaces the closed `Bottom | Int` scheme special case with the smallest
general Simple-Sub scheme path that is reachable from production source:

```text
my f x = x
  -> canonical Pattern application CST
  -> parameter/Lambda HIR
  -> polarized Function constraint
  -> SCC generalization
  -> forall q0. q0 -> q0
```

The identity result is evidence, not an implementation branch. F5 is complete
only when this source path reaches the generic scheme machinery. A solver-only
fake Function witness may test the kernel but cannot close the gate.

F5 excludes expression application typing, annotations, destructuring,
multiple semantic parameters, effects beyond the closed pure Function subset,
roles/methods, imports, Core IR, and dynamic dependencies.

## 2. Authority and narrow supersession

F0-F4 retain authority for collection branding, the static dependency-sink-first
SCC plan, exact constraint/provenance admission, local semantic recovery,
atomic solve availability, and publication ordering.

On approval, F5 narrowly supersedes these F4 limitations:

- `ClosedValueScheme` is no longer a zero-binder `Copy` wrapper over only
  `Bottom | Int`;
- value rows are no longer fixed completely during collection;
- the integer-only endpoint grammar and `L + U <= 2V` bound do not govern
  structured Function endpoints;
- a resolved Name body no longer implies `use.value <: parent.root`; nested
  expression ownership decides where a use result flows;
- structured endpoints no longer trigger the direct-frontier rollback merely
  because they exist. The no-transitive-Var-pair invariant remains.

The withdrawn identity-function documents remain evidence for polarity only.
Their fixture-led ordering, equality-like shortcuts, unsupported-recursion
state, and definition-order lifecycle remain rejected.

## 3. Source and CST contract

The binding header accepts canonical Pattern ML application tails, so `f x` is
one lossless target Pattern rather than a binding-specific token exception.
The parser owns Pattern application topology and recovery. It must not inspect
the binding name or construct an identity-only node.

F5 semantic lowering admits exactly one recovery-free identifier parameter:

```text
my <identifier> <identifier> = <body>
```

Repeated parameters, annotations, destructured parameters, recovered targets,
and other Pattern application shapes remain lossless CST but lower to the
existing total unsupported/error boundary. They create no partial parameter,
Lambda, Function fact, or scheme.

At least one non-binding Pattern consumer must prove that the CST application
topology is canonical rather than binding-private.

## 4. HIR ownership and resolution

`yu-hir` adds:

- an artifact-owned `ParameterId`, identified by owning definition root plus
  parameter ordinal;
- a parameterized binding form with one ordered parameter;
- a Lambda/function-value expression occurrence distinct from its body
  occurrence;
- parameter Name resolution distinct from module `DefinitionUseId`;
- an evaluation classification that marks Lambda construction as a value.

Name lookup inside the body is local-first, then module namespace. A parameter
reference is monomorphic and never enters F2 or scheme instantiation. A module
reference remains an exact F2 definition use.

The Function constructor owns the only Function-to-definition-root fact. A
nested module Name flows to the Function result position, never directly to
the enclosing definition root.

HIR/lowering owns the value/computation classification and freezes a
generalization-boundary recipe. Empty effects are not a value-restriction
test, and `generalize` must not inspect source syntax.

## 5. Live inference ownership

`InferenceSession` owns appendable, session-local live variables. Each live
value/effect variable has:

- a checked dense `u32` identity;
- a level;
- one exact lower/upper bounds row;
- origin/non-generic metadata sufficient for generalization eligibility.

`ConstraintBatch` retains source identities and endpoint recipes. At session
startup they are translated once to live variables. Incoming instantiation may
append fresh variables; it must not reuse collection-owned component IDs,
definition roots, spelling, ranges, or module paths as type-variable identity.

The canonical pair key remains fixed-size and source-free. Direct variable
adjacency remains the physical representation of variable flow. Every
`constrain` call drains one synchronous, non-recursive frontier before return;
no transitive variable-pair table or deferred cross-call queue is allowed.

## 6. Polarized Function structure

Live and closed type structure is explicitly polarized. The minimal Function
shape is:

```text
PositiveFunction {
    argument: NegativeValue,
    argument_effect: NegativeEffect,
    result_effect: PositiveEffect,
    result: PositiveValue,
}
```

The negative Function form has the dual polarity. Argument position flips
polarity; result preserves it. F5 effects remain the closed pure subset
(`Bottom`/`Empty`) and are not quantified.

For identity, one live variable `alpha` occurs negatively in the argument and
positively in the result. Two reciprocal constraints, an opaque Function tag,
or direct construction of `forall a. a -> a` are forbidden substitutes.

## 7. Arenas and closed scheme representation

There are two distinct arenas:

1. mutable inference nodes and live variables owned by `InferenceSession`;
2. an immutable, canonical closed arena owned by `SolvedModule` through
   `yu-types`.

Typed arena handles are storage identities, not public semantic identities.
Closed nodes contain `Bottom`, `Top`, `Int`, quantified binder references,
recursive binder references, polarized Function, normalized union/intersection,
and neutral lower/upper bounds.

The closed scheme header contains:

```text
ClosedValueScheme {
    quantifier_count,
    recursive_bounds,
    predicate: PositiveValueId,
}
```

Ordinary binders `Q` and recursive binders `R` are disjoint:

- `Q ∩ R = ∅`;
- every closed variable belongs to exactly one of them;
- every `R` binder has exactly one neutral lower/upper bound entry;
- no `Q` binder has a recursive-bound entry;
- no session/live/source identity survives closure.

Binder ordinals follow deterministic normalized first occurrence and define
alpha-equivalence. Recursively owned boxed trees and whole-arena cloning per
use are rejected.

## 8. Generic generalization

For each SCC member, generalization starts from its live root in positive
polarity and performs:

1. structural/bound expansion memoized by `(live variable, polarity)`;
2. active-path recursion detection;
3. normalized polarity census over the whole reachable graph;
4. elimination of generalizable positive-only variables to bottom and
   negative-only variables to top;
5. retention of bipolar variables;
6. eligibility filtering by level, boundary, and non-generic/environment
   ownership;
7. deterministic assignment of disjoint `Q` and `R` ordinals;
8. pruning of unreachable recursive records;
9. closure and handle validation;
10. finalization into the immutable closed arena.

A naked unconstrained root therefore remains ordinary bottom/Never rather than
`forall a. a`. Productive re-entry records an `R` binder and its completed
lower/upper sides. F2 definition SCC identity and type-recursive binder identity
remain distinct.

Every member draft and finalized candidate is prepared before any durable
scheme slot changes. If validation/finalization can fail, the component install
is transactional. Only after all member schemes are installed may incoming
uses observe them.

## 9. Instantiation

Each incoming closed use creates a fresh substitution table:

1. allocate fresh live variables for all `Q` and `R` binders;
2. clone each reachable closed node at most once while preserving sharing;
3. restore both lower and upper sides of every recursive bound;
4. admit the instantiated positive predicate below the exact use value;
5. retain the exact definition-use cause and instantiation provenance.

Two uses never share fresh variables. Repeated occurrences of one binder inside
one use map to the same fresh variable. Internal SCC uses allocate no fresh
binder and continue to connect the target live root to the occurrence value.

Missing scheme slots, dangling handles, unmapped binders, `Q/R` overlap, and
allocation exhaustion are availability/invariant failures; they are not local
Unknown recovery and publish no partial `SolvedModule`.

## 10. Recovery and recursion

Registered definitions with ordinary body/type errors still complete through
the SCC lifecycle and generalize their actual remaining bounds. Body status
does not select Never. No `Failed`, `Blocked`, or `NotGeneralized` scheme state
is introduced.

Function structure is admitted atomically only after its required parameter and
body ownership exist. An erroneous body that produces no Function lower leaves
the ordinary unconstrained root and therefore bottom/Never. Independent
components continue.

Internal module-name uses remain open live-root constraints. Incoming uses only
instantiate closed schemes after the whole target component publishes.
Unseeded naked definition cycles remain bottom/Never; productive Function
recursion is represented by `R` bounds.

## 11. Public observation

`SolvedModule` adds one artifact-checked borrowed query:

```text
scheme_for(root) -> Result<ClosedValueSchemeView<'_>, ArtifactMismatch>
```

The view pairs the dense scheme slot with the one closed arena. It is the sole
complete definition-type observation and creates no second map or mirrored
type enum.

`root_value_for` remains a compatibility projection:

- closed bottom -> `Never`;
- closed Int -> `Int`;
- structured schemes -> `Unknown`.

It is documented as incomplete for structured definition types. Adding a
`SolvedValue::Function` mirror is rejected.

## 12. Provenance

Parameter IDs and occurrences are artifact-owned; spelling and range remain
payload. The Function-to-root direct fact uses the Lambda occurrence cause.
Scheme drafting/finalization creates no fabricated source cause.

Incoming provenance retains the exact `DefinitionUseCause`, source scheme
slot, top-level admitted fact, and dense substitution range. Recursive-bound
restoration uses derived instantiation provenance keyed by route, binder, and
bound side. F5 must specify whether the public explanation surface exposes
these derived records; it must not invent HIR occurrences for them.

## 13. Ordering

The F4 ordering remains exact:

```text
internal open uses
-> all member drafts
-> DraftsVisible barrier
-> validate/finalize all candidates
-> install all member schemes
-> incoming fresh instantiation
```

No incoming use may observe a partially published component. Canonical binder,
node, bound, member, and route order must be independent of hash iteration,
source spelling, range, and module path.

## 14. Performance and resources

Work units are:

```text
A = admitted direct constraints
E = direct variable edges
B = exact structured bound memberships
T = frontier transmissions
K = structured pair decompositions
G = generalized (variable, polarity) visits
N = finalized closed nodes
F = fresh Q/R variables over incoming uses
C = closed nodes cloned over incoming uses
```

Expected bounds:

```text
solve       O(A + E + B + T + K)
generalize  O(G + N)
instantiate O(F + C)
space       O(live variables + inference nodes + E + B + frontier
              + pair cache + drafts + closed arena + substitutions)
```

Each draft visits a `(variable, polarity)` state at most once. Each
instantiation clones each reachable node at most once. Generalization uses an
iterative worklist; it must not recursively overflow on deep chains. Component
memoization may share immutable completed structure but must not merge binder
identity or mutable draft state.

Counters and independent resource evidence cover live allocations/levels,
inference and closed arena nodes/capacity/bytes, structural decompositions,
generalization visits/polarity incidences/eliminations, `Q/R`, instantiation
fresh variables/node visits/restored bound sides, substitution scratch, draft
and publication coexistence, and total session retained/peak bytes. Existing F4
counters keep their meaning.

Deterministic exact-count tests precede timing. Isolated 1k/2k/4k identity and
incoming-instantiation processes must keep all listed linear fields below the
approved ratio bound. Repeated timing samples are collected only when counter
and resource evidence leaves a concrete unresolved decision.

## 15. Internal implementation gates

F5 is one completion gate with these internal stages:

1. **F5a — closed types/API:** closed polarized arena, Function, `Q/R`, bounds,
   views, alpha-equivalence; no solver behavior change.
2. **F5b — live variables:** session-owned appendable variables, levels and
   batch-recipe translation; general structured frontier; F4 regression gate.
3. **F5c — general schemes:** polarity census, elimination, recursive bounds,
   transactional publication, per-use fresh instantiation.
4. **F5d — source/HIR Function:** canonical Pattern application CST, one
   identifier parameter, local-first scope, Lambda/body occurrences, evaluation
   classification, structural Function collection.
5. **F5e — publication/certification:** `scheme_for`, compatibility projection,
   provenance, complete counters/resources, source identity witnesses, and
   scale certification.

F5 does not complete after a synthetic F5c witness.

## 16. Required witnesses

- `my f x = x`: exact source/CST/HIR/constraint/scheme path;
- alpha-renamed and locally shadowed identity;
- `my k x = 42`: negative-only parameter elimination;
- `my n = 42; my f x = n` and forward-order equivalent;
- productive self and mutual Function recursion with exact `R` records;
- unproductive self/mutual cycles remain Never;
- two closed identity uses allocate disjoint fresh variables while preserving
  intra-use sharing;
- malformed/unresolved Function body plus an independent integer;
- `Q/R` disjointness, closure, deterministic alpha-equivalence, and no live IDs;
- all-drafts/all-installs/incoming ordering;
- no partial result after injected handle/allocation/closure failure;
- foreign-artifact `scheme_for` rejection;
- all F4 integer, Name, recovery, provenance, counter, and scale contracts.

Formatted type text is secondary evidence only.

## 17. Rollback conditions

Return to design if implementation requires:

- collection-owned identities for fresh instantiation variables;
- source/HIR IDs, spelling, or range as type-variable identity;
- a second SCC, union-find equality, transitive variable-pair materialization,
  or a frontier surviving `constrain` return;
- identity-specific generalization or formatted-output authority;
- `Q/R` overlap, unmapped free variables, or cross-use fresh-variable sharing;
- incoming instantiation before complete component publication;
- retained mutable drafts or a second root-type authority;
- per-use whole-arena clone, per-definition store scan, or unbounded recursive
  expansion;
- binding-private Pattern parsing or fake HIR nodes unreachable from production;
- expression application typing merely to pass identity;
- source/CST replay or a parallel typed HIR;
- non-linear 1k/2k/4k count/resource families.

## 18. Decisions proposed for approval

The integrated recommendation is:

1. F5 completes only at the real source identity path, not a synthetic-only
   solver milestone.
2. Canonical Pattern ML application is admitted for binding headers; semantic
   expression application remains excluded.
3. F5 HIR admits one recovery-free identifier parameter and a Lambda value.
4. Inference uses session-owned appendable live variables; collection stores
   endpoint recipes only.
5. Inference and closed types use separate typed arenas.
6. `Q` and `R` are disjoint and closure-validated.
7. HIR evaluation classification owns the generalization boundary.
8. Existing F2/F4 SCC ordering handles recursive definitions; `R` handles
   productive type-graph recursion.
9. `scheme_for` becomes the complete public definition-type query;
   `root_value_for` projects structured schemes to `Unknown` and is documented
   as incomplete.

Implementation is forbidden until this Draft passes M3 review and the user
approves these decisions.

## 19. Review-closure authority inside this Draft

Sections 19–27 replace any less-specific or conflicting statement in §§3–16.
They are executable contract, not optional implementation guidance. In
particular they close the initial M3 findings about Pattern recovery, HIR/API
shape, structured `constrain`, effects, levels/extrusion, recursive binders,
derived provenance, canonical ordering, and finite resource evidence.

## 20. Exact Pattern grammar, CST, and recovery

Add public `SyntaxKind::PatternMlApplicationTail` and the precedence
`PatternPrecedence::MlApplication`, tighter than alias, alternation, and type
annotation:

```text
Pattern ::= PatternNud PatternTail*
PatternTail ::= PatternMlApplicationTail
              | PatternAliasTail
              | PatternAlternationTail
              | PatternTypeAnnotationTail
PatternMlApplicationTail ::= Gml Pattern@MlApplication
Gml ::= one maximal nonempty trivia run
```

The tail loop first tests caller stops, matching/foreign closes, fences, `=`,
`Item`, non-NUD `@`, and layout handoff. Existing fixed-marker tails win before
ML application. Thus `f as y` is alias and `f (as)` is application.

`Gml` is admitted only when it is same-line trivia, or every newline is
followed by indentation strictly deeper than the enclosing Pattern baseline.
A same-line comment belongs to `Gml`; continuation after its newline still
requires deeper indentation. On failure, the whole trivia run and following
item are left untouched and no tail, `Missing`, or `Error` is emitted.

The argument is parsed at `MlApplication` minimum precedence with
unparenthesized ML continuation and looser tails disabled inside it. The outer
loop then continues, giving:

```text
f x y      = two sibling application tails
f x as y   = application, then outer alias
f x | g y  = alternation of two applications
f x: T     = annotation of the application
```

Once an argument Pattern is admitted, existing Pattern recovery owns its
malformed content. There is no replay or rescan. Trivia remains a direct child
of the enclosing Pattern and the nested argument Pattern is the only semantic
child of `PatternMlApplicationTail`:

```text
Pattern
  IdentifierPattern("f")
  Whitespace(" ")
  PatternMlApplicationTail
    Pattern
      IdentifierPattern("x")
```

Because this is shared Pattern grammar, `(a b)` and `[a b]` become one
application-pattern element. `{a b}` retains record-field grammar. These are
intentional expected-output changes. Tests cover every ordering example above,
spaces/comments, deeper/equal/shallower indentation, every stop/close/fence,
malformed admitted arguments, exact parenthesized/list/record topology, and a
non-binding Pattern consumer.

## 21. Exact HIR and source-constraint product

Public `yu-hir` additions are:

```text
HirParameterId
HirParameter { id, name, range }
HirBinding::parameters() -> &[HirParameter]
NameResolution::Parameter(HirParameterId)
ResolvedExpr::Lambda {
    occurrence: HirOccurrenceId,
    parameter: HirParameterId,
    body: Box<ResolvedExpr>,
    range: TextRange,
}
```

`HirParameterId` is artifact-branded and identified by owning
`DefinitionRootId` plus left-to-right ordinal. Spelling/range are payload.
F5 permits only ordinal zero. Lambda occurrence precedes its body in HIR
preorder. Structural equality uses IDs and owned child structure, never source
spelling or range.

Lowering uses a lexical scope stack with a depth guard restored on every
success, local error, and availability exit. Lookup is parameter-local first,
then the completed module namespace. Parameter references never allocate a
`DefinitionUseId` or enter F2.

Exact lowering outcomes are:

| Target/body | HIR/result ownership |
|---|---|
| bare recovery-free identifier | existing binding behavior |
| recovery-free identifier plus one tail whose argument is exactly one recovery-free identifier | registered binding, root, parameter zero, Lambda |
| admitted header plus supported body | ordinary Lambda body; Function eligible |
| admitted header plus recovered/unsupported/unresolved body | Lambda with current Error/unresolved body; root/parameter retained; Function ineligible |
| repeated tail or annotated/destructured/recovered head/argument | existing unsupported/error item; no root, parameter, Lambda, Function, or scheme |

HIR classification freezes `FetchValue` for Lambda, Integer, and supported pure
Name forms. Future computation forms use `FetchComputation`. `generalize` never
examines syntax, HIR tags, or effect emptiness.

For `my f x = x`, allocate one live value variable `alpha` for the parameter.
The parameter body occurrence reuses `alpha` directly as its positive value;
it has no second body value row. It owns `epsilon_body` and emits the two exact
effect relations. Lambda owns `epsilon_lambda` and emits the same two evaluation
effect relations. One Lambda-owned fact is admitted:

```text
Function(alpha-, EmptyEffect, epsilon_body+, alpha+) <: f.root
```

There are exactly five direct facts: four effect relations and this Function
fact. There is no parameter value fact, equality edge, or body-to-root fact.

Integer and module-Name bodies retain their F4 occurrence value/effect recipe,
except that their result flows only into Function result/effect fields. Nested
module Names keep internal/incoming SCC routing to the body occurrence.

Function admission is atomic. If the admitted header's body has no supported
positive value/effect endpoint, neither Lambda effect facts nor Function fact
is emitted. `my f x = @` and `my f x = missing` therefore retain their root and
close to Bottom/Never, with existing diagnostics. The lexical guard prevents
`x` leaking into the next definition.

## 22. Total live endpoint and `constrain` algebra

F5 retains F4 effect ownership: source occurrence effects stay exact leaf/
component relations and are not quantified. Session-owned effect rows exist
only where Function structure and bound replay require live latent/body effect
variables; they use the same direct-edge discipline and are counted separately.

Live endpoints are:

```text
PosValue ::= Bottom | Int | PosVar(v)
           | PosFunction(NegValue, NegEffect, PosEffect, PosValue)
NegValue ::= Top | Bottom | Int | NegVar(v)
           | NegFunction(PosValue, PosEffect, NegEffect, NegValue)
PosEffect ::= EffectBottom | PosEffectVar(e)
NegEffect ::= EmptyEffect | NegEffectVar(e)
```

Union/intersection are closed normalization products, not live input terms.
Each admitted pair uses one fixed-size source-free typed pair key and is marked
before decomposition. The memo lives for the whole session. Duplicate probes
do no mutation or decomposition.

The same-kind transition table is total:

| Lower | Upper | Action |
|---|---|---|
| Bottom | any negative value | success, no mutation |
| any positive value | Top | success, no mutation |
| Int | Int | success |
| Int | Bottom or negative Function | local `IncompatibleValue` |
| positive Function | Bottom or Int | local `IncompatibleValue` |
| `Function(a,ae,re,r)` | `Function(A,AE,RE,R)` | enqueue `A <: a`, `AE <: ae`, `re <: RE`, `r <: R`, in that order |
| `PosVar(a)` | `NegVar(b)` | one direct `a -> b` edge; replay exact lowers of a against exact uppers of b |
| non-variable positive | `NegVar(b)` | extrude to b's level; insert exact lower once; replay uppers |
| `PosVar(a)` | non-variable negative | extrude to a's level; insert exact upper once; replay lowers |
| EffectBottom | EmptyEffect | success |
| EffectBottom | `NegEffectVar(e)` | insert exact lower |
| `PosEffectVar(e)` | EmptyEffect | insert exact upper |
| `PosEffectVar(a)` | `NegEffectVar(b)` | one direct effect edge and exact replay |
| different `ComponentKind` | any | existing local `CrossKind` |

The four Function subpairs encode argument/effect contravariance and result/
effect covariance exactly. `IncompatibleValue` is appended to
`SolverErrorKind`; it is local and mutates no incompatible pair's bounds.

The frontier is iterative, synchronous, empty on entry/return, and propagates
only direct rows and exact structural memberships. No recursive descent,
transitive Var-pair materialization, deferred queue, or union-find is allowed.

## 23. Levels, extrusion, eligibility, and recursion

Level zero is the module/environment boundary. Top-level definition roots,
parameters, and body components are level one. Future nested bodies use a
checked child level. Incoming Q/R variables are allocated at the consuming
definition body's frozen use-site level. Each `DefinitionUse` recipe therefore
retains that level. Checked level or identity overflow returns the existing
availability exhaustion error.

Before inserting a positive bound into variable `v`, iteratively traverse the
node and lower every reachable younger variable to `level(v)`; negative
insertion is dual. Lowering a variable traverses its installed exact lower and
upper bounds once per extrusion operation. A Var/Var relation ages endpoints
to their minimum level through the two bound directions.

Generalization order is normative:

1. expand exact bounds with iterative `(variable, polarity)` memoization;
2. detect guarded active-path re-entry;
3. compute non-generic closure from the pre-component enclosing environment;
4. compute eligibility before elimination;
5. census normalized positive/negative incidence;
6. eliminate eligible positive-only to Bottom and negative-only to Top;
7. remove R variables and assign remaining eligible bipolar variables to Q;
8. reject any reachable live variable that is not Q, R, or a valid enclosing
   closed binder;
9. prune unreachable R entries, validate closure, finalize candidates.

```text
eliminable(v) = level(v) >= boundary && v not in non_generic
quantifiable(v) = level(v) > boundary && v not in non_generic
```

`FetchValue` supplies boundary zero. `FetchComputation` supplies the body
level, allowing one-sided simplification at equality but forbidding
quantification there. F5 admits no computation-valued source form.

An active re-entry creates provisional R only when the path from first entry
crosses a Function constructor. Direct variable cycles and bound-aggregation-
only cycles are unguarded. Retain R only when its reference remains reachable,
its completed bound contains the guarded return path, and it is not reduced to
Bottom..Top. One live variable owns one R across both polarities. Complete the
encountered side, expand the dual side under the same owner, then normalize.
Assign R before Q by normalized first guarded re-entry; emit R entries in
ordinal order, lower before upper.

With `PureFun(A,B) = Function(A, EmptyEffect, EffectBottom, B)`, normative
schemes are:

```text
my id x = x
  Q=[q0], R=[], predicate=PureFun(q0-, q0+)

my k x = 42
  Q=[], R=[], predicate=PureFun(Top, Int)

my f = f
  Q=[], R=[], predicate=Bottom

my f x = f
  Q=[], R=[r0]
  predicate=PureFun(Top, r0+)
  R0=[lower=PureFun(Top, r0+), upper=Top]

my f x = g; my g y = f
  each member: Q=[], R=[r0]
  predicate=PureFun(Top, PureFun(Top, r0+))
  R0=[lower=PureFun(Top, PureFun(Top, r0+)), upper=Top]
```

The F5c trace test must validate these records before implementation proceeds.
Different incoming uses allocate disjoint substitutions; repeated occurrences
within one use share exactly one fresh variable. Restore each R lower then upper
side before routing the instantiated predicate.

## 24. Exact public API and provenance delta

`yu-types` exports opaque arena/handle and borrowed-view types:

```text
ClosedTypeArena
PositiveValueId, NegativeValueId
PositiveEffectId, NegativeEffectId
NeutralValueId
QuantifierId, RecursiveBinderId
PositiveValueView<'a>
NegativeValueView<'a>
PositiveEffectView
NegativeEffectView
NeutralValueView<'a>
ClosedRecursiveBound
ClosedValueScheme
ClosedValueSchemeView<'a>
```

Views expose predicate, binder counts/entries, node lookup, borrowed children,
and structural alpha-equivalence. Handles are opaque `Copy` storage IDs;
`ClosedValueScheme` is opaque `Clone + Eq`, not `Copy`. Public constructors for
handles/schemes are removed; arena construction is crate-private.
`ClosedPositiveValue`, `ClosedValueScheme::new`, and `body` are removed.

`SolvedModule` owns one closed arena plus dense scheme slots and adds:

```text
scheme_for(&DefinitionRootId)
  -> Result<ClosedValueSchemeView<'_>, ArtifactMismatch>
```

`root_value_for` remains a documented incomplete compatibility projection:
Bottom→Never, Int→Int, structured→Unknown. No `SolvedValue::Function` is added.

Public `Term` becomes an opaque handle into a read-only inference-term arena
owned by `ConstraintStore`; `term_view(Term)` exposes Leaf, Component,
positive/negative Function, or live-variable structure. Existing
`SemanticFact::lower/upper` return these handles. This is a breaking API
migration; rustdoc path/trait/lifetime probes and every exhaustive match are
part of F5a/F5e expected-output authority.

Derived provenance is private in F5. Direct source facts retain current public
fact/cause/receipt edges. Incoming routes add source scheme slot and dense
substitution range. Decomposition, extrusion, frontier transmission, and R
restoration create no public SemanticFact, HIR occurrence, or explanation
node. Private route metadata retains R binder/side ranges for validation and
counters. Public derived explanations require a later gate.

## 25. Canonical ordering and bounded generalization sharing

Canonical order is source order for Pattern tails/parameters/occurrences,
existing F0/F2 order for definitions/members/uses, component recipe then route
and binder order for live allocation, first successful pair admission for live
bounds, and argument/argument-effect/result-effect/result for Function
decomposition.

Closed union/intersection children sort by normalized structural discriminator
and recursive normalized child key, then deduplicate. Hash-cons lookup never
sets output order. R uses normalized first guarded re-entry; Q uses normalized
first retained bipolar occurrence after R removal. Scheme install follows F2
member order.

Generalization memo has two layers:

- component-scoped immutable expansion summaries keyed by `(variable,
  polarity, frozen-bound-epoch)` may share only binder-free normalized
  structure and incidence facts;
- each root draft owns its R/Q namespace, active-path stack, eligibility,
  pruning, and final closed-node mapping.

Bounds are frozen throughout one component's drafting; mutation during the
draft barrier is an invariant failure. This prevents D roots from rescanning a
shared acyclic cone while forbidding binder namespace sharing. Scale tests must
include many roots over one shared large graph, independent graphs, and guarded
shared recursion.

## 26. Finite counters, resources, and scale contract

Add exactly these logical counters:

```text
live_value_variable_allocations
live_effect_variable_allocations
live_variable_level_lowerings
inference_positive_value_node_allocations
inference_negative_value_node_allocations
inference_positive_effect_node_allocations
inference_negative_effect_node_allocations
structured_pair_probes
structured_pair_admissions
structured_pair_duplicates
structured_pair_decompositions
generalization_state_visits
generalization_positive_incidences
generalization_negative_incidences
generalization_positive_eliminations
generalization_negative_eliminations
generalization_quantifier_writes
generalization_recursive_binder_writes
closed_positive_value_node_allocations
closed_negative_value_node_allocations
closed_neutral_value_node_allocations
instantiation_fresh_value_variables
instantiation_fresh_effect_variables
instantiation_node_visits
instantiation_lower_bound_restorations
instantiation_upper_bound_restorations
```

The session-lifetime structured pair memo bounds decompositions exactly by
successful structured pair admissions. Duplicate probes never decompose.

Add five resource families, each with requested slots, actual capacity,
retained bytes, peak bytes, and capacity growths:

```text
live_variable_tables
inference_type_arena
closed_type_arena
generalization_scratch
instantiation_substitution
```

Byte models are checked `capacity * size_of::<slot>()`, excluding allocator
metadata/control bytes/fragmentation exactly as F4. Checked aggregate sums count
each physical lane once. Independent test ledgers reconcile aggregate semantic
and session retained/peak values exactly.

O(1) resource samples occur only after batch translation, on actual capacity
growth, when all drafts coexist, when all finalized candidates coexist with
drafts, after atomic install, at each incoming substitution scratch peak, and
after finish transfer. No sampling scan is allowed.

Exact families include N independent identities (`5N` direct facts, `N` Q,
zero R/fresh), one identity plus N later alias uses (N substitutions and N
fresh value variables, zero fresh effects), exact self/mutual R restoration,
many roots sharing one graph, independent graphs, and guarded shared recursion.
To detect whole-arena cloning, include Θ(N) unrelated closed-arena content plus
Θ(U) uses of one constant-size identity scheme; clone visits must follow that
scheme, not total arena size.

Run 1k/2k/4k identity, alias-use, shared-graph, and arena-factorization
families in isolated single-thread processes capped at 30/60/120 seconds.
Every causal count is exact. Every capacity/retained/peak field has adjacent
actual-observation ratio `<2.5`. No repeated timing samples are taken unless
the deterministic evidence leaves a named decision unresolved. Existing F4
counters and limits retain their meanings.

## 27. Revised internal gates and test disposition

1. **F5a — source/HIR contract:** exact shared Pattern grammar/recovery,
   one-parameter HIR, scope restoration, lowering table; no solver Function.
2. **F5b — public types/live algebra:** breaking closed/public fact-view API,
   live variables/levels/extrusion, total Function table, F4 regression.
3. **F5c — closure:** eligibility-before-elimination, guarded R, two-layer memo,
   transactional publication, fresh instantiation.
4. **F5d — structural integration:** real Lambda recipe and all identity,
   constant, module Name, error, self/mutual witnesses.
5. **F5e — observation/certification:** `scheme_for`, compatibility projection,
   private provenance, canonicalization, exact counters/resources and scale.

Supersede F4 negative controls only where they assert Function structure is
impossible. Retain F4 integer, SCC, ordering, recovery, availability,
provenance, exact-store, and no-transitive-frontier contracts. Mechanically
migrate public view access only where §24 requires it.

Focused tests cover every Pattern rule, HIR outcome, constrain-table row,
Function field order, both extrusion directions, `>=` elimination versus `>`
quantification, closure/Q-R rejection, guarded/unproductive cycles, both R
sides, allocation/handle/finalization atomic failure, scope restoration,
foreign artifact queries, normalized renamed/relocated/range-shifted/hash-order
scheme equality, and all source witnesses in §16.

No separate design choice remains inside this integrated proposal. User
approval authorizes the Pattern topology change, one-parameter public HIR,
breaking closed/fact-view API migration, error-body Bottom/Never, guarded R
records, private derived provenance, and the finite counter/resource contract.

## 28. Second review closure and precedence

Sections 28–35 replace conflicting details in §§20–27. They close the second
M3 review. In §20, the retained CST name is `SyntaxKind::PatternTypeAnnotation`
and the grammar alternative is `PatternTypeAnnotation`, not
`PatternTypeAnnotationTail`. `PatternPrecedence::TypeAnnotation` is unchanged.

## 29. Exact public HIR contract

```rust
#[derive(Clone)]
pub struct HirParameterId { owner: DefinitionRootId, ordinal: u32 }

impl HirParameterId {
    pub fn definition_root(&self) -> &DefinitionRootId;
    pub const fn ordinal(&self) -> u32;
}
impl Debug for HirParameterId;
impl PartialEq for HirParameterId; // artifact + owner + ordinal
impl Eq for HirParameterId;
impl Hash for HirParameterId;

#[derive(Clone, Debug)]
pub struct HirParameter {
    id: HirParameterId,
    name: HirName,
    range: Range<usize>,
}
impl HirParameter {
    pub fn id(&self) -> &HirParameterId;
    pub fn name(&self) -> &HirName;
    pub fn range(&self) -> &Range<usize>;
}
impl PartialEq for HirParameter; // name + range; excludes artifact ID
impl Eq for HirParameter;

impl HirBinding { pub fn parameters(&self) -> &[HirParameter]; }
impl HirModule {
    pub fn owns_parameter(&self, parameter: &HirParameterId) -> bool;
}
```

`HirParameterId` is not `Copy`, ordered, serializable, or publicly
constructible. `owns_parameter` checks the artifact and an allocated
owner/ordinal. All ranges remain `Range<usize>`.

Ordinary ID equality remains artifact-sensitive. Cross-artifact structural HIR
equality is separate: parameters exclude `id`; Lambda excludes occurrence and
parameter artifact tokens but compares parameter ordinal, body, and range; a
parameter-resolved Name compares owner-local ordinal. No artifact ID equality
is weakened. Lambda joins the existing exhaustive `range()` and `occurrence()`
accessors.

## 30. Single live bound authority and exact effect bridge

`InferenceSession` is the sole mutable bound owner. F5 removes F4's parallel
`occurrence_exact_bounds` solve authority. At session start an injective private
map translates every collected value/effect component and root exactly once to
a live variable; parameter recipes translate to live value variables. Public
source facts remain unchanged, but admitting each fact updates the mapped live
row. Finish derives `SolvedProjection` once from those rows and never consults
a frozen occurrence summary.

The body occurrence's effect component maps to the same live effect variable
used by the Function result-effect field. Lambda evaluation owns a separate
live effect variable. For identity the exact allocation is two live value
variables (`f.root`, `alpha`), two live effect variables (`epsilon_body`,
`epsilon_lambda`), one positive Function node, and the five facts in §21. The
parameter Name has no separate live value; Lambda has no live value row and its
positive Function endpoint is admitted directly below `f.root`.

An Integer or module-Name body keeps one live value and one live effect row and
its four F4 leaf/effect facts, while its former body-to-root fact is replaced by
the Function fact. An error body allocates only root and parameter, no body or
Lambda effect row, Function node, or fact. This supersedes only F4 frozen row
IDs, `occurrence_exact_bounds`, and finish-time occurrence-bound authority; F4
public facts, causes, leaf semantics, and projections remain.

## 31. Incompatible-value causality

```rust
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueShape { Bottom, Int, Function }

pub enum SolverErrorKind {
    CrossKind { lower: ComponentKind, upper: ComponentKind },
    IncompatibleValue { lower: ValueShape, upper: ValueShape },
}
```

Only `Int <: Bottom`, `Int <: Function`, `Function <: Bottom`, and
`Function <: Int` produce this error. Every frontier item carries the inducing
direct `ConstraintOccurrenceId` and `CauseId`; decomposition copies them to
all children. A pair-memo entry caches compatible or the exact incompatible
shape result. A duplicate never mutates or decomposes, but replays an
incompatibility for the current direct cause. Diagnostics deduplicate by
`(ConstraintOccurrenceId, SolverErrorKind)`: repeated derived paths from one
source report once, while distinct sources each report. Order is direct fact
admission order, then Function argument, argument effect, result effect,
result; hash iteration never orders diagnostics.

## 32. Exact closed-type and term observation API

Closed handles are opaque `Clone + Copy + Debug + Eq + Hash + Ord` pairs of an
arena brand and `u32` index; Q/R handles have the same traits and only a `u32`
ordinal. Their constructors and every arena mutation are crate-private.

```rust
pub enum ClosedTypeLookupError { ArenaMismatch, InvalidHandle }
pub enum PositiveValueView<'a> {
    Bottom, Int, Quantified(QuantifierId), Recursive(RecursiveBinderId),
    Function { argument: NegativeValueId,
               argument_effect: NegativeEffectId,
               result_effect: PositiveEffectId,
               result: PositiveValueId },
    Union(&'a [PositiveValueId]),
}
pub enum NegativeValueView<'a> {
    Top, Bottom, Int, Quantified(QuantifierId), Recursive(RecursiveBinderId),
    Function { argument: PositiveValueId,
               argument_effect: PositiveEffectId,
               result_effect: NegativeEffectId,
               result: NegativeValueId },
    Intersection(&'a [NegativeValueId]),
}
pub enum PositiveEffectView { Bottom }
pub enum NegativeEffectView { Empty }
pub enum NeutralValueView {
    Bounds { lower: PositiveValueId, upper: NegativeValueId },
}
```

`ClosedRecursiveBound` is `Clone + Copy + Debug + Eq + Hash` with public
`binder()` and `bounds()` accessors. `ClosedValueScheme` is opaque
`Clone + Debug + Eq + Hash`, non-`Copy`, and stores arena brand, quantifier
count, boxed R entries, and predicate. Storage equality includes arena/handle
identity and is not semantic equality.

`ClosedValueSchemeView<'a>` is `Clone + Copy`, borrows arena and scheme, and
exposes `quantifier_count`, `recursive_bounds`, `predicate`, and fallible
`positive_value`, `negative_value`, `positive_effect`, `negative_effect`, and
`neutral_value` lookups. Each lookup returns the view above or
`ClosedTypeLookupError`. `alpha_eq(other)` ignores arena IDs, indices, and
binder ordinals while preserving Q/R class, recursive structure, polarity,
Function field order, and normalized union/intersection membership.
`scheme_for` has the signature in §24 and its view cannot outlive
`SolvedModule`.

Public constraint terms become opaque `Clone + Copy + Debug + Eq + Hash`
arena/index handles. `ConstraintStore` owns their arena and exposes:

```rust
pub enum TermLookupError { ArenaMismatch, InvalidHandle }
pub struct LiveVariableView { kind: ComponentKind, polarity: Polarity,
                              ordinal: u32 }
pub enum TermView<'a> {
    Leaf(Leaf), Component(&'a ComponentId), LiveVariable(LiveVariableView),
    PositiveFunction { argument: Term, argument_effect: Term,
                       result_effect: Term, result: Term },
    NegativeFunction { argument: Term, argument_effect: Term,
                       result_effect: Term, result: Term },
}
impl ConstraintStore {
    pub fn leaf_term(&mut self, leaf: Leaf) -> Term;
    pub fn component_term(&mut self, component: ComponentId)
        -> Result<Term, ArtifactMismatch>;
    pub fn term_view(&self, term: Term)
        -> Result<TermView<'_>, TermLookupError>;
    pub fn term_kind(&self, term: Term)
        -> Result<ComponentKind, TermLookupError>;
}
```

`LiveVariableView` has public `kind`, `polarity`, and `ordinal` accessors.
Function/live constructors remain crate-private. Both
`ConstraintOccurrence::{lower,upper}` and `SemanticFact::{lower,upper}` return
`Term` by value. Remove public enum construction and `Term::kind`; callers go
through `ConstraintStore`.

Compile probes cover exact traits, inaccessible constructors, exhaustive view
matching, owner-bound lifetimes, foreign-handle errors, removal of `.body()`,
`ClosedValueScheme::new`, `Term::Leaf`, and `Term::Component`, and migration of
every workspace exhaustive match without wildcard masking.

## 33. R classification and safe expansion sharing

Generalization expands and records provisional guarded traces, completes both
polarities of every provisional owner, and computes non-generic closure,
eligibility, and incidence without rewriting. It then classifies retained R
owners *before* one-sided elimination. Retained R owners are excluded from
elimination and Q; only eligible non-R one-sided variables reduce to polarity
extremes. Q is assigned to remaining eligible bipolar non-R variables, after
which normalization, pruning, closure validation, and finalization run.

A retained trace identifies owner, entry/re-entry polarity, and an ordered path
of lower/upper bound indices, Function fields, and direct-variable edges. It
must contain a Function field, return to the same owner, survive hypothetical
non-R one-sided elimination, and complete to a nontrivial bound. Thus the root
in `my f x = f` remains R despite a positive-only census. Tests expose the
private trace and assert self/mutual guarded paths; unguarded Name cycles have
no Function step and close to Bottom without R.

The session pair memo lives from batch translation through `finish` and is
never cleared between constraints, components, drafts, or incoming routes.
Component sharing memoizes only completed root-neutral acyclic raw summaries.
A state and every dependent ancestor is uncacheable if it observes a backedge,
provisional/retained R, root-dependent completion, non-generic/boundary choice,
binder reference, or recovery/invariant state. Q/R namespaces, active stacks,
traces, elimination, pruning, and closed mapping are always root-local. Tests
draft members in forward, reverse, and rotated order and require identical
alpha-normal schemes, diagnostics, and cache counters.

## 34. Bounded closed normalization, counters, and resources

Closed union/intersection nodes remain in F5. Finalization first constructs a
cycle-safe postorder DAG. Every finalized child receives once a cached
`NormalizedKeyId`; recursive references use their already assigned R ordinal,
so key construction never follows a cycle. A node's key is its discriminator
plus child key IDs. Children are sorted by fixed-size key ID and deduplicated;
comparison and hashing never recurse. Work is
`O(N + S)`, where `N` is finalized nodes and `S = sum(k log2(k+1))` over
union/intersection arities. The earlier `O(G+N)` claim is superseded.

Public `ProductionCounters` adds every field named in §26 plus:

```text
generalization_shared_summary_admissions
generalization_uncacheable_states
generalization_shared_summary_hits
closed_normalized_key_writes
closed_normalization_child_comparisons
closed_normalization_hash_probes
closed_normalization_hash_admissions
closed_normalization_hash_duplicates
```

Rename §26's structured pair fields to the retained F4-wide names
`constraint_pair_probes`, `constraint_pair_admissions`, and
`constraint_pair_duplicates`; their F5 scope is every typed live value/effect
pair and explicitly supersedes the F4 value-row-only meaning. Every logical
counter has a public same-named `const fn -> usize` accessor.

Expose these eight resource families, each with public `requested_slots`,
`actual_capacity`, `retained_bytes`, `peak_bytes`, and `capacity_growths`
accessors:

```text
live_variable_tables
inference_type_arena
structured_pair_memo
component_expansion_memo
closed_type_arena
closed_normalization_index
generalization_scratch
instantiation_substitution
```

The test-only independent ledger enumerates every physical vector/map/set lane
inside each family, including pair entries, expansion keys/summaries, normalized
keys, sort scratch, hash-cons keys/entries, active stacks/traces, closed-node
maps, and substitution maps. Per lane it records requested length, capacity,
slot size, retained/peak bytes, growths, and clear/transfer point. Checked
aggregate sums count each lane once and reconcile all public families plus
semantic-arena and inference-session retained/peak totals. Transient families
finish at zero retained bytes. Sampling remains exactly at §26's named O(1)
boundaries and actual growth events.

Exact primitive builder deltas are those in the §26 replacement: identity
allocates 2 live values, 2 live effects, 1 Function, 5 facts, 5 direct pair
admissions, Q=1; constant allocates 3/2/1, 7 facts, Q=R=0; error allocates
2/0/0 and no facts; identity instantiation allocates one fresh value, visits
its five closed nodes, and restores no R side. The following parameterized
builders make the previously informal scale families executable:

| Builder | Construction | Exact causal expectations |
|---|---|---|
| `independent_identities(D)` | D disconnected identities | facts=5D, Q=D, R=0, shared-summary hits=0 |
| `identity_aliases(U)` | one identity plus U later incoming aliases | substitutions=U, fresh values=U, instantiation visits=5U |
| `shared_acyclic(D,K)` | D roots point to one K-node alternating-polarity acyclic cone | raw states=2K, summary admissions=2K, hits=2K(D-1), uncacheable=0 |
| `independent_acyclic(D,K)` | D disjoint copies of that cone | raw states=2DK, admissions=2DK, hits=0 |
| `guarded_cycle(D,K)` | D roots enter distinct rotations of one K-Function cycle | R writes=D, summary admissions=0 for the cyclic cone, uncacheable states=2DK |
| `normalization(D,K)` | D closed unions and intersections, each with K distinct leaf/key children | key writes=D(K+1), hash admissions=D(K+1), child comparisons equal the deterministic merge-sort comparison oracle recorded by the builder, no recursive comparison |
| `arena_factor(M,U)` | M unrelated closed nodes plus one five-node identity instantiated U times | visits=5U, fresh values=U, substitution peak slots=1, all three independent of M |

For every builder, the fixture returns its exact edge, bound, term, key, and
frontier cardinalities from construction, and tests assert each public counter
against the closed formula above or the builder's deterministic comparison
oracle. This oracle is computed while constructing integer key sequences and
does not invoke production normalization. Capacity peaks are reconciled from
the independent per-lane ledger rather than predicted allocator capacities.

Run D, K, M, or U (one named dimension at a time) at 1k/2k/4k in isolated
single-threaded processes with 30/60/120-second caps. Logical equalities must be
exact; each actual capacity/retained/peak adjacent ratio is below 2.5. Timing is
not repeated unless deterministic evidence leaves a named decision.

## 35. Additional required tests and F4 migration

Add HIR trait/owner and cross-artifact structural equality probes; all §32
compile probes; exact identity/constant/error allocation builders; proof that
live effect rows alone derive projections; every direct and Function-derived
incompatible shape with repeated-pair/multiple-cause ordering; R survival
traces; root-order cache tests; pair-memo persistence across constraints,
components, and routes; normalization work/key tests; and arena factorization.

The old occurrence-bound resource fields are deprecated zeroes. `bound_table_*`
aliases `live_variable_tables_*`; `constraint_pair_cache_*` measures
`structured_pair_memo_*`; semantic-arena totals include inference and Term
arena storage. Existing fact/provenance/SCC/scheme/route/publication counters
retain their meaning. All capacity arithmetic is checked; overflow is
`IdentityExhausted`, and a causal-cap violation is an invariant failure that
publishes no `SolvedModule`.

## 36. Final review closure: term lifetime, replay, and canonical ranks

This section replaces the conflicting parts of §§31, 32, and 34.

Collection creates one `TermArena` inside `ConstraintBatch`. All collected
endpoint recipes and `ConstraintOccurrence` handles name that arena. Before
solve, the batch is their public lookup owner:

```rust
impl ConstraintBatch {
    pub fn term_view(&self, term: Term)
        -> Result<TermView<'_>, TermLookupError>;
    pub fn term_kind(&self, term: Term)
        -> Result<ComponentKind, TermLookupError>;
}
```

`SolvedModule::solve` consumes the batch and moves the same arena, without
rebranding or remapping handles, into `ConstraintStore`. The store then exposes
the identical lookup signatures. Collection-time leaf/component interning and
solve-time live/Function interning use crate-private `TermArena` methods;
`leaf_term` and `component_term` are not public APIs. Thus a Term is inspectable
through exactly one public owner at each lifecycle phase, occurrence and fact
handles share one stable brand, and a foreign or stale-owner lookup returns
`ArenaMismatch`. Compile probes cover batch lookup before solve, store lookup
after transfer, and the absence of public construction/interner methods.

Every successfully decomposed structured-pair memo entry stores an ordered,
deduplicated cause-independent descendant diagnostic summary:

```text
DerivedMismatch {
    route: [FunctionField],
    kind: IncompatibleValue,
}
FunctionField ::= Argument | ArgumentEffect | ResultEffect | Result
```

Routes are lexicographically ordered in the fixed Function field order and
then by descendant depth. The first admission computes the summary while
performing semantic decomposition. A duplicate performs no semantic mutation
or child admission; it replays the complete cached summary under the new direct
occurrence/cause. `structured_pair_decompositions` counts only first semantic
decompositions. Add public `derived_diagnostic_summary_writes` and
`derived_diagnostic_summary_replays` counters and a corresponding physical
summary-vector lane under `structured_pair_memo`; the independent ledger and
resource totals include it. Tests require two distinct direct Function facts
whose common pair produces multiple child mismatches: each source receives the
same complete ordered set once.

`NormalizedKeyId` is never assigned by encounter order. After cycle-safe
postorder discovery, finalization constructs a descriptor for every node from
its stable discriminator, literal/binder payload, and already ranked child
descriptors. R references use alpha-normal R ordinal. For each postorder height,
all descriptors from all component drafts are collected, then sorted by a
specified stable top-down mergesort using lexicographic descriptor-word order;
byte/word equality after comparison resolves hash collisions. Equal descriptors
receive one rank and distinct descriptors receive consecutive ranks in sorted
order. Only these deterministic structural ranks order and deduplicate
union/intersection children. Ranking is independent of source traversal,
arena allocation, hash seed, and root draft order.

Replace the §34 normalization bound by `O(N + W + C)`: `N` finalized nodes,
`W` total descriptor words, and `C` descriptor-word comparisons performed by
the specified mergesort, including child-member sorts. Add public
`closed_normalization_descriptor_words` and
`closed_normalization_word_comparisons`; the normalization index owns descriptor
and mergesort-scratch lanes. The fixture oracle runs the same specified
mergesort over independently constructed integer descriptor sequences and
predicts `C` without invoking production key construction. Reversed node
allocation, reversed union input, hash collision, and root-order permutations
must yield identical ranks, normalized child order, schemes, and counters.

## 37. Finite cyclic diagnostic-summary completion

This section refines §36's diagnostic-summary cache. Each pair memo entry has
the lifecycle `Pending -> Complete`. Admission marks `Pending` before enqueueing
children. It records ordered outgoing child-pair edges and reverse parent edges;
an incompatible leaf completes with its singleton mismatch and a compatible
leaf completes empty. A duplicate seen while `Pending` appends its direct
occurrence/cause to that entry's deduplicated pending-waiter vector and performs
no replay yet.

After the semantic frontier empties, one iterative reverse-edge worklist solves
all affected summaries before `constrain` returns. A summary is a finite map
keyed by `(terminal_incompatible_pair_key, SolverErrorKind)`, not by arbitrary
walk. Each value retains the canonical route: the shortest *simple pair path*
from the entry to that terminal; equal lengths choose lexicographic Function
field order. Extending a route that already contains the next pair key is cut.
Consequently a route contains at most `P` pair keys and one entry contains at
most `I` results, where `P` is admitted pairs and `I <= P` incompatible pairs.
The worklist updates a parent only when a key is new or its canonical route
improves. Finite `(entry, terminal)` states and route ordering guarantee
termination even for Function-pair SCCs.

When an entry reaches its fixed point it becomes `Complete`; its waiters are
replayed in direct fact-admission order and cleared. A later duplicate replays
immediately. Replay emits each cached terminal kind once for that direct
occurrence, ordered by canonical route and then error kind. This phase mutates
no semantic bounds or pair graph. All affected entries must be complete and all
waiter lists empty on `constrain` return.

Replace the two summary counters with entry-level counters:

```text
derived_diagnostic_summary_entry_writes
derived_diagnostic_summary_entry_improvements
derived_diagnostic_summary_waiter_writes
derived_diagnostic_summary_replay_entries
solver_error_emissions
```

The `structured_pair_memo` resource family and independent ledger separately
account pair entries, child/reverse edges, summary map entries, route words,
worklist slots, waiter entries, and emitted-error storage, including requested,
capacity, retained/peak bytes, growth, and clear/transfer points. Exact causal
caps are: child edges `<= 4 * structured_pair_decompositions`, summary entries
`<= P*I`, route words `<= P*P*I`, waiter entries `<=` duplicate direct causes
observed before completion, replay entries and error emissions `<= causes*I`.

Add `cyclic_diagnostic_replay(C,U)`: one C-node Function-pair cycle with one
reachable incompatible leaf and U distinct duplicate direct causes admitted
before completion. It has `C` structured decompositions, `C+1` pair entries,
one summary terminal per cycle entry, routes of at most `C+1` pair keys, U
waiters, U replay entries, and U emitted errors. Run C and U independently at
1k/2k/4k under the existing isolated caps and ledger reconciliation.

## 38. Linear canonical diagnostic witness

This section replaces §§31, 36, and 37 only where they require complete
descendant mismatch sets, waiter vectors, or multiple incompatibilities per
direct source occurrence. The synchronous `constrain` boundary is unchanged:
one direct occurrence and cause enter, the semantic frontier and diagnostic
analysis drain, and the call returns with no pending state. Distinct direct
causes can therefore never wait in the same call.

Each pair-memo entry stores `Pending` or one `Complete` optional canonical
mismatch witness. A witness contains only terminal incompatible pair key,
`SolverErrorKind`, shortest distance, and the first child field/pair; it does
not own a route vector. After semantic frontier drain, a deterministic
multi-source shortest-path worklist starts from every incompatible pair and
flows over recorded reverse child edges. It uses a stable binary heap ordered
by `(distance, error kind, lexicographic Function-field path, dense pair key)`.
Equal-distance path comparison follows stored predecessor/first-edge ranks;
cycle edges never improve a settled distance. Each pair settles once and keeps
only the canonical first mismatch reachable from it. Child edges remain at
most four per structured decomposition. Work is `O((P+E) log P)`, retained
summary storage is `O(P)`, and `E <= 4P`.

The direct root pair emits at most one `IncompatibleValue` for its occurrence.
If its entry was already `Complete`, a later duplicate replays that one witness
immediately without semantic mutation. Distinct direct occurrences each emit
their own diagnostic; multiple incompatible descendants intentionally select
only the canonical first witness. Diagnostic order is therefore direct fact
admission order. This bounded cardinality supersedes the earlier complete-set
and Function-child-list requirements.

Use these counters:

```text
derived_diagnostic_witness_writes
derived_diagnostic_heap_pushes
derived_diagnostic_heap_pops
derived_diagnostic_replays
solver_error_emissions
```

The pair resource family accounts child/reverse edges, one optional witness per
pair, heap slots, and emitted errors; there are no waiter, summary-map, or route-
word lanes. Exact caps are witness writes `<= P`, heap pushes `<= 1+E` per
analysis drain, settled pops `<= P`, replays `<=` later duplicate direct facts,
and error emissions `<=` direct fact occurrences.

Replace `cyclic_diagnostic_replay` with two possible real lifecycles:

- `cyclic_witness(C)`: one C-node Function-pair cycle reaches one incompatible
  leaf; `P=C+1`, `E=C`, witness writes `C+1`, and one error is emitted;
- `cyclic_duplicate_replay(C,U)`: after the first call completes that same
  graph, U later direct duplicate facts each cause one immediate replay and one
  error, with zero additional decomposition or witness write.

Add `many_terminal_witness(C,I)`: a C-node shared structured DAG reaches I
incompatible leaves. It still stores at most one witness per pair and emits one
error for its direct root. Run C, I, and U independently at 1k/2k/4k; assert
the formulas and independent-ledger peaks exactly.

## 39. Delta-only diagnostic completion

Section 39 replaces §38's whole-session worklist wording. A pair's outgoing
children are fixed completely on its first admission and never extended.
Therefore `Complete` is immutable: no later constraint can add a shorter or
otherwise different descendant. A new `constrain` records only pair entries and
edges first admitted during that call. Diagnostic completion walks that delta
subgraph; an edge to an old `Complete` child reads its witness in O(1), and no
old entry or edge is enqueued or reopened.

New entries are completed bottom-up by an iterative pending-child-count
worklist. In the new-entry subgraph, cyclic SCCs are condensed iteratively;
each SCC receives the best seed from a direct incompatible member or an edge to
a completed/external child, then propagates it once over its internal reverse
edges. An SCC with no seed completes with no witness. Every new entry settles
once and every new edge is examined a bounded constant number of times, so one
call is `O(delta_P + delta_E)` and the session total is `O(P + E)`.

Canonical selection needs no path comparison or rank. Every structured pair
has at most one child in each distinct Function field. A pair selects the
candidate with least distance; a tie selects the lowest first field in the
fixed field order; a direct mismatch has distance zero. Inside a cyclic SCC,
multi-source FIFO layers are processed by distance and then fixed field order.
Dense pair key orders only otherwise semantically identical scheduling and
cannot change the selected error kind or first field. No route is stored or
compared.

Replace heap counters/lanes with:

```text
derived_diagnostic_delta_entries
derived_diagnostic_delta_edges
derived_diagnostic_scc_writes
derived_diagnostic_worklist_pushes
derived_diagnostic_worklist_pops
```

Each equals or is bounded by the current call's newly admitted entries/edges;
their session sums are bounded by `P`, `E`, number of diagnostic SCCs, and a
constant multiple of `P+E`. Resource accounting uses pending-child counts,
iterative SCC scratch, FIFO slots, and one witness per pair, all under the pair
family and independent ledger.

Add `disjoint_admission_stream(K,C)`: K successive synchronous direct facts,
each admitting a disjoint C-pair graph. Exact session totals are `P=KC`, the
fixture's `E=K*E_C`, delta-entry visits `KC`, and no old-entry revisit. Run K
and C independently at 1k/2k/4k. Existing cyclic and many-terminal witnesses
also assert delta rather than retained-graph work.

## 40. Canonical mismatch comparator

This section explicitly replaces §38's heap/path comparator and §39's
field-only tie wording. Candidate witnesses order by:

1. shortest distance;
2. `IncompatibleValue { lower, upper }`, comparing each `ValueShape` by the
   declared `Bottom < Int < Function` rank;
3. first Function field by Argument, ArgumentEffect, ResultEffect, Result;
4. dense pair key only as a scheduling tie that cannot change the identical
   observable witness.

There is at most one outgoing edge for each Function field. After equal
distance, error kind, and first field, candidates follow the same unique child,
so no remaining path comparison exists. Multi-source SCC buckets and FIFO
insertion use the same ordering. Focused tests put different mismatch kinds in
equal-depth Argument and Result children and assert this exact comparator under
reversed admission and allocation order.

## 41. Delimiter-scoped non-binding Pattern witness

This section resolves the F5a caller-ownership contradiction discovered during
implementation and supersedes the non-binding-consumer requirement in §20. The
user approved this amendment on 2026-09-21.

`PATTERN_STOP_ITEM` is a current-Pattern-frame capability boundary. It prevents
`PatternMlApplicationTail` admission only at the Pattern depth directly owned
by that caller. It does not disable fixed Pattern tails and is not inherited
through a Pattern-owned explicit delimiter. `parenthesized_pattern`,
`list_pattern`, and `record_pattern` replace the outer non-close stop mask with
their local comma/matching-close mask and carried `PatternCallerCloses`; the
outer Pattern resumes its original mask after the delimiter returns.

Consequently `cast(f x): A` has no application tail: Cast owns the ordinary
Item following its direct Pattern, including close/target recovery. In contrast,
`cast((f x)): A` has exactly one application tail inside the nested
`ParenthesizedPattern`; that delimiter owns its content through matching `)`.
The latter is the required genuine production non-binding witness. Shared
Pattern grammar means every consumer reaches the common parser subject to its
explicit current-frame stops; it does not authorize consuming caller-owned
recovery Items.

Required witness topology is:

```text
CastDeclaration
  CastPattern
    Pattern
      ParenthesizedPattern
        Pattern
          IdentifierPattern("f")
          Whitespace(" ")
          PatternMlApplicationTail
            Pattern
              IdentifierPattern("x")
  CastTarget(": A")
```

Keep these regressions exact:

| Source | Required disposition |
|---|---|
| `cast((f x)): A` | one inner ML tail; Cast target remains `: A` |
| `cast(f x): A` | no ML tail; existing Cast close/target recovery owns the Item |
| `cast(x else tail` with `STOP_ELSE` | `else` remains pending and CastPattern ends at its established coordinate |
| `cast(x: A): B;` | first colon is Pattern annotation; second colon is Cast target |
| `cast((f x) else tail` with `STOP_ELSE` | inner tail completes; `else` remains outer Cast-owned after synthesized outer close |

Do not permit unparenthesized direct-depth ML application in Cast, case arms,
catch handlers, or for patterns without a separately approved caller-recovery
contract.

## 42. Implementation status

F5a is complete on 2026-09-22. It implements the shared Pattern ML-application
CST/recovery contract, delimiter-scoped non-binding witness, one-parameter
Lambda HIR and lexical parameter scope, private HIR-owned evaluation
classification, and the F5a-only solver compatibility disposition. That
disposition preserves Lambda body status but emits no Function facts, live
variables, or scheme behavior; those remain F5b–F5d work. Focused syntax, HIR,
solver, doctest, workspace-check, formatting, and whitespace verification are
recorded in `tasks/current.md`; semantic, specification, and regression review
are clean.

## 43. F5c closed-extreme Term amendment

The user approved this F5c amendment on 2026-09-22. Closed `Top` and `Bottom`
may occur as Function children during incoming scheme instantiation, while
the live `Term` grammar has no ordinary variable-free value nodes for those
extremes. The private inference-term arena therefore adds closed-extreme
nodes and extends the exact `TermView` surface with `PositiveBottom`,
`NegativeTop`, and `NegativeBottom`.

These nodes are structural values, not fresh live variables. Instantiation
must preserve them directly, so a closed extreme allocates zero fresh Q/R
rows and remains compatible with the constant-scheme allocation contract.
The amendment is private to F5c closure; public structured observation,
resource-family exposure, and scale certification remain deferred to F5e.
