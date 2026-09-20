# Identity-function Simple-Sub R1 supersession

Status: Reviewed

Date: 2026-09-20

Reviewed by: compiler-referee, specification, and performance M3 reviews on
2026-09-20; clean after one bounded repair/delta round.

Scope: redefine R1 as the first complete Simple-Sub definition witness. R1 is
not complete until both `my x = 42` and `my f x = x` pass from source through
canonical CST, HIR, constraint solving, polarity-aware expansion,
simplification, and definition generalization. The identity definition must
freeze a structural scheme alpha-equivalent to `forall a. a -> a`.

Upon user approval, this successor:

- supersedes `2026-09-20-simple-sub-direct-int-expansion-supersession-draft.md`
  only where its R1/R2 boundary makes integer-only completion sufficient or
  forbids the parameter, local-scope, function, bipolar-variable, and scheme
  work required by `my f x = x`;
- retains that record's canonical `Int`, direct integer occurrence value,
  `Int <: definition.value`, positive expansion, effect, provenance,
  failure-isolation, resource, and integer-witness contracts;
- supersedes the 2026-08-20 syntax architecture's ML-application-Pattern
  deferral only for the canonical Pattern form below;
- supersedes the first HIR module slice's parameter-pattern and local-scope
  exclusion only for one recovery-free, unannotated identifier argument;
- narrowly supersedes the completed directed-integer slice's literal value
  component, two literal value facts, exact lower/upper `Int` projection, and
  polarized `Int` leaves; it retains artifact identity, exact-pure occurrence
  effects, ordered constraint collection, store/provenance authority, recovery,
  local failure isolation, and dependency boundaries;
- narrowly supersedes the completed binding-root slice's body value component,
  `body.value <: definition.value` fifth fact, valid-root `Unknown`, peer
  `root_values` authority, and associated exact construction/resource counts;
  it retains definition-root identity, one directed value flow into that root,
  append-only store/provenance ordering, no definition effect, recovery and
  cross-kind isolation, and downstream dependency boundaries;
- does not revive the superseded integer scheme/name proposal.

Function application expressions, scheme instantiation at module-name uses,
recursive inference, multi-parameter HIR semantics, richer parameter patterns,
general effect inference, Core IR, and runtime behavior remain out of scope.

## Why the former R1 is insufficient

Current syntax does not accept `my f x = x` as one binding. It closes
`BindingStatement("my f")` before `x` and publishes `x = x` as root recovery.
Current HIR also has no parameter identity, lambda/function expression, local
scope, or nested expression occurrence. Current `yu-types`/`yu-solver` cannot
represent a function, a quantified scheme, or one variable occurring in both
negative and positive positions.

The frozen `yulang2-oracle@a58eefc31e22141574b6f20c6a5748151` proves the
required semantic chain: header arguments lower to lambdas; body `x` resolves
to the same monomorphic parameter variable; function arguments traverse in
negative polarity and results in positive polarity; bipolar variables survive
simplification and are quantified at the definition boundary. Its observable
scheme is exactly `'a -> 'a`.

## R1 completion contract

R1 closes only when the following derivation is structural, not formatter-made:

```text
source:       my f x = x
parameter:    alpha
body value:   alpha
function:     Function(alpha-, pure, pure, alpha+)
definition:   Function(alpha-, pure, pure, alpha+) <: rho_f
expansion:    rho_f | Function(alpha-, pure, pure, alpha+)
simplify:     Function(alpha-, pure, pure, alpha+)
generalize:   forall alpha. alpha -> alpha
```

`alpha` is one identity referenced from both positions. Two unrelated unknowns,
an opaque `Function` tag, an exact-bound shortcut, equality, reciprocal edges,
or display-only substitution do not satisfy R1.

## Canonical Pattern syntax

R1 reopens syntax-v0 for canonical ML application in Pattern. Binding continues
to consume one canonical `Pattern`; there is no binding-only parameter parser.

The approved candidate topology is:

```text
BindingHeader
  MyKw
  Pattern
    IdentifierPattern("f")
    Whitespace(" ")
    PatternMlApplicationTail
      Pattern
        IdentifierPattern("x")
  Equals
```

The canonical production is:

```text
PatternMlApplicationTail := Gml Pattern@MlApplication
```

`Gml` is one nonempty maximal trivia run. It is admitted when it contains no
newline, or when every newline is followed by indentation deeper than the
Pattern baseline. A same-line comment is part of that run; a newline after it
must satisfy the same deeper-indent rule. An equal-or-shallower newline rolls
the entire run back to the caller unchanged. `Pattern@MlApplication` admits an
argument only when the next token is a canonical Pattern NUD start.

The tail judge order is active caller boundary/stop first, then the existing
exact Alias, Pipe/Alternation, and terminal annotation tails where applicable,
then ML application only when no existing fixed tail wins. Thus `f as y`
retains its Alias tree rather than treating contextual `as` as an ML argument;
`f (as)` is the unambiguous application form when `as` is intended as an
identifier argument.

`PatternMlApplicationTail` is a new Pattern-owned node. Its argument payload
begins at the nested Pattern; the nonempty separating trivia remains a direct
child of the enclosing Pattern. Repeated arguments are forward sibling tails.
The nested argument parses with ML continuation disabled, so `f x y` means
siblings `f`/`x`/`y`, never `f (x y)`.

ML application has the tightest fixed Pattern precedence. Alias, alternation,
and a terminal type annotation remain outside an unparenthesized application:
`f x as y`, `f x | g y`, and `f x: T` retain those outer owners. Active stops,
`=`, caller closes, fences, Item, a non-NUD token such as `@`, and an
equal-or-shallower layout boundary create no tail: trivia and token are returned
unchanged to the caller. A tail opens only after a Pattern primary and a real
argument payload are admitted; trailing trivia alone creates no wrapper or
`Missing`. Once an argument child is admitted, malformed continuation inside it
is recovered by that nested Pattern under its existing owner and caller-stop
rules. No relex, replay, or source rescan is allowed.

This canonical syntax is available to every Pattern consumer. Consequently,
`(a b)` and `[a b]` contain one application-pattern item rather than two items
separated by a synthesized missing separator. These are approved specification
changes to expectations in `tests/pattern.rs` and
`tests/pattern/recovery/{delimited,sequence}.rs`, not edits merely following
implementation output. Record-field sequence behavior for `{a b}` is unchanged.

R1 HIR semantics deliberately admit only one
`PatternMlApplicationTail(IdentifierPattern)` with no annotation or recovery.
Repeated tails and every other application-pattern argument remain total
`UnsupportedTarget` HIR in R1 even though the CST preserves them canonically.

## HIR parameter, scope, and occurrences

For the admitted shape, HIR separates the definition head `f` from the ordered
one-element parameter list. It retains the existing `DefId` and
`DefinitionRootId` for `f` and introduces a distinct artifact-owned
`HirParameterId`, keyed by exact HIR artifact, owning definition root, and
parameter ordinal. Spelling and source range are payload, never identity.

```text
ResolvedExpr::Lambda {
    occurrence,
    parameter: HirParameterId,
    body: Box<ResolvedExpr>,
    range,
}

NameResolution::Parameter(HirParameterId)
```

`HirBinding` is the sole owner of the ordered `HirParameter { id, name, range }`
list; Lambda stores only its owned parameter ID, and
`HirBinding::parameters()` is the sole parameter-record query. Parameter scope
is exactly the Lambda body. A rejected parameterized target has no
binding/root/parameter list. The lambda and body have distinct artifact-branded
occurrences minted by one module-local preorder allocator;
the allocator replaces root-index reuse and fails on ordinal exhaustion before
freezing HIR.

Body resolution is local-first, then module namespace. Therefore
`my x = 0; my f x = x` resolves the body `x` to the parameter, not the module
definition. Scope is restored on every success and error path. Parameter IDs
are never `DefId`s, definition roots, spelling keys, or source offsets.

## Open terms and closed schemes

`yu-solver` owns open position-typed terms. R1 introduces exactly the structure
needed by its two witnesses:

```text
OpenValueId ::= Definition(DefinitionRootId) | Parameter(HirParameterId)

PositiveValue ::= Int | Variable(OpenValueId)
                | Function {
                    argument: NegativeValue,
                    argument_effect: NegativeEffect,
                    result_effect: PositiveEffect,
                    result: PositiveValue
                  }
NegativeValue ::= Variable(OpenValueId)

PositiveEffect ::= Bottom | Variable(EffectComponentId)
NegativeEffect ::= Variable(EffectComponentId) | EmptyRow
```

Constraint endpoints use the same positional grammar: a positive effect
endpoint is `Bottom` or `Variable(component)`, and a negative effect endpoint
is `Variable(component)` or `EmptyRow`. Thus all four exact-pure occurrence
facts below are constructible without an unchecked endpoint escape hatch.

Constructors are solver-private. R1 adds no negative function, generic
union/intersection node, uniform unchecked `Term`, equality, or union-find.
The logical root union remains a transient expansion view.

The function node contains explicit latent effects. An unannotated parameter
has the negative pure endpoint `NegativeEffect::EmptyRow`; the identity result
effect expands to the positive pure endpoint `PositiveEffect::Bottom`.
Function construction and body-name evaluation retain
separate exact-pure occurrence effects and do not enter the value scheme.

`yu-types` owns the closed structural result:

```text
ClosedValueScheme {
    binders: [BoundValueBinder(0)],
    body: ClosedValue::Function {
        argument: BoundValue(0),
        argument_effect: Pure,
        result_effect: Pure,
        result: BoundValue(0),
    },
}
```

Both bound references must point to binder 0. Normalized rendering for this
witness is `'a -> 'a`; structural equality, not rendering, is authoritative.

## Exact identity constraints

Let `alpha` be `OpenValueId::Parameter(x)`, `epsilon_x` the body-reference
effect component, `epsilon_lambda` the function-construction effect component,
and `rho_f` the definition root.

The body occurrence carries direct known open value `alpha`; local parameter
use does not instantiate a scheme and allocates no body value component or
value fact. The only value fact is:

```text
Function {
  argument: Variable(alpha) in negative position,
  argument_effect: EmptyRow,
  result_effect: Variable(epsilon_x) in positive position,
  result: Variable(alpha) in positive position,
} <: RootVariable(rho_f)
```

Pure occurrence effects are:

```text
Bottom <: epsilon_x      <: EmptyRow
Bottom <: epsilon_lambda <: EmptyRow
```

The body occurrence owns its two `epsilon_x` facts. The Lambda occurrence owns
its two `epsilon_lambda` facts and the Function-to-root fact. Admission follows
preorder occurrence order, then that fixed local slot order. The admitted
Function-to-root fact is the sole authority for the Lambda's open value during
solving; no duplicate known-open occurrence payload is retained.

One identity witness therefore has one parameter identity, one definition-root
identity, two effect components, five semantic facts and receipt-provenance
edges, one lambda occurrence, and one body occurrence. It has no definition
effect and no hidden lambda/body value variable.

## Expansion, simplification, and generalization

`ConstraintStore` remains the sole authority for directed semantic facts.
Definition processing runs once in source order over the accepted lower facts:

1. expand `rho_f` through its function lower;
2. traverse the function domain negatively and its result positively;
3. expand positive `epsilon_x` through its `Bottom` lower;
4. eliminate positive-only `rho_f` and the pure effect variable;
5. retain `alpha`, because the same identity occurs negatively in the argument
   and positively in the result;
6. quantify exactly that candidate-owned, environment-free `alpha`, in first
   structural-occurrence order.

The R1 negative base case is
`expand-(Parameter(alpha), no upper bounds) = Variable(alpha)`. It records the
negative incidence for the polarity census without eliminating or replacing
`alpha`. Any negative upper bound or negative structural expansion is
`UnsupportedValueExpansion` in R1.

The expansion form and polarity census are solve-workspace views, never new
semantic facts or provenance edges. R1 permits only the direct `Int` lower, the
one positive Function lower above, candidate-owned parameter variables, and
bounded pure-effect expansion. A second lower, recursive root graph, foreign
open variable, negative-function requirement, or unbounded traversal yields
`UnsupportedValueExpansion` before a solved module freezes.

## Definition result authority

Every admitted root has one dense result:

```text
DefinitionSchemeState ::= Generalized(ClosedValueScheme)
                        | NotGeneralized(DefinitionSchemeFailure)
```

`SolvedModule::scheme_state_for(root)` is the sole retained definition-type
authority and rejects foreign artifacts. The former peer `root_values` result
is removed rather than retained beside a scheme.

The integer witness now freezes the zero-binder scheme `int` through the same
definition-result path. Its occurrence remains direct `Known(Int)`. The
identity witness freezes the one-binder function scheme above. Existing solved
occurrence observations remain closed `Known(Int)` or `Unknown`. R1 does not
retain or expose solver-private open terms after generalization: the Lambda and
parameter-use occurrences project `Unknown`. Their relationship is
authoritative through the frozen definition scheme and constraint/provenance
evidence only.

Only an admitted definition root receives a dense scheme state. A
malformed/recovered/unsupported target is a HIR error with no binding, root,
parameter, or scheme state. An admitted one-parameter binding whose body is
unsupported receives one of these finite failures:

```text
DefinitionSchemeFailure ::= UnsupportedBody
                          | UnsupportedNameValue
                          | FailedRequiredFact
                          | FailedRequiredComponent
```

An unresolved name is `UnsupportedNameValue`; so is every resolved module name,
including `my f x = f`. Only `NameResolution::Parameter(parameter)` admits the
identity body. No such failure emits a substitute Function fact. Failure of
either occurrence-effect component or the Function/root fact makes the owning
definition `NotGeneralized`; a failed interval is never simplified as pure.
Local `CrossKind` failure marks the involved component and dependent definition,
while later independent definitions continue. Artifact, parameter-ownership,
receipt, missing-state, identity-exhaustion, and solver-invariant failures are
availability failures and prevent freezing `SolvedModule`.

`UnsupportedValueExpansion` is also a solve availability error, not a dense
definition failure: a distinct second lower, recursive/foreign/negative
structure, or unbounded expansion prevents any `SolvedModule` from freezing.

## Fact and lifecycle registry

| Fact | Identity key | Sole writer | Reader / lifecycle |
|---|---|---|---|
| parameter | HIR artifact + definition root + ordinal | HIR binding lowering | local resolver and solver collection; retained in HIR |
| expression occurrence | HIR artifact + preorder ordinal | HIR preorder allocator | collection and solved occurrence query; retained in HIR/result |
| known body open value | parameter ID | solver collector | used transiently to build the Function lower; not retained after solving |
| directed semantic fact | artifact + canonical endpoints | `ConstraintStore` admission | expansion and explanations; retained with receipt provenance |
| expansion/polarity census | definition root | solver workspace | simplification/generalization; transient |
| binder candidate/order | definition root + first structural occurrence | generalizer | closed-scheme builder; transient |
| closed scheme | canonical structural binder/body | `yu-types` constructor called by generalizer | dense definition state; retained |
| definition scheme state | definition root | solver finalizer | `scheme_state_for`; retained and dense for admitted roots |

The Function lower is built once from the parameter identity and then owned by
the store fact. The generalizer reads only accepted store facts and workspace
views; it never reconstructs meaning from cause order, source spelling, or a
second HIR/CST traversal.

## Atomic R1 gate

R1 may use internal commits, but it is one completion gate and is not declared
complete until all of these are integrated:

1. canonical Pattern ML-application CST and recovery;
2. parameterized-binding HIR, parameter identity, local-first scope, and nested
   occurrence allocation;
3. canonical `Int` and the direct integer correction retained from the former
   proposal;
4. position-typed open Function terms and exact pure occurrence effects;
5. directed Function/Int lower facts, bounded polarity-aware expansion,
   simplification, and definition generalization;
6. structural closed schemes and the sole dense definition-scheme query;
7. focused behavioral and production-counter verification.

No intermediate state in which the parser accepts the function but HIR drops
its parameter, or HIR constructs it but the solver returns `Unknown`, closes
R1.

## Required witnesses

- exact lossless CST and zero diagnostics for `my f x = x`;
- sibling Pattern topology for `f x y`, `f x as y`, `f as y`, `f (as)`,
  `f x | g y`, `f x: T`,
  `(a b)`, `[a b]`, boundaries, layout, and recovery;
- a non-Binding Pattern consumer proving the syntax is canonical rather than a
  binding-only branch;
- HIR lambda/body distinct occurrences, one parameter identity, exact ranges,
  foreign-artifact rejection, local shadowing, and alpha-renaming;
- exact five identity facts and their directions; no equality, upper function,
  reverse root edge, definition effect, module-name instantiation, or hidden
  body/lambda value component;
- structural scheme equality to `forall binder0. binder0 -> binder0`, with the
  same binder at both positions and exact pure latent effects;
- retained `42` and `my x = 42` direct-Int/zero-binder-scheme witnesses;
- two identities use distinct internal parameter/binder IDs but alpha-equivalent
  schemes;
- `my f x = missing`, malformed/recovered parameters, a second argument,
  annotated/destructured parameters, and `my f x = f` do not fabricate the
  identity scheme;
- direct expression application `f 1` remains unsupported.

More exactly, malformed/recovered, second-argument, annotated, and destructured
parameter targets are `HirItem::Error` with no definition root or scheme state.
`my f x = missing` and `my f x = f` admit the binding/root but freeze
`NotGeneralized(UnsupportedNameValue)` with no Function fact; the latter remains
ordinary resolved module/self-name syntax and does not authorize recursion or
scheme instantiation. Direct expression `f 1` retains its existing
`UnsupportedExpression` HIR contract.

## Resource contract

For `N` independent `my f_i x_i = x_i` definitions, require exactly `N` roots,
parameters, lambda nodes, nested body occurrences, dense scheme states,
generalized schemes, scheme binders, and closed function bodies; `2N` effect
components; `5N` facts and provenance edges; and `N` definition expansions,
polarity censuses, simplifications, and generalizations.

Those censuses visit exactly `N` function nodes, `2N` `alpha` incidences, `N`
pure-effect-variable incidences, `N` root eliminations, `N` pure-effect
eliminations, `N` binder candidates, and `N` quantification sites. Counts also
include the retained parameter-list records/references, dense scheme states,
and closed scheme/function storage; there is no retained open occurrence
projection.

Collection performs one HIR traversal and generalization one definition-order
pass. There is no CST rescan, per-root store scan, parallel typed tree, SCC,
generic closure worklist, cache/invalidation scheme, or eager explanation.
Counters cover nested traversal/occurrence allocation, parameter/lambda and
scheme/binder/function allocations, copied spelling bytes, open-term nodes and
variable incidences, facts/components/receipts/provenance, expansion polarity
visits, eliminations, binder visits, all index probes/rebuilds/capacities, clone
counts/payload bytes, and retained/peak workspace bytes.

The 1,000/2,000 witnesses use unique definition and parameter spellings and
require linear counts and less-than-2.5x work/retained-byte growth. Timing is
introduced only if counters expose a second scan, superlinear probes/bytes,
repeated rebuilds, per-root global work, nontrivial clone growth, or a
cache/worklist requirement.

Let `P` be total Pattern ML tails in a module. Parsing/CST allocation and direct
HIR header validation are `O(P)` through one direct-child traversal, with zero
source/CST rescans and no per-tail map or set. A large unsupported repeated-tail
witness records exactly `P` tail allocations and at most `P` HIR tail visits;
the second-tail rejection path may consume the remaining chain once but never
restart it, so it is not `O(P^2)`.

## Stop and rollback conditions

Stop before or roll back R1 if the witness requires a binding-only parser, CST
replay, a second syntax tree, range/spelling identity, module-name lookup for
the parameter, equality or reverse edges, two argument/result variables, a
hidden value variable, root-to-body copying, generic union-find/SCC closure,
parallel typed HIR, peer root-type/scheme authorities, or if `alpha` is erased
instead of quantified.

## Approval choice

Recommended choice: approve this integrated R1 with canonical repeated Pattern
ML-application syntax, one-identifier-argument HIR semantics, explicit pure
function effects, direct local reuse of one parameter variable, structural
closed schemes, and completion only at the two end-to-end definition witnesses.

Narrow alternative: canonical Pattern syntax accepts only one ML argument in
this gate. This reduces initial syntax surface but requires another grammar
reopen for ordinary curried headers. A binding-only parameter syntax is not an
available alternative.
