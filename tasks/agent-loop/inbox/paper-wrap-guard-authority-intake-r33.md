# R33 operational `wrap` graph-guard authority intake

Status: **OPEN authority gap; no constructor classification adopted.**

## Decision owner and scope

The unresolved rule belongs to the operational manuscript's `rec`/finite-graph
guard authority. The current task record assigns Luna the authority-intake
role. It does not identify a separate named human manuscript owner. The source
SCC/closure owner can establish how source bindings and references are captured,
but that evidence cannot determine the operational manuscript's runtime graph
guard rule.

The pinned operational manuscript is a research derivation, not an approved
production specification. No governing approved `wrap` guard clause or
wrap-specific approved answer was found in the pinned source set and targeted
question-board search. No semantic choice is made by this intake.

## What the current operational text establishes

- O `:151–165` includes `wrap(v,a,r)` in the value grammar and identifies `a`
  and `r` as argument/result adapter code.
- O `:184–185` says recursive value graphs cycle through actual data, lambda,
  or delay constructors and exclude alias/roll/type-evidence-only cycles. It
  does not state the `wrap` case.
- O `:224` types `wrap(f,a,r):C(A',B')` from `f:C(A,B)`, an argument adapter
  `a(z):A` under `z:A'`, and result adapter `r(z):B'` under `z:B`.
- O `:258–268` makes `H` a finite immutable value graph, `Xi` a reference-type
  map, and graph typing the conjunction of each node's type derivation and the
  preceding guard condition. It gives no constructor-indexed `wrap` edge or
  guard clause.
- O `:362–376` separately defines call entry: it peels outer wraps, constructs
  a delayed argument computation, saves result adapters, and does not execute
  the argument adapter during peeling. This runtime entry rule is not a head
  observation/guard rule for recursive graph typing.
- O `:1002–1008` uses guarded graph observation in callable shape reasoning and
  says a callable graph can expose lambda/wrap, but does not say which child
  edges of `wrap` observation follows or whether wrap itself guards a cycle.
- The pinned source manuscript S has its own closure/SCC grammar. Its source
  capture account is useful correspondence evidence, not authority to complete
  the omitted operational rule. `PaperExecutionSyntax.lean` is raw syntax
  evidence, not a semantic edge definition.

## Decision questions the governing rule must answer

1. When a typed graph observer reaches `wrap`, does this node itself count as
   the required guard, does observation continue through the wrapped function,
   or do both facts hold in a specified way?
2. If it follows the function child, which exact edge is followed and in what
   order across nested wraps? How does the observation retain the outer type
   `C(A',B')`, inner type `C(A,B)`, and both adapter typing derivations?
3. Are adapter computations graph edges at head observation, deferred code
   stored without being traversed, or traversed under a distinct rule? If
   references occur only inside adapter code, what establishes their capture,
   typing, and eventual cycle relevance?
4. What exact guard judgment applies to a cycle consisting only of a wrap and
   its function reference? Is the answer the same when the function child is
   itself another wrap?
5. Which finite-graph node premise and cycle criterion ensure the rule composes
   with O `:258–268` and supports the callable shape argument at O `:1002–1008`?

These questions must be answered together. “Peel wraps at call entry” alone
cannot settle head observation because call entry is a later operational
transition and the argument adapter is explicitly deferred there.

## Discriminators, not conclusions

**Function-position cycle.** Candidate graph:

```text
Xi(r) = C(A,A)
H(r)  = wrap(graphReference(r), idArg, idResult)
path  = r → wrap.function → r
```

O `:268` types the reference and O `:224` gives the wrapper typing shape,
provided the identity adapters have their ordinary code typings. If wrap is a
guard, the cycle passes the constructor test; if the function edge is
transparent and wrap does not guard, it fails as an unguarded self-cycle. A
rule could also define a different combination; no branch is selected here.

**Adapter-only reference.** Put a recursive reference only in deferred argument
adapter code while the wrapped function is a lambda with no such recursive
reference. This distinguishes “follow every nested syntax child” from “follow
the callable function edge only.” The typed finite-heap admission and the exact
edge for adapter code are unestablished until the governing rule says how
adapter code is represented and typed in `H`.

## Authority route and remaining evidence

First seek an existing accepted correction or an explicit constructor clause
from the operational manuscript's `rec`/graph authority. If none exists, the
source owner must provide an unadopted rule proposal that answers all five
questions and preserves the exact wrapper/adapter type evidence. Any proposal
that changes the operational language semantics must receive independent review
and explicit user approval before it becomes authoritative or guides code.

The source SCC/closure owner may separately provide exact source-to-graph
capture evidence for adapter references. That can answer correspondence
premises only; it cannot choose whether the operational `wrap` constructor
guards or what graph typing observes.

No `wrap` classification, rank measure, graph theorem, implementation slice,
expected-output change, or parent-gate transition follows from this intake.
The full paper guard, recursive graph extension, typed observation,
source/native correspondence, A/B and production gates remain **OPEN**.

Next evidence owner: Luna, operational manuscript authority intake. Stop if a
semantic selection is required; route that choice through the existing
independent-review and user-approval process.
