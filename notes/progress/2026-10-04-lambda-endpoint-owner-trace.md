# Current Lambda endpoint owners and the remaining denotation law

Date: 2026-10-04
Branch: `research/simple-sub-intrusion`
Base: `9520e76683f18ce3e96caed9cd92219de61cd925`
Status: read-only production trace; no implementation authority

## Scope

This trace checks whether the current production owners for the bounded
`id x = x` and `zero x = 0` Lambda forms already determine the complete local
relation required by the callback endpoint bridge. It reads HIR collection,
`LambdaRecipe`, Lambda fact admission, `TermView`, and the returned
`SolvedModule`. No tests or builds were run.

## What the owners preserve

| Stage | `id x = x` | `zero x = 0` |
|---|---|---|
| HIR | Parameter `HirParameterId` is referenced by the body Name. | Integer spelling, range, and occurrence are retained. |
| Collection | `emit_lambda` recognizes the matching own parameter; `body_value_component = None`. | `emit_integer` creates separate body value/effect components; the recipe stores the value component. |
| Lambda admission | Function argument and result use opposite polarities of the same live parameter ordinal. | Function argument uses the parameter ordinal; result uses the distinct body value ordinal constrained by Int facts. |
| Solved output | Original HIR and constraint store remain available. | Original HIR retains the numeral; constraint facts preserve its Int type, not its spelling. |

Relevant owners:

- `yu-hir/src/module.rs:361,426,1157,1200,1402` — parameter identity,
  resolved Lambda/Integer/Name forms, scope-sensitive name lowering, and the
  current non-leaf application boundary.
- `yu-solver/src/lib.rs:687,1039,1452,1555,10537` — `LambdaRecipe`, collection,
  Int constraints, source-body distinction, and the admitted positive Function
  fact.
- `yu-solver/src/term.rs:170` — four Function child handles and live type
  variable coordinates.
- `yu-solver/src/lib.rs:2912,3271,15417,15637,15666,15675` — retained HIR/store
  and public projection. `LambdaRecipe` itself is session state; the finished
  module keeps its HIR and admitted facts, not the recipe object.

The admitted Function fact is structurally:

```text
PositiveFunction(negative parameter, EmptyEffectNegative,
                 positive body effect,
                 positive parameter OR positive body value)
    <: definition root
```

It records type-level port sharing and occurrence provenance. The shared
parameter ordinal is a type coordinate; it does not itself establish equality
of runtime input/output value roots. Likewise, an Int bound on the literal
body component does not establish its complete observation relation.

## Exact production bridge still missing

Neither an exact source relation nor the reviewed scalar `Sat_j` relation is
identified by the current endpoint trace. Retained HIR distinguishes the two
bodies; the Function fact and Int bounds do not define complete value-root
relations, decorated configuration tuples, receipt/path transport, or
full-bound inversion. In particular, those Int facts alone do not certify
`Sat_j(a,v,C,C')`, its projected observation contract, capability
preservation, or shared actual/checked generation.

Thus there is no code-grounded conclusion yet that the endpoint is endpoint-
only or that it denotes the exact `name`/literal execution graph. HIR/store
retention makes either proof route possible without a new carrier, but does
not prove either route. The next proof obligation is the endpoint realization
law from [production callback endpoint generation](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
§4: identify the source-owned local `Rel_j` each retained endpoint fact
denotes, then prove the checked Pure endpoint is its full-tuple-preserving
total-coordinate extension. For the scalar candidate, also show how its
first-order projected contract is admitted at the production Function bound;
the existing local abstraction theorem does not close that correspondence.
