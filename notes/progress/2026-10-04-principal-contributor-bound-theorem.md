# Principal contributor-bound theorem attempt

Date: 2026-10-04
Status: proof candidate derived from user-directed principal schemes; not an
approved source rule or implementation authority
Scope: source-owned output effect allowance candidate for finite nonrecursive
source graphs; value endpoints and intermediate Function values remain separate

## Question

Can the expected shared components for `compose`, `twice`, `choose`, and
`higher` arise from the existing inequality solver and generalization, without
equating original endpoints or adding an effect-specific carrier?

The candidate concerns one selected covariant effect-output port `R` at a
completed source observation boundary. It does not combine arbitrary value and
effect endpoints. A source occurrence may contribute to `R` only when the
existing source typing rule and complete invocation/interface query already
place that occurrence's outward effect guarantee at this port. The proposed
constraint must then be that existing endpoint-dependent inequality, with its
source identity and evidence retained:

```text
contributor_i <: R
```

This is an ordinary endpoint query at its source boundary, not a new row
subtyping rule. Variable endpoints can be retained as bounds and propagated
transitively. Concrete endpoints are resolved locally by the one `A <: B`
solver. Successful concrete queries are never composed to create another
query. The endpoint identities and each query's `ν,K,D`, scope, occurrence,
and attachment evidence remain distinct. If existing source rules do not
generate such a query, this candidate cannot add it by assumption.

The candidate has two important limits:

- For a callback-position literal, the normative B rule still independently
  synthesizes its parameter/body/result endpoints before one completed
  `F_lit <: F_cb`; no contributor inequality copies an endpoint from the
  expected Function.
- A contributor is collected only when source introduction/elimination and
  the complete invocation relation place it at this result boundary. Merely
  sharing a printed row variable does not establish that path. `Rel_C` and
  its `K,D` fiber keep value/effect and stage correlations; separate support
  projections are not multiplied as independent Cartesian choices.

## Constraint-shape consequences

The following are projections of that single generation rule, not special
typing rules:

| Source pattern | Candidate effect-port path to the common output allowance | Value and public-row consequence |
|---|---|---|
| `call f x = f x` | the call's own invocation effect is related to `R` through the existing complete application/interface path | the call's value result remains its own endpoint; the one call row is preserved |
| `compose f g x = f (g x)` | `g`'s invocation effect and `f`'s outward effect reach `R` only through their existing staged application/interface paths | `g x`'s value flows to `f`'s argument endpoint, never directly to the final value endpoint; `g`'s effect contribution remains in outward `R`, even when its concrete attachment at `f` is witnessed, and is not subtracted for this source definition |
| `twice f x = { f x; f x }` | both invocation effects reach the outward allowance through their respective occurrence paths | block continuation and value result remain separately constrained; public support has no multiplicity, while both occurrence/evidence paths remain |
| `choose cond f g x = if cond: f x else: g x` | each branch's invocation effect reaches the common allowance through its branch path | branch value results meet at their own branch-result endpoint; source endpoints/evidence remain distinct |
| `higher f g x = f g x` | first-stage and returned-call outward effects can reach `R` only through separate staged application/interface paths | the intermediate returned Function remains its own value endpoint; public `e` may be common while stage evidence and dependencies stay correlated |

The output effect allowance is generalized with all original bounds and
residual evidence; value endpoints and intermediate Function interfaces remain
separately represented. A prospective instantiation map may send the
allowance to any valid public endpoint satisfying the retained direct
constraints. Thus the mechanical principality route would be a bound-graph
factorization theorem: each valid public view must satisfy the same
source-generated direct constraints, and the scheme's freshening map must
transport their evidence. This uses the existing scheme/bound carrier; it does
not claim that support union alone preserves a complete interface.

## Proof obligation, not conclusion

The table identifies a candidate endpoint shape, but the current source
specifications do not yet prove the source-to-`R` contributor map for general
applications, sequential blocks, and branches. The concrete-compatibility
design explicitly leaves component-to-carrier mapping and co-occurrence
consolidation open. Nor does this argument prove that every valid complete
Function view factors through the generalized endpoint, that all concrete
adapter choices are preserved, or that the finite residual has a principal
presentation.

The required same-fiber totality statement is explicit: for each original
solution fiber `ξ=(ν,K,D)` with solution set `Sξ`, every `s∈Sξ` must admit a
source-expressible, well-scoped allowance `a` such that every required direct
invocation comparison succeeds while preserving dependencies and public
observation (`∀s∈Sξ. ∃a. Qξ(s,a)`). Principality additionally requires every
valid public Function/effect view to factor through the generalized
presentation. The smallest next proof is therefore not a new row calculus:
establish the finite source-owned contributor map using existing direct
inequalities and one full fiber, then prove totality and all-view factorization
through the existing generalizer. Failure on a particular source occurrence
would identify a missing incidence/path premise; success would discharge
these clauses only for that finite grammar. Callback production adequacy,
recursive SCCs, open-world imports, and the full supported-input envelope
remain separate.
