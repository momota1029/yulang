# Principal contributor-bound theorem attempt

Date: 2026-10-04
Status: proof candidate; the standalone contributor-inequality shortcut is
withdrawn after a conformance audit; no source rule or implementation authority
Scope: source-owned output effect allowance candidate for finite nonrecursive
source graphs; value endpoints and intermediate Function values remain separate

## Question

Can the expected shared components for `compose`, `twice`, `choose`, and
`higher` arise from the existing inequality solver and generalization, without
equating original endpoints or adding an effect-specific carrier?

The candidate concerns one selected covariant effect-output port `R` only as a
projection of a completed Function comparison at a source observation
boundary. It does not license an independent query `contributor_i <: R`:
Function effect ports are not independently-subtyped general Types. The one
`A <: B` solver must compare both effect descriptors jointly inside the
complete Function inequality, using its existing `ν,K,D`, scope, occurrence,
and attachment evidence. This note has not derived how an outward contributor
is represented by that coupled query or how its principal common allowance is
projected. A row-support inclusion written by itself would add an unapproved
effect-subtyping relation.

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

The following are candidate source projections through the complete coupled
Function comparison, not special typing rules or independent effect checks:

| Source pattern | Candidate source projection in the coupled Function comparison | Value and public-row consequence |
|---|---|---|
| `call f x = f x` | the call's own invocation effect is related to `R` through the existing complete application/interface path | the call's value result remains its own endpoint; the one call row is preserved |
| `compose f g x = f (g x)` | `g`'s invocation effect and `f`'s outward effect reach `R` only through their existing staged application/interface paths | This annotation-free source has no written capture contract, so full hygiene applies: `g x`'s value flows to `f`'s argument endpoint, while its effect contribution remains in outward `R`. An inferred matching component at `f`'s port alone does not grant capture/subtraction. |
| `twice f x = { f x; f x }` | both invocation effects reach the outward allowance through their respective occurrence paths | block continuation and value result remain separately constrained; public support has no multiplicity, while both occurrence/evidence paths remain |
| `choose cond f g x = if cond: f x else: g x` | each branch's invocation effect reaches the common allowance through its branch path | branch value results meet at their own branch-result endpoint; source endpoints/evidence remain distinct |
| `higher f g x = f g x` | first-stage and returned-call outward effects can reach `R` only through separate staged application/interface paths | the intermediate returned Function remains its own value endpoint; public `e` may be common while stage evidence and dependencies stay correlated |

### Direct source-level consequence for annotation-free `compose`

With nothing written about capture, hygiene applies fully by default. Under
that source-level rule and the draft Function denotation in
`2026-10-01-coupled-effect-interface-core-draft.md` § candidate Function
contract, the effect-preservation part of `compose` follows directly from
source execution. Fix the same `ν,K,D` fiber and a composition derivation whose
application relation passes `g x`'s inert whole-argument carrier `D_g` to
`f`'s Value-entry port. Take any request `q` in an observed prefix of the
designated `Force(D_g)`. The entry expansion runs
`Force(D_g) >>= RebindResultPath >>= B_f`; stateful bind preserves that same
request origin and its `K,D` incidence. Since the source writes no capture
contract, the default full hygiene prevents a handler inside `f` from
consuming this caller-owned `q`. The complete `Beh(f,D_g)` therefore exposes
the same event at `f`'s call boundary. The candidate Function contract for
`f` then requires that event to belong to its covariant output row. The outer
`compose` body exposes that contribution under the same assignment and
evidence fiber. This
derives the source-level reason `g`'s contribution must be admitted by outward
`c`; it does not compare an effect port independently or infer a subtraction
from matching row-variable spelling.

This closes only the source-execution inclusion for observations already
present in `Force(D_g)` and the stated Value-entry path. It does not prove that
production endpoint constraints denote the complete `Beh` relation, that
their finite Function comparison projects to this inclusion, or that every
original solution has a representable principal `c`. Those are the remaining
endpoint and scheme obligations below.

If the coupled Function source rule constructs an output allowance, it must be
generalized with all original bounds and residual evidence; value endpoints
and intermediate Function interfaces remain separately represented. A
prospective instantiation map may send the allowance to any valid public
endpoint only through the retained whole-interface constraints. The mechanical
principality route would therefore be a factorization theorem for complete
Function comparisons and their joint evidence, not a bound graph of
independently-subtyped effect components. Support union alone does not preserve
a complete interface.

## Proof obligation, not conclusion

The table identifies a candidate endpoint shape, but the current source
specifications do not yet prove the source-to-`R` projection through complete
Function comparisons for general applications, sequential blocks, and
branches. The concrete-compatibility design explicitly leaves
component-to-carrier mapping and co-occurrence consolidation open. Nor does
this argument prove that every valid complete
Function view factors through the generalized endpoint, that all concrete
adapter choices are preserved, or that the finite residual has a principal
presentation.

The required same-fiber totality statement is explicit: for each original
solution fiber `ξ=(ν,K,D)` with solution set `Sξ`, every `s∈Sξ` must admit a
source-expressible, well-scoped allowance `a` such that the generated complete
Function inequalities jointly succeed while preserving dependencies and
public observation (`∀s∈Sξ. ∃a. Qξ(s,a)`). Principality additionally requires
every valid public Function/effect view to factor through that generalized
presentation. The candidate still lacks the source-to-complete-Function
projection that would establish `Qξ`; treating an effect contributor as a
standalone lower bound is not an available shortcut. Callback production
adequacy, recursive SCCs, open-world imports, and the full supported-input
envelope remain separate.
