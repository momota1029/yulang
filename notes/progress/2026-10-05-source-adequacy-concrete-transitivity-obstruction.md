# Concrete transitivity obstruction in the legacy source-adequacy fragment

Date: 2026-10-05
Status: exact counterexample to lifting the conditional preorder theorem to complete Yulang `A <: B`; no replacement typing rule or implementation authority
Scope: applicability of the candidate pure expression / recursive-group generation adequacy proofs
Governing decision: variable-bound propagation may use transitivity; successful concrete comparisons may not be composed. Optional-record witness: [concrete compatibility boundary](../design/2026-10-03-concrete-compatibility-boundary.md#1-governing-semantic-decision)
Audit: independent compiler-referee and source-interface review

## Result

The candidate pure source-typing and recursive-group adequacy theorems are
valid only for their declared global-preorder structural fragment. Their
completeness arguments cannot be reused for the complete endpoint-dependent
Yulang inequality solver, because the source typing rules permit successive
concrete subsumption checks while generation compresses them to one direct
endpoint comparison.

This does not refute the conditional theorems in their restricted fragment,
nor the operational complete-interface simulation in
[`source-interface-adequacy-theorem.md`](../design/2026-10-02-source-interface-adequacy-theorem.md).
It identifies a missing bridge between concrete source typing with local
compatibility/adaptation checks and a generated direct inequality.

## Smallest source counterexample

Use the approved optional-record observations:

```text
A = {foo?: string}
B = {}
C = {foo?: int}

A <: B    succeeds
B <: C    succeeds
A <: C    fails
```

For the expression `x` with `Γ(x)=A`, the candidate declarative typing rules
can derive `Γ ⊢ x : B` by one `Sub`, then `Γ ⊢ x : C` by a second `Sub`.
Both checks are individually successful local concrete inequalities. The
candidate generator's `Name` rule instead emits the anchor `A` with no
constraints. Its completeness conclusion for the typing at `C` would require
the direct comparison `A <: C`, which fails. This is not a counterexample to
the restricted theorem when its carrier really is a preorder; it is a
counterexample to identifying that carrier relation with all successful
Yulang concrete resolutions.

The recursive-group theorem has the same failure at its exact transitivity
step. Let a member body be `x`, let its declarative body type be `T_d=B`, and
choose `S_d=R_d=C`. The two `RecGroup` inequalities hold by the local checks
`B <: C`; generation emits `A <: s_d` and `A <: r_d`, which cannot be
satisfied by those chosen endpoints because `A <: C` fails. Thus the proof at
[`pure-recursive-group-adequacy.md`](2026-09-30-intrusion-pure-recursive-group-adequacy.md)
§ Adequacy theorem, which obtains generated edges from
`eval(t_d) ≤ T_d ≤ S_d/R_d`, needs transitivity of assigned concrete values.

## Exact boundary

- Transitive propagation of `X <: Y` variable bounds remains allowed by the
  selected endpoint-dispatch contract, subject to its retained context and
  replay obligations.
- Transitivity inside the independently defined mandatory structural
  subtyping fragment remains valid. The scoped structural theorems and the
  old pure typing results keep their stated fragment scope.
- Transitivity of two successful *concrete* endpoint resolutions is invalid
  for the complete inequality solver. A `Sub` chain cannot silently erase its
  intermediate source comparisons or their local cast/adapter evidence.
- The carrier-parametric saturation theorem remains conditional on a genuine
  preorder and its exact pure decomposition laws. It does not establish that
  complete concrete compatibility supplies that carrier.

## Minimum missing source bridge

Any complete source-adequacy proof must show how source subsumption and
Function application preserve the endpoint-dependent query semantics. In
particular, it must either retain each intermediate source comparison and
its evidence through generation, or prove that the supported source envelope
restricts such chains to a transitive structural subrelation. The current
candidate rules choose neither bridge. This is the minimum missing premise;
it is not discharged by allowing transitivity only for variable bounds.

No new solver carrier is justified by this counterexample. The immediate proof
gate is to replace the global-preorder completeness interface for the claimed
source envelope with an evidence-preserving endpoint-query correspondence, or
to establish a source restriction that makes the old theorem applicable. No
such restriction is selected here.
