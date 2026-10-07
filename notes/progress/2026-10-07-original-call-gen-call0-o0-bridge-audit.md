# Original Call O0: Gen-Call-0 bridge audit

Date: 2026-10-07
Baseline: `5a156fc7bccd4438d51b99c25bf9e4fb0b91c992`
Status: bounded conditional source-constructor audit; independently reviewed
Claim class: source-structure bridge localization
Semantic and implementation authority: none

## Question and result

Does the reviewed `Gen-Call-0` source constructor already supply round 4's O0
original typed-output/source-root correspondence, or does O0 remain wholly
unconstructed?

It supplies a **conditional precursor**, so O0 is not wholly absent at the
source-construction layer. For the exact approved
`my apply f = { my step x = f x; step }` route, `Gen-Call-0` constructs a
shared root `R_f`, dependent complete Function variable `F_c`,
`beta=(d_f,R_f)`, initial call-effect address `p_0`, complete-invocation
address `p_out(c)`, and `ElimOrigin`. This already supplies the source-side
root, address, and elimination schema. The reviewed source-call construction
also records this Call's upper use with `F_c` and emits `WF_Dec(F_c;xi)`.

The unconditional original-sort O0 judgment is **not closed** by the static
schema alone. The reviewed construction makes the typed observation-port
interpretation conditional on a well-formed realization of `F_c`; round 4
requires `TypedOutputCorrespondence(U,outEff(U),p0; scope,xi)` in original
sorts. The remaining bridge must provide that realization and identify it
with the exact `U` from this source Call without assuming ownership or using
the success of comparison `Q`.

This result does not derive complete `Slots_orig(beta)`, `Own_orig`, an
original contribution, or a joint original association. In particular,
`InitialSeedSlots(beta)={p_0}` remains only the initial contribution of
`Gen-Call-0`; it does not prove that the complete slot inventory is a
singleton. O1 and C1/J0 remain separate.

## Governing boundary and inputs

- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §2 requires one source-derived shared contract and typed paths/ownership,
  independent of `Q`, while leaving exact construction rules open.
- [Nested-block source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3 fixes this exact sequential binding, inert return of `step`, outer
  `f` capture, and local `x` binding.
- [Source-call generation construction](2026-10-06-source-call-generation-construction.md)
  §§3–4.4,7 is an independently compiler-referee/spec-auditor-reviewed
  non-authoritative construction. It derives the dependent source schema and
  the exact constructor limits below.
- [Round-4 fiber construction](2026-10-09-original-call-fiber-construction-round4.md)
  §3 separates O0 from O1, C0, C1 and J0; O0's premise is an original typed
  output map plus source root/position formation, not a slot count.
- [Reviewed source-introduction interface](../design/2026-10-07-original-call-source-introduction-contract.md)
  §§3–4 keeps these ports separate and all proof/cutover gates open.

All coordinates below use the same original source component, binder tree,
scope and `xi=(nu,K,D)`. `R_f` is the shared contract root generated from the
resolved captured formal; `F_c` is the complete Function constraint variable
at that root.

## Constructor output and conditional correspondence

For the fixed resolved Call, `Gen-Call-0` produces:

```text
R_f                         shared inferred-contract root
F_c                         dependent complete Function variable at R_f
beta = (d_f,R_f)            stable source-contract identity
p_0 = (beta, call.effect)   initial complete-invocation effect address
p_out(c)                    complete-invocation effect address of c
ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c))
```

The Call source constraint also records the upper use with `F_c` and emits
`WF_Dec(F_c;xi)`. The source-call construction states that when `F_c` has a
well-formed realization, its immediate `call.effect` position has the
required observation-port sort and `ElimOrigin` maps it to the complete
invocation output occurrence. This is a source-directed dependent schema,
not a fact inferred from a solved type shape. It remains available when the
constraints later have no solution.

The exact conditional route established by that construction is:

```text
Gen-Call-0 at (C,d_f,c,sigma,xi)
U is the upper use emitted for this Call and is identified with F_c
F_c has a well-formed realization in the reviewed decorated-call relation
ElimOrigin maps F_c.call.effect to p_out(c) in that relation
-----------------------------------------------------------------------
beta and the decorated observation-port correspondence to p_0
```

This is a conditional constructor correspondence, not the original-sort O0
judgment. The source-call note makes the observation-port interpretation
conditional on a well-formed realization of `F_c`; it does not establish that
the decorated relation realizes the original typed-path judgment. O0 still
requires a typed-elaboration bridge that identifies this exact `U` and
interprets the generated map at the original sorts, with the same source root,
scope, and `xi`. Neither this missing bridge nor realization follows from
`Own_orig`, `Slots_orig`, a successful comparison, or a numeric identity.

## Non-conclusions and next cut

The following shortcuts are invalid:

- treating a source address or `ElimOrigin` alone as an inhabited original
  typed-path witness;
- treating `WF_Dec` text or a generated but unrealized `F_c` as a solved
  interpretation;
- choosing `s=p_0` or deriving `s in Slots_orig(beta)` from the initial seed;
- deriving `Own_orig` from source capture, endpoint equality, or the typed
  output map;
- adding runtime receipt/receiver activation to this static O0 bridge;
- restricting original witnesses, production Option 2 extras, or `xi` to
  make the bridge fit.

The next proof cut is narrow: formulate and prove the source typed-elaboration
rule that realizes this generated Call upper use and its immediate output map
in the original typed-path judgment, retaining the exact `R_f`, scope and
`xi`. Then address O1 via complete source-profile/owner introduction; do not
restart generation of the already reviewed address schema. The rule is not
yet selected by an Authoritative design, and any new semantic meaning needs
the normal review and approval before implementation.

Independent compiler-referee and spec-auditor reviews found no remaining
issues after narrowing the conditional conclusion to the decorated
observation-port correspondence. No code, test contract, design authority or DAG status changed. No Oracle
behavior was used or adopted. No tests, builds, runtime probes, or performance
measurements were run.
