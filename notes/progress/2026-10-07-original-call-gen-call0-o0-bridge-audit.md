# Original Call O0: Gen-Call-0 bridge audit

Date: 2026-10-07
Baseline: `5a156fc7bccd4438d51b99c25bf9e4fb0b91c992`
Status: bounded O0 source-constructor audit; independently reviewed after repair
Claim class: source-structure bridge localization
Semantic and implementation authority: none

## Question and result

Does the reviewed `Gen-Call-0` source constructor already supply round 4's O0
original typed-output/source-root correspondence, or does O0 remain wholly
unconstructed?

It supplies a **source address/schema precursor**, but not a complete
conditional O0 derivation. For the exact approved
`my apply f = { my step x = f x; step }` route, `Gen-Call-0` constructs a
shared root `R_f`, dependent complete Function variable `F_c`,
`beta=(d_f,R_f)`, initial call-effect address `p_0`, complete-invocation
address `p_out(c)`, and `ElimOrigin`. The reviewed source-call construction
also emits the decorated relation containing `VIncl(A_f,F_c;xi,e_value)` and
`WF_Dec(F_c;xi)`. These records fix the source-side root/address/schema and
the constraint's Function variable.

The unconditional original-sort O0 judgment is **not closed** by the static
schema. Round 4 requires
`TypedOutputCorrespondence(U,outEff(U),p0; scope,xi)` in original sorts. The
source-call constructor names `F_c` in its generated decorated upper
constraint, but the reviewed rule does not separately construct round 4's
original upper-use witness `U` or state an original-sort interpretation of
that witness. The earlier bridge sequent treated “`U` is this Call's emitted
upper use and is identified with `F_c`” as a premise; it is not an output
proved by Gen-Call-0. Even granting a well-formed decorated realization of
`F_c`, its conditional observation-port interpretation does not establish
the original typed-path judgment.

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

The Call source constraint contains `VIncl(A_f,F_c;xi,e_value)` and emits
`WF_Dec(F_c;xi)`. The source-call construction states that when `F_c` has a
well-formed realization, its immediate `call.effect` position has the
required observation-port sort and `ElimOrigin` maps it to the complete
invocation output occurrence. This is a source-directed dependent schema,
not a fact inferred from a solved type shape. It remains available when the
constraints later have no solution.

The exact source output is:

```text
Gen-Call-0 at (C,d_f,c,sigma,xi)
-----------------------------------------------------------------------
R_f,F_c,beta,p_0,p_out(c),ElimOrigin
plus a decorated Call constraint containing VIncl(A_f,F_c;xi,e_value)
```

Under a well-formed decorated realization, the reviewed construction gives a
conditional decorated observation-port correspondence. This remains distinct
from original-sort O0. The precise missing interface has two linked parts:
introduce the original upper-use witness `U` for this exact Call and identify
it with the generated Function demand; then interpret the immediate
`call.effect` map as an original typed-path derivation at the same source root,
scope, and `xi`. Typed-core §§3/6 do not fill this gap: translation consumes
typed-path premises and source Call synthesis retains them as obligations.
Neither part follows from `Own_orig`, `Slots_orig`, a successful comparison,
or endpoint/type-shape equality.

A bounded selector-swap discriminator explains why shape reconstruction is
insufficient. For a candidate `F_c = Fun(Value(B), Comp(E, Comp(E,B)))`, the
immediate `call.effect` and latent `result.latent.effect` have the same row
sort but are distinct positions. Repointing a later witness decoder from the
immediate to the latent position preserves the types and generated
Gen-Call-0 records but violates the required correspondence. This is a
representation discriminator, not an admitted-source counterexample; an
original Call rule that directly returns the correct immediate-port witness
would discharge O0, but no such closed derivation was found in the inspected
rules.

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

The next proof cut is narrow: expose an exact original upper-use witness for
the generated Call demand and prove its immediate output-map interpretation
in the original typed-path judgment, retaining `c`, `R_f`, scope and `xi`.
The current shadow HIR/core/solver records preserve the lexical Call, operands
and unresolved structural rows but do not make that semantic witness. Then
address O1 via complete source-profile/owner introduction; do not restart
generation of the already reviewed address schema. Any new semantic rule
still needs the normal review and approval before implementation.

Compiler-referee and spec-auditor delta reviews found no remaining issue in
the corrected source-identity and original-sort claims. No code, test
contract, design authority or DAG status changed. No Oracle behavior was used
or adopted. No tests, builds, runtime probes, or performance measurements were
run.
