# Original literal Result owner extension — bounded candidate

Date: 2026-10-09
Status: Draft; non-authoritative, no implementation authority
Baseline: `eb6032bb0136b3f5a07c2574a202dd850fac4136`
Scope: literal argument occurrence in the bounded `Apply(Name(f), IntegerLiteral(1))` owner seam
Proposal source: reviewed conditional R-flat candidate §3 and approved `Application_N` q1/d1
Claim class: candidate source-registration/typed-realization interface, for independent review

## 1. Decision boundary

This draft makes one candidate source-owner boundary concrete: an authentic
original literal Data derivation and Result-port registration at the actual
literal child of the bounded Application. It proposes a target for the
`realizeResult_N` proof bridge. It does not assert that the candidate is already
an original source rule or that any current compiler operation produces it.

Approved q1/d1 selects `Application_N` as the successor owner for its stated
Name/Int literal seam. It does not equate N-owned ports with original ports,
adopt the `PortReg+` proposal, or authorize implementation. The original
Call-input consumer still requires its own Data derivation and original result
port. The previously reviewed owner candidate explicitly leaves its
`ResultLiteral` as `PortReg+`, not `PortReg_orig`.

The source contract remains open to user decision after independent review.
No source acceptance, semantic inhabitance, solver result, or production
change follows from this proposal.

## 2. Exact source and semantic inputs

Fix one actual source occurrence `a`, its integer value/spelling `1`, its
actual parent Call occurrence `c`, the literal-child incidence
`ArgumentChild(c,a)`, the original lexical telescope `T_c` and scope
`Delta_c`, and one dependent tuple `xi=(nu,K,D)`. These are not reconstructed
from printed type endpoints or allocated independently for each port.

The independent primitive input `H_prim` is the complete contract already
required by `Application_N` Literal-N: `Prim_a`, `Value(Int)`, the inert
literal descriptor, ordered dependent inputs, every witness/alternative,
licenses, world/provider/future indices, and lawful action. It is neither
derived from the integer spelling nor from a successful F5 query. A semantic
Return member still requires an actual primitive member witness.

The independent source/kernel input `H_return` is the existing typed-core
literal normalization and pure Return interpretation at these original
indices, with its complete dependent domain and lawful action. It must accept
the output license below. It provides no primitive inhabitance, argument
check, Call admission, or execution receipt.

## 3. Candidate owner constructor

The candidate constructor is source-directed and returns both the original
Data derivation needed by Code-Result and its separately tagged original
Result-port certificate:

```text
H_prim at the actual literal occurrence a
ArgumentChild(c,a), actual original T_c / Delta_c, actual xi
H_return at those same dependent indices
-------------------------------------------------- Original-ResultLiteral
q_a^orig : Data_orig(T_c, literal(a,1), Value(Int))
o_a^orig : PortReg_orig(parent=a, role=ResultOfLiteral,
                       interface=Comp(empty,Int), scope=Delta_c,
                       telescope=xi, source-child=ArgumentChild(c,a))
q_res^orig = Code-Result(q_a^orig, o_a^orig)
  : Code_orig(T_c, result(literal(a,1)), Comp(empty,Int)).
```

The constructor stores its exact primitive, source occurrence, parent/child
edge, original telescope, port role, kernel, all witness and future fields,
and derivation alternatives. Its eliminator returns those same fields.
Different literal occurrences, parents, roles or scopes create distinct
licenses even when every erased endpoint is `Return(1)` or
`Comp(empty,Int)`. It creates no Name binding for the literal.

`Original-ResultLiteral` is a proposed new original static formation case.
If selected, the old Name-family image remains unchanged through its existing
Keep path; the literal branch is a tagged extension, not an endpoint-based
merge. This rule is not emitted-Application membership and does not complete
the full R-flat schema.

## 4. N-to-original realization target

Given the selected N-side literal/result certificate and the output above,
the proof target is a dependent map

```text
realizeResult_N(q_result^N, q_a^orig, o_a^orig)
  : (q_result^orig, eta_a, commute_Return, commute_action)
```

`eta_a` preserves the actual primitive identity, integer payload, source
occurrence, parent/child incidence, original scope/telescope, every witness
alternative, current world/configuration and provider/future coordinates.
`commute_Return` relates the two complete Return interpretations at these
mapped records. `commute_action` proves the map commutes with identity and
every allowed whole dependent action. The map retains exact `J_a^N` and
`J_a^orig` records and their incidences; it does not assert either equals the
interface `R_a=Comp(empty,Int)` or identify N and original port keys.

The bridge must follow from the selected whole primitive and Return contracts
plus the authentic owner derivation. If those inputs do not determine a typed
map, the residual is an explicit kernel-realization proof obligation; code
erasure or displayed-type equality cannot discharge it. No satisfying
`WholeArgCompatible` witness is created here.

## 5. Consequences and non-goals

If the constructor and bridge are selected and proved, existing Code-Result
can form the literal's original typed Return image. The following remain
separate: Call-owned ArgReify/Delay and whole-carrier typing; original
`WholeArgCompatible` and other Check origins; complete original Application
result/suffix origins; emitted membership and complete inventory (`E-flat` /
`H-inventory`); SeedExposure and CallInitial/I0; `mu_adm`; `Valid_V`; Direct;
general source inference, principality, production correspondence and F5
cutover.

Explicitly rejected derivations: inventing `Name(literal)`, substituting
`p_1` from `my one=1`, equating `J_a` with `R_a`, choosing an original port by
the endpoint, inferring primitive membership from source spelling, treating a
static port as a successful check, or claiming a completed original Call.

## 6. Review and approval gate

Review this exact draft with a `compiler_referee` for constructor ownership,
typed incidence, full dependent witnesses/action and naturality, and a
`spec_auditor` for q1/d1 and existing Call-input conformance. The reviews must
identify whether `H_return` is already sufficient for `commute_Return` or
whether a genuine semantic bridge remains. Any added primitive/Return clause,
changed old Name behavior, missing input field, endpoint quotient, or claim of
emitted membership is a blocking finding.

Only after those reviews should the user decide whether to select this
bounded original registration case. Approval would authorize this source
formation/bridge gate only; it would not authorize E-flat, compiler
implementation, or F5 cutover. No tests, builds, probes, or production edits
are appropriate for this Draft.
