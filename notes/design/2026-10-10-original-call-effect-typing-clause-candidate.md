# Original Call-effect typing clause candidate

Status: Draft; reviewed candidate, not adopted
Scope: Optional original typing for the generated immediate Call-effect position and its Call occurrence
Approved-by: none
Reviewed-by: `compiler_referee` and `spec_auditor` (pre-write review plus post-write §5 domain-repair delta; no remaining blocking, major, or minor findings)
Supersedes: none
Semantic and implementation authority: none

**Current scope after local adoption.** The user separately approved the
[original Call formation definition](2026-10-07-original-call-formation-definition.md)
for actual emitted Gen-Call-0 records. Its reviewed
[O0-selected theorem](../theory/2026-10-07-adopted-call-formation-o0.md)
closes that local static formation port. This Draft instead fixes old semantic
families before interpreting its optional constructors; its coherent sections,
active-primitive pullbacks and finite counterexample remain relevant to that
distinct comparison problem. The following historical statements that O0 is
open or adoption unavailable concern this fixed-family candidate, not the
separately approved local definition. No section/pullback theorem here is
claimed proved by the local adoption, and this Draft is not itself adopted.

## 1. Purpose and boundary

This candidate turns the O0 interface into two explicit typing clauses over
fixed original semantic families. It also states the exact condition under
which these clauses can be interpreted conservatively in an existing original
model. The clauses are not consequences of the current Authority: source
Function-view formation leaves its constructing judgments open, and the
current source-call record supplies only a dependent schema and conditional
port map.

The candidate does not define the original Function interpretation,
occurrence domain, admission, licensing, owner/slot relation, or contribution
domain. It does not establish that the required old-sort witnesses exist.
Production inference and all semantic DAG statuses remain unchanged.

Governing constraints:

- [Inferred Function call views](2026-10-05-inferred-function-call-views.md)
  §§2, 5 fixes source-directed formation, stable source identity, one original
  `xi`, and independence from successful comparison; the exact rules remain
  open.
- [Nested-block Function source addendum](2026-10-06-nested-block-function-source-realization-addendum.md)
  §2 fixes the captured outer `f`, local `x`, inner `f x`, and inert return of
  `step`.
- [Typed computation core](2026-10-02-typed-computation-core-elaboration.md)
  §§6, 9 fixes complete invocation entry and designated consumers, while
  leaving original descriptor typing to its independent interpretation.
- [Source contracts](2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2 requires original typed owner/view inputs and constructor-typing
  lemmas; adding graph metadata is insufficient.
- [Source Call generation](../progress/2026-10-06-source-call-generation-construction.md)
  §§4.2–4.4 supplies the research-only dependent `Gen-Call-0` record and
  conditional port map, not an original typing rule.

## 2. Fixed original families and dependent context

Fix one original interpretation `M`, original binder tree `B`, component `X`,
and whole tuple `xi = (nu,K,D)`. Let `Delta_c` be the actual inner Call context
at `sigma_step`. The captured provider `(d_f,A_f,R_f)` remains anchored at
`sigma_apply`; the local demand `U_c` is not hoisted to that scope.

For the exact retained `Gen-Call-0` record, write its full dependent telescope
as `iota`. Split out signature-position indices `j_sig`, which retain the
original binder tree, component, whole tuple, actual context, captured
provider/root and permitted descriptor dependencies, but exclude `p0` and the
original occurrence-typing witness being introduced. The source record
retains at least:

```text
iota = (B, X, xi, Delta_c;
        d_f, A_f, R_f, c, u_f, u_x, u, beta, p0, p_out(c), ...)
U_c = demand(e_c) at Delta_c
beta = (d_f, R_f)
p0 = (beta, call.effect)
```

All original roots, scopes, providers, occurrences, and dependency indices
remain distinct. In particular, `u_f` is the lexical callee use and `u` is the
generated checking occurrence. No endpoint equality or identifier cast
identifies them.

Assume the independently fixed model has these old indexed families:

```text
FDesc_0(j_sig)                        complete Function descriptors
EffPos_0(U; j_sig)                    original signature effect positions
Occ_0(iota)                           original typed occurrence witnesses
Inc_0(a,e,U,q; iota,j_sig)            original joint typed incidence
```

These names abbreviate existing original interpretations if they are already
defined. They are not definitions as images of this candidate's constructors.
If one of these families or its indexed equality is not defined by the chosen
model, the realization obligation below remains open; the new notation does
not complete it by itself.

## 3. Optional typing clauses

The first clause forms the designated immediate complete-invocation position
from an independently well-formed complete Function descriptor:

```text
Gamma; xi; Delta_c; j_sig |- U : FDesc_0(j_sig)
-------------------------------------------------- OSig-FCall [OPTIONAL]
Gamma; xi; Delta_c; j_sig |- inv(j_sig,U) : EffPos_0(U; j_sig)
```

`inv(j_sig,U)` denotes the existing designated complete-invocation effect
position. Its meaning includes the actual entry and designated consumers. It
does not select a body/native-return position or a latent result position.
The clause uses neither the source occurrence interpretation nor `Q`,
execution, seed truth, or successful `VIncl`.

The second clause types the retained Call occurrence at exactly that
signature-local position:

```text
Gamma; xi; Delta_c; iota |- e : GenCallDemand(iota, U, j_sig)
Gamma; xi; Delta_c; j_sig |- U : FDesc_0(j_sig)
Gamma; xi; Delta_c; j_sig |- q : EffPos_0(U; j_sig)
q == inv(j_sig,U)
e.U == U and e's signature indices are exactly j_sig
e's other indices are exactly the original iota
---------------------------------------------------------------- OC-FCall [OPTIONAL]
Gamma; xi; Delta_c |- ce(e) :
    Sigma a : Occ_0(iota). Inc_0(a, e, U, q; iota, j_sig)
```

The second and third premises are explicit. `GenCallDemand` does not certify
original descriptor formation. The equality is definitional in the proposed
indexed calculus; any non-definitional transport would need an independently
typed transport over the entire telescope. Shape equality, identifier casts,
or separate port witnesses are insufficient.

`ce(e)` chooses a typed witness in the fixed `Occ_0` fiber; it allocates no new
semantic occurrence. Its projections compute as follows:

```text
signature_position(ce(e)) := inv(j_sig,U)
source_position(ce(e))    := e.p0
source_incidence(ce(e))   := (e.beta, e.u, e.c)
origin_and_scope(ce(e))   := e's exact original dependent indices
```

The pre-existing `ElimOrigin` leg to `p_out(c)` remains present. These rules
introduce no runtime `Flow`, receipt, owner, slot, contribution, admission,
license, or effect-row equality.

## 4. Formation and whole-tuple substitution

The clauses above prove **syntactic formation in the proposed calculus only**,
under their displayed `FDesc_0`, `GenCallDemand`, and old-position judgments.
The `q == inv(j_sig,U)` premise excludes pairing the source `call.effect` port
with a latent result port.

For substitution, assume a legal, typed action on the entire old telescope
and all old indexed families. This base action is an independent premise. It
must preserve the original binder tree, whole `xi`, scopes, providers, source
tags, dependent indices, and indexed equality, and satisfy identity,
composition, and typing-conversion laws. An action on the new syntax alone is
not sufficient.

Extend that action by:

```text
theta(inv(j_sig,U)) = inv(theta(j_sig),theta(U))
theta(ce(e))  = ce(theta(e))
```

Because `theta` acts on the whole telescope, the premises for each new
constructor transport together. Induction on the two new constructors proves
that the extension preserves typing and satisfies identity and composition.
The projection equations commute with this action by their definitions.
This proof does not construct the base action for the original semantic
families, nor prove that its interpretation preserves the selected original
positions or incidences.

## 5. Exact condition for conservative interpretation

For each context `Delta`, let:

- `S_Delta` be every signature input `(j_sig,U)` for which the independently
  fixed old model already derives `U : FDesc_0(j_sig)`, within the candidate's
  stated rule scope. This is the complete domain of `OSig-FCall`; it is not
  merely the subset of demands that happened to arise from source calls.
- `P_Delta(j_sig,U)` be the old designated immediate complete-invocation
  positions for that exact typed descriptor input.
- `E_Delta` be the legal existing `Gen-Call-0` records at independently
  selected base assignments. The base predicate selecting them contains no
  O0 conclusion, successful `Q`, or newly invented admission/execution
  premise.
- `C_Delta` be exactly the complete `OC-FCall` premise instances
  `(e,j_sig,U,q)` with `e : GenCallDemand(iota,U,j_sig)`, `e`'s signature
  indices equal to `j_sig`, `e.U=U`, the displayed old descriptor typing, and
  `q=inv(j_sig,U)` from `OSig-FCall`.
- `O_Delta(e,j_sig,U,q)` be the old occurrence/incidence witnesses at exactly
  `e`'s descriptor, `beta`, `u`, `p0`, `c`, scope, dependencies, and
  `ElimOrigin`, whose signature projection is `q`.

The optional clauses have an interpretation in the existing families exactly
when there are total sections

```text
s_Delta : forall (j_sig,U) in S_Delta. P_Delta(j_sig,U)
t_Delta : forall (e,j_sig,U,q) in C_Delta. O_Delta(e,j_sig,U,q)
```

and both commute with every legal whole-tuple substitution `theta`:

```text
theta(s_Delta(j_sig,U)) = s_Delta'(theta(j_sig),theta(U))
theta(t_Delta(e,j_sig,U,q)) =
  t_Delta'(theta(e),theta(j_sig),theta(U),theta(q))
```

Equality is the existing indexed equality. Proof irrelevance, quotienting, or
independent freshening of the coordinates is not implicit.

**Necessity.** An interpretation of `OSig-FCall` selects `s` for every
independently typed signature input in its full rule domain. The same term
`inv(j_sig,U)` has one interpretation for that exact indexed input; typing
derivation identity is not an extra index. An interpretation of `OC-FCall`
selects `t` for every complete premise instance. Old typing places the
selected values in `P` and `O`, the projection equations fix their exact
indices, and substitution coherence supplies the displayed equations.

**Sufficiency.** Interpret `inv(j_sig,U)` by `s(j_sig,U)` and `ce(e)` by the
section for its exact complete premise instance. Old family membership
supplies typing, designation, and joint incidence. The section equations
establish the projections; their coherence establishes the new substitution
equations. This yields an interpretation extension, not an admissible
derivation in an independently fixed formal proof system. A derivation still
requires old introduction rules producing `s` and `t`.

For this extension to preserve all old judgments and observations, require
the following in addition:

1. The sections are total over every old legal solution/strategy in the
   selected source envelope, including independently admitted contexts and
   retained witnesses.
2. For every active old primitive `K_0` used by membership, admission,
   incidence typing, or observation, its extended interpretation satisfies
   `K_plus(z_plus) <=> K_0(erase(z_plus))` on every legal tuple. Successful
   `Q` cases alone are not enough.
3. Erasure preserves original providers, scopes, predicate identities,
   dependent incidence, and every original evidence alternative. No original
   witness is replaced by the image of the new constructor.
4. Relation construction, alternatives, binder positions, admission history,
   final observation projection, and the approved Option 2 production extras
   remain unchanged.

Under these assumptions, induction on primitive, conjunction, union,
constructor-image, and scoped-binder derivations preserves old membership and
admission. Induction over finite recursive derivations covers positive
recursion. The total coherent sections provide corresponding witnesses in
both directions. Therefore the old observation projection is unchanged.
This is a conditional conservativity theorem; its old-family section and
pullback premises are not currently proved.

## 6. Why free evidence extension is insufficient

One demand `e`, one original tuple `z`, one designated position `q`, one
possible observation `o`, and one handle `a` suffice. Keep descriptor
membership and all other active predicates true. Let the active root contain
the primitive:

```text
R(z) iff exists a. Inc_0(a, e, U, q)
```

With an empty old incidence fiber, `R(z)` is false and the projected
observation set is empty. Adding a free occurrence/incidence witness makes
`R_plus(z)` true and the observation set `{o}`. Thus free evidence creation
does not imply preservation of an active kernel's behavior.

This finite model pair falsifies only the generic implication “free evidence
extension is conservative.” It is not a pair of complete Authority-consistent
Yulang interpretations for an admitted source and establishes no user-choice
blocker.

## 7. Status and remaining theorem

This is an unadopted semantic candidate. Current Authority does not establish
its old-family sections or primitive pullback, so O0 remains open. No
Authority-consistent model pair with different observable/principal outcomes
has been demonstrated. The user-decision threshold is unmet.

Before adoption or implementation, the exact remaining proof is to realize
both constructors in the selected original families, provide coherent old
sections for every legal assignment, and prove pullback for every active
primitive and evidence alternative. If this interpretation cannot exist,
the optional clauses would change the original occurrence semantics and need
a separate behavioral assessment.

No production inference path, user-visible behavior, DAG status, or theorem
claim is changed by this Draft.
