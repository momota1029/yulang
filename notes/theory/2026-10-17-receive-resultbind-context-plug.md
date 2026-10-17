# Receive ResultBind context: apply the existing source inversion

Date: 2026-10-17  
Status: Draft conditional source derivation and exact remaining-premise audit; independent review pending.  
Author: `/root/receive_resultbind_context_plug`, bounded Astra proof assignment.  
Sprint: `receive-resultbind-context-plug-20261017`, contract revision 1, SHA-256 `5ae922e68fa123cd99484a4cc1589c757b1cd418d9b582eb0c056edd43b7061d`.  
Baseline supplied by Luna: `e92374886346d0b561246514b02558f02cad7a48`.  
Authority: research only; no new semantic rule selected or proposed here.

## 1. Result and parent application

The existing [initial-context construction](../progress/2026-10-06-initial-context-source-construction.md)
§§4.1, 4.3–5 and 7 covers the punctured immutable source graph

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
c1 = f(Unit)       c2 = g(Unit)
S_g = g(Unit)      K_src = let g = [distinguished c1] in S_g.
```

`K_src` denotes the source context, not the K component of `xi=(nu,K,D)`.
The displayed bracket is a context notation for the distinguished Call node:
that node retains the two original holes H_f and H_a. It introduces no third
freely fillable semantic hole or independently chosen first-result provider.

Consequently the prior candidate's missing *structural* context-plug step is
already an instance of existing generation and conditional inversion. It does
not need a new `CTX-RESULTBIND-PUNCTURE` semantic rule. An independently checked
open suffix supplies the suffix's local witnesses. It does **not**, on its
own, supply the surrounding Bind's complete image bound, unchanged ambient
residual, independent import/current-world leaves, or original profile and
typed-path interpretations. Section 3 states precisely how the witnesses join.

For this actual fragment no complete open-suffix derivation at the original
A1 has been supplied by the pinned records. Expanding its first Call rule
exposes the missing independent c2 Function elimination: a well-formed
original F2 and `VIncl(A1,F2;xi,e_f2)`, followed by the original whole-argument
and complete-image constraints. The syntax generates these obligations; it
does not prove them. Even assuming that suffix derivation as in the sprint's
question leaves the displayed ambient/Bind obligations to supply. This is
outcome (c), an exact remaining-premise result, not a source counterexample.

Apply this to hypothesis 2 of [FORWARD-FIRST-CALL](2026-10-16-first-call-joint-forward-preservation.md)
§1: its source-owned *graph construction* can use the existing inversion;
its satisfying independent context remains unproved until the listed
witnesses are supplied together. The theorem's environment premise and
anchored native MODEL premise remain separate. Source T, source plan
export/import, full parent theorem and production all remain OPEN.

## 2. Exact constructor expansion for this graph

Fix the original source instance, binder tree, A1/E1 and xi. Do not choose
A1 to be alpha+, F2, the actual first returns, or a more convenient subset.
Register the original source nodes and their I/d/n coordinates once. Keep
local witnesses at their original binding scopes; no existential is moved
outside a rigid binder or solved separately for an alias.

The generation below is an application of initial-context §§3–5, not a new
definition of `Phi_B^H`. That predicate remains the conjunction of **all**
emitted local relations, the unchanged independent source residual, and
independent import leaves from that source. No displayed sublist replaces it.

| Original node/owner | Generated relations or retained operands | Evidence boundary |
| --- | --- | --- |
| Distinguished c1, §5 | Original occurrence, slot, H_f:F_beta, H_a at its whole-carrier interface, original A1/E1, result/rebind path to b_g, ordered suffix | Puncture omits the tested c1 comparison Q and plugged-call preservation. It does not erase the other original residual constraints. Neither hole asserts actual membership or actual execution. |
| Bind, §4.3 | Register g:Value(A1) at b_g; retain the same source result/state/suffix witness and the whole state-threaded Bind image | Registration is hypothetical before Return. The complete Bind effect/image bound is a local semantic obligation, not a consequence of allocating g. |
| Name g, §4.1 | `I_g=I_b_g=Value(A1)`, `d_g=name(r_b_g)`, `n_g=result(d_g)` | An occurrence copies the original root and dependent references. This is not an import of an actually installed g. |
| c2 Unit, §§4.1–4.2 | Ground Unit descriptor, its ordinary literal relation and `result(Unit)` normalization; whole carrier `Delay(result(Unit))` | Ground formation is provided by the selected Unit/Return/Delay construction. Its scope/license and comparison to the actual c2 inlet remain the original obligations. |
| c2 Call, §4.4 | The full relations displayed below, one original F2, original actual-provider schema and same source input/output positions | Source syntax emits the relations. An independently checked open c2 derivation supplies their semantic witnesses; merely recognizing an arrow shape does not. |
| Enclosing source graph, §§3–5 | Every retained other-binding, annotation, capture and outer-node clause, plus the unchanged original residual | Removing c1's tested Q does not remove these clauses or replace an enclosing Lambda's complete bound by its body's result skeleton. |
| Imports/world and profile, §§4.1, 5, 8 | Original `Imp_Delta(rho,C_ext;xi,w_imp)` when present, current C0 incidences, and independent P_beta interpretation | Syntax transports references, not live permission. No-import syntax alone does not certify an arbitrary current world. |

With `a2` the original Unit argument occurrence, the c2 Call emits exactly
the §4.4 obligations specialized at its original root:

```text
WF_Dec(F2;xi)
VIncl(A1,F2;xi,e_f2)
WholeArgCompatible(Result(I_a2),CarrierContract(F2);xi,e_a2)
ReceiveSchema(c2,F2,r_b_g,Delay(n_a2),call_view2;xi)
CIncl(ExecuteCallableImage(n_g,Delay(n_a2),F2,e_f2,e_a2;xi),
      Comp(E2,A2);xi,e_out2).
```

E2/A2 name the existing c2 output coordinates, not new independently solved
outputs. `VIncl` quantifies over the original decorated values at A1; `CIncl`
retains the complete invocation, pending observations and independently
admitted developments. Neither is a check of one returned g or one trace.
`ReceiveSchema` retains original received-carrier/complete-call addresses and
the receipt-before-entry order, with the actual callable's own entry/body/
consumer. Its generation creates no dynamic receipt, acceptance or provider.

The original Bind equations are retained literally:

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S
  = Request(q,C,lambda(response,C'). k(response,C') >>= S).
```

They explain why the open suffix can be registered before either Return or
Request. They do not establish its semantic typing or manufacture a current
state. The hypothetical binder ranges at its original dependent scope;
future response/current-state parameters remain bound there. A proof of the
suffix only at the initial C0 would not be the required open derivation over
its original future obligations. Nothing replays receipt, restores an expired
grant, or substitutes historical C0 for resumed C'.

This fragment uses the finite immutable Hole/Name/Literal/Call/Bind envelope.
The written ctrl annotation is an independent annotation/descriptor input;
it does not introduce an operation invocation, handler, or State source node
into this syntax. Its semantic effect/profile obligations are still retained.
Any surrounding nodes actually included in B must also be generated and
checked; this local calculation does not silently discard them.

## 3. Conditional inversion applied, with its exact seam

Let D_s be an ordinary open source derivation of **this** S_g under the
original hypothetical binder g:Value(A1), using the fixed interpreted rules
of initial-context §7. This means an actual derivation with the local side
witnesses above, not an AST, a list of generated constraints, or a native
success flag. Fix its original source/world/root parameters; its local
witnesses remain dependent functions at their original scopes.

Perform the §7 forward extraction on D_s. Read its Name root, Unit relation,
F2 and its full c2 witnesses into the preallocated coordinates. This satisfies
every emitted suffix conjunct, including all shared operands of those
conjuncts. It yields a partial assignment on the full graph, not a proof of
all of `Phi_B^H`.

Now supply, at those **same** overlapping coordinates:

1. The original two-hole source assumptions and c1 occurrence/result/path
   references, retaining A1/E1 and the static source port correspondences.
2. The original Bind local result/state/suffix relation and semantic bound
   on its complete image, including the original effect incidences. Do not
   add actual c1 output membership to prove that relation. Its source
   interpretation is open under the puncture's hypothetical assumptions.
3. Every remaining enclosing-node clause and the unchanged independent
   source residual, excluding only the pending tested Q as §5 prescribes.
4. Each actual independent import leaf with its **joint** imported roots,
   descriptor membership, original operation instances/endpoints, scope,
   retained K/D, shared continuations, current ownership, receipt/profile/
   path incidences, activation order, and absence of live expired activation.
   For a source-prefix world, use that prefix's existing constructor image;
   for an arbitrary current external world, use its independent world input.
5. The independent original descriptor/profile/path interpretations at the
   source incidences where the preceding relations depend on them.

Items 1–5 are a witness inventory of the original clauses, not a new aggregate
`TypedContext` axiom. In particular item 2's bound and item 4's world validity
remain visible semantic premises. Some coordinates can already occur in D_s;
then the same witnesses must be reused or related by an independently lawful
original action. The argument does not choose a second world/model to make
the remaining clauses true.

Join the extracted suffix fields and these fields without changing any
shared root, source instance, scope, xi, provider/reference, effect operand,
world or witness. The construction is defined only if all overlaps agree at
their full dependent types. Every conjunct of the original `Phi_B^H` now has
its owning witness: suffix conjuncts by forward extraction, the rest by the
enumerated original premises. Thus the joined tuple satisfies `Phi_B^H`.
Conversely a satisfying tuple restricts to the suffix's original local
conjuncts, and §7 reconstruction supplies D_s under the hypothetical binder.
This restriction claims no separate world chosen for the suffix.

This is the exact structural content of the proposed plug step. Initial-context
§7 already supplies the node-wise extraction/reconstruction; the present
argument identifies its nodes and overlap obligations for receive. There is
no extra admission rule to adopt. The conclusion is pointwise for every
original tuple with these witnesses; there is no existential assertion that
such witnesses have been constructed for this receive fragment.

With the additional P_beta and realization premises, §5 PCInit-source may
then construct its original source initial seed. The selected Unit inlet §4
still separately requires the other-value/current-world inputs, original
context/path/role formulas and `E_t <: E_A`, plus the actual Unit-port filling.
`Initial_source` is not complete production admission. Every independently
typed compatible non-source context, Option 2 provider, divergent carrier and
independent response/Resume/FutureUse development remains in the original
approved domain. This local inversion neither proves nor restricts that domain.

## 4. First missing independent evidence for receive

The pinned prior receive note supplies a candidate premise D_s, rather than
constructing it. The ResultBind projection supplies the *later actual*
J_z/Value(A1)/environment extension when its premises hold. That later proof
cannot fill D_s during c1 challenge formation. The challenge-ownership note
supplies field owners and scopes, not their semantic truth.

In the generated suffix, Name's equations and the ground Unit constructor are
available. The first Call-side independent premise in §4.4's order is a
well-formed original F2 at xi; the immediately following essential check is
the full same-value inclusion `VIncl(A1,F2;xi,e_f2)`. There is no supplied
derivation of this pair at the original A1/F2 incidence in the pinned inputs.
The source owner is c2's Name-to-Call elimination and its original Function/
descriptor interpretation. The required follow-on witnesses are e_a2 and
e_out2 above, not a proof that some particular g can be called.

The printed `alpha+ = ([ctrl]Unit) -> [ctrl]Int` does not establish this
inclusion at A1. A1 is the distinct Apply-owned first-result position. Even
an independently established inclusion from alpha into A1 has the wrong
direction to imply that **all** A1 values meet F2. The whole original
incident constraints might establish the required check; this note does not
prove they do, or claim they cannot. Substituting alpha for A1, choosing a
convenient F2 after Return, or reading a function-shaped native row would
discard the exact source obligation rather than solve it.

If D_s is granted as a fully checked derivation, this c2 premise is supplied
by definition of that existing derivation judgment. The next unfinished seam
is the Bind image bound and unchanged ambient residual at its same tuple,
with the independent import/current-world/profile inputs above. The question
"does D_s alone imply Phi_B^H?" therefore cannot be answered by invoking §7
on only D_s: §7's premise is the open derivation of the **whole** graph with
all fixed independent interpretations. No source-qualified counterexample
has been established here; the result identifies the unprovided premises.

## 5. Noncircularity, correspondence and next evidence

The proof reads no actual c1 acceptance, completed receipt, result z, W_z,
F_R,z, installed g or plugged-call preservation. At actual Return the selected
ResultBind rule may install the same full J_z at b_g; while pending, it may
not. c2's actual completed result goes to the enclosing Lambda body-result
destination, not b_g. The conditional source context construction creates
neither actual packet.

Native MODEL remains the original anchored joint premise, including original
alpha/A1/E1, every incident predicate, and lawful maps. It is not produced by
the inversion, the ground Unit proof, retained native constraints or a model
of only c2. No Simple-sub generation/accumulation/propagation/level/extrusion/
intrusion/generalization mechanism changes. No F1/FK1, foreign-kernel or
independent future quantifier is discharged by this local Bind calculation.

The next discriminating task is **RECEIVE-C2-OPEN-CHECK**: at original A1 and
xi, supply the actual open c2 Function formation/checking derivation including
WF_Dec, VIncl, WholeArgCompatible and the complete CIncl image, or isolate its
first unavailable descriptor law. Inputs are the original result position,
Name reference, Unit construction, source Function contract and unchanged
incident constraints. Its falsifier is a missing guard, altered original
coordinate, use of an actual c1 output/receipt, or proof of only one provider's
trace. The source Call/descriptor owner owns this evidence; compiler source
implementation is not granted by this request.

In parallel only if separately leased by Luna, **RECEIVE-AMBIENT-JOIN** can
identify the actual surrounding Bind bound/residual and independently
supplied world/profile witnesses. It must return one same-tuple join, or the
exact unresolved field and owner; it must not package them as unexplained
context validity. These TODOs refine the prior plug-law request: structural
generation is available, satisfaction and independent interpretations remain.

## 6. Checks and frozen scope

All 13 input SHA-256 pins in contract revision 1 and that contract's own hash
were directly recomputed and matched before use. Method: constructor-by-
constructor source audit, application of existing §7 inversion, same-tuple
join audit, and attempt to discharge the emitted c2/Bind/world premises from
the pinned selected rules. These are author checks, not independent review.
No test, build, executable probe, compiler invocation, Git operation, source
edit, external contact or descendant was used. No standalone scratch file
was created. Only this note and its exact assigned handoff were written.

Prior work reused: the conditional initial-context inversion; selected Unit
carrier/inlet; selected actual ResultBind projection; challenge ownership;
same-provider challenge assembly; the unchanged conditional first-Call
theorem. Prior inference rejected: treating absence of a separate named
ResultBind plug rule as absence of the existing structural constructor
inversion, or treating that inversion as a satisfaction theorem for this
instance. No prior theorem or accepted semantic contract is weakened.
