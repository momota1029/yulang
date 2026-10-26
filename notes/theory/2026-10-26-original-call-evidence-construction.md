# Original Call evidence: consumer-complete candidate and construction

Date: 2026-10-26. Author: `/root/original_call_construction`.
Status: **unadopted declaration candidate and paper construction; independently
accepted in that scope** ([review](../../tasks/agent-loop/inbox/20261026-inference-original-call-evidence-review.md)).
Supplied baseline: `2eced4d`, branch `yulang3`.
Scope: the original immutable `Call(Name h,Name x)` at an actual fresh
ValueBind, its original full decorated constraint, and the consumers listed
below. No language rule, compiler code, original predicate, or parent gate is
changed. This does not define `TypedCallCert_Dec` by abbreviation.

## 1. Result

The consumer audit makes the missing declaration substantially more precise.
An adequate candidate must contain **three different layers**: the staged
source/receiver evidence, the selected native profile and ownership evidence,
and the interpretation of those objects by the original active consumers.
The first two can be assembled for the selected Name call from genuine child
packets, GC1–GC4, PF1/PF2, and the accepted NPR/VB-NP theorem, retaining the
original independent boundary/annotation and complete-arm evidence wherever
it is required. The last layer
is identity only when the target consumer actually uses the selected
constructor interpretation. A separately fixed profile, contribution,
incidence, or coverage interpretation requires its actual typed map and the
back law wherever exactness is claimed.

Sections 4–6 give an explicit dependent declaration candidate and an
introduction calculation. Every field is attached to a named original
consumer. No `remainingFields`, arbitrary whole-Call typing axiom, or
`LocalLaws` argument is inserted. Section 7 gives a concrete discriminator
for the interpretation choice. The candidate is exhaustive **as the proposed
declaration**, not a claim that the undeclared historical predicate is equal
to it. That equality, and the actual host interpretation at each field, are
the exact decisions left for its owning declaration/review.

There is also a real, smaller reconstruction fact that does not wait for
that decision: a solution of the original full `G_call` supplies its original
certificate. Section 8 gives the witness-preserving local Call derivation
from that solution and genuine reconstructed children. It does not attempt
to reconstruct the supplied certificate from scalar success.

The unchanged parent remains

```text
forall s xi d a,
  supported(s) -> generates(s,xi,d) -> solves(d,a) ->
  exists e, sourceJudgment(s,xi,e) and sameScoped(s,xi,e,a).
```

Nothing below instantiates that parent for all original source constructors.

## 2. What the actual consumers demand

### 2.1 Original decorated Call and complete operation

[Original generation §5](../progress/2026-10-06-source-call-generation-construction.md#5-genuine-semantic-call-constraint-generation)
places `TypedCallCert_Dec(c,F_c,e;xi)` inside the **same** scoped existential
as `WF_Dec`, same-value `VIncl`, `WholeArgCompatible`, complete source-image
`CIncl`, `Role_0`, and the canonical Gen-Call-0 records. The certificate is
described as retaining supplied receipt, profile, operation, observation,
and correspondence premises. It is not described as a record consisting
only of those five words.

The [typed-core input](../design/2026-10-02-typed-computation-core-elaboration.md#2-declarative-input-without-executable-schedules)
already has source constructors, actual parameter/entry and result roles,
typed introduction/elimination paths, `Flow`/receipt evidence, handler
declarations, and one `nu,K,D`. Its §4 realization consumes these to preserve
all finite prefixes and admitted future/raw-resumption histories. Its §7
same-value checking retains that evidence and changes no entry/consumer.
Its §8 certificate comparison has four separate consumers:

| Consumer | Fields it actually reads |
| --- | --- |
| Domain preservation | Complete independently admitted arguments, responses, future calls/forces, stored/shared values, current compatible stores, and their joint dependencies. |
| Routing preservation | Original profile presence and admission interpretation, source typed paths, receiver/handler identities, `Flow`, `Receive`, `Observe`, current `Path/Inc_C/Protected/Grant/Visible`, and ordered handler selection. |
| Guarantee preservation | Every original designated observation, ordinary descriptor and hard envelope, actual result provider, and its dependent future interface, at the same witness. |
| Structural preservation | Actual source roles, executable entry/body/consumer, native delimiters, scoped identities and complete original correspondence. |

In particular, the routing consumer applies universally to relevant request
points. An outward effect bound cannot replace it. A changed admission row
must have equal membership at **all** request points in that fixed-domain
comparison; an opaque admission predicate is retained identically. None of
this is a conclusion of ordinary value-type preservation.

The selected [complete Call definition §§2–5](../design/2026-10-07-complete-call-contribution-definition.md)
has a second consumer family. `C-Call` retains the authentic complete
operation witness and every independent alternative; `J-Owned` reads four
accounting conditions, not membership alone: original whole witness,
commuting source/root diagram, all ordered region placements, and correct
own-upper versus inherited attribution. Lexical `u_f` and checking `u` have
separate incidences. The selected [IF definition](../design/2026-10-08-call-source-interface-definition.md)
constructs the entire frame but explicitly preserves primitive typing,
domain, provider/future, and lawful-action inputs.

Authority matters here. The typed-core and typed-boundary documents remain
Draft outside their selected premises; native-signature §1 explicitly does
not adopt the whole typed-core package. Their explicit consumer equations
are useful for specifying and testing a candidate evidence presentation.
This note does not promote those equations to an exhaustive original
certificate or infer boundary realization from native profile formation.
Any independently fixed boundary interpretation remains an F10 obligation.

### 2.2 Full audit of the existing typed-core preservation/progress interface

The Lean object called `TypedCall.CallTerm` is a separate represented
fragment, not the original decorated judgment. Its exact eleven fields in
[CoreSyntax.lean](lean/YulangClosure/CoreSyntax.lean) are:

```text
function          : Function
argument          : Carrier
inputType         : Original.Ty
resultType        : Original.Ty
functionTyped     : FunctionTyped function inputType resultType
argumentIsThunk   : argument.carrierType = thunk inputType
callView          : CallView
sourceReceiptMatches : function.sourceReceipt = callView.sourceReceipt
wrapPlanMatches   : function.wrapAdapters =
                    map (argumentAdapter,resultAdapter) callView.interfaces
activeOwners      : List Nat
receiverFresh     : callView.receiverOwner not in activeOwners
```

The dependent subrecords are material. `Carrier` includes its actual value,
type, `ValueTyped` derivation, occurrences and receipt slots. Each `Adapter`
contains its actual code, typed body, path correspondences and captured
views. `FunctionTyped.lambdaValue` requires the body under a value binding;
`lambdaComputation` requires the body under a thunk binding. Both require
the exact consumer input/output equations. `wrap` retains the typed inner
function and both adapter endpoint equations. `CallView` contains the
receiver, source receipt, carrier occurrences, interface plans, adapter
paths and captured views. None of these subrecords supplies the original
foreign profile interpretation.

`CallStateTyped` has an active-head derivation, a typed Call zipper, and an
independently typed **literally retained** Control suffix. Its head cases are
`call`, `enter`, `received`, `active`, `originalState`, `returned`,
`requesting`, `requested`, and `failed`. Enter/received consume function,
whole-thunk and pending-adapter typing. Requests consume payload and saved
continuation typing. `call_state_typed_step_preservation` and
`call_state_typed_prefix_preservation` preserve these fields and literal
suffix/result identity. Their stated types quantify over arbitrary supplied
world type and metadata; they do not assert world/profile validity.

The complete generic safety interface in
[Contracts.lean](lean/YulangClosure/Contracts.lean) is also explicit. Its
fields cannot be silently supplied by the Call prefix theorem:

| `LocalLaws` field | Exact obligation; relation to this packet |
| --- | --- |
| `Result`, `result`, `typing` | A fixed result index and the original syntax-directed typing family. No concrete original decorated instance is defined here. |
| `initial` | The actual machine's initial configurations. A Call formation graph is not this set. |
| `initial_typing` | Every actual initial configuration has that original typing. This needs source/core initialization. |
| `initial_seed` | Each initial configuration has one analysis seed representing it. This is source/analysis correspondence. |
| `internal_preservation` | Every internal successor preserves that typing. Existing Call preservation covers its represented relation only. |
| `resume_formation` | For the same saved object, each independently admitted response at the supplied current world and each actual resume successor is typed. Original R/E retains the semantic inputs; it is not a native implementation proof. |
| `internal_simulation` | Each internal successor has a matching analysis edge and represented target from the same current cell. IF field maps do not establish this. |
| `resume_simulation` | The corresponding statement for every admitted raw resume/current-world/response successor. |
| `observation` | Every actually exposed output at a typed represented state is an analysis observation. |
| `no_bad` | The original typing excludes the actual machine's bad predicate. |
| `progress` | Every typed state is returned, requested, failed, or has an internal successor. This is not a finite-prefix preservation conclusion. |

These are all thirteen fields, grouping the first three only to display
their shared role. The generic `native_success_elaborates` theorem still
takes original NativeCorrespondence, InferenceSoundness and Elaboration;
connection of its core judgment to `initial` is explicitly additional.

The distinction is witnessed, not merely conjectural:
[CallProgressObstruction.lean](lean/YulangClosure/CallProgressObstruction.lean)
constructs a `CallStateTyped` state after a five-step prefix whose active
head is `force(view(delay(ret unit), occurrence))` and has no successor in
that represented Call relation. This is a formal-fragment obstruction; it
does **not** establish source/frontend reachability or a Yulang counterexample.
It rules out filling generic progress merely by projecting `CallTerm` and
its existing preservation theorem. No stronger progress field is added to
the original certificate by this paper.

## 3. Fixed indices and legitimate construction inputs

Fix the actual immutable occurrence

```text
q_h = Call(Name h, Name x)
j = (B,X,xi,Delta_e; original callee/carrier/receiver/result/future incidence)
xi = (nu,K,D)
```

Fix its original binder tree, registrations, Resolve/capture occurrences,
source reify/Call origins, the authentic complete operation declaration `Q`,
and the complete list/family of its original clauses at their original
scopes. An unknown clause signature is not an empty signature. The operation
is the original callee Bind followed by actual-provider `ExecuteCallable`,
plus its actually declared independent alternatives. It is not replaced by
the draft Name/Integer operation in the older compositional paper.

Use exactly these independent inputs:

1. The complete, independently formed `H*` and actual hereditary immutable
   child `b_h : ValueMem_H*(v_h,r_h,e0)`.
2. An independently compatible actual extension `e0 -> e1`, a genuine typed
   `Return(v_a,r_a,C1,w1)` with `JointWF`, `ValueMem_A` and the original
   result/root/provider/world incidences, and its actual fresh rebind
   `d_x@kappa`. This cannot be obtained by assuming an unproved recursive f.
3. The actual source constructor/registration/reify rules and independently
   typed punctured contexts, other values, whole-carrier admissions,
   primitive contracts, annotation interpretation when present, and lawful
   leaf actions that the original judgments require.
4. For every actual independent clause, its complete original telescope,
   original guards/licenses, local typing and input/domain/provider/future
   actions. These are declaration-local inputs; none can require the final
   `TypedCallCert_Dec(q_h)` or a missing global source theorem.

The current selected inlet is the whole `Comp(empty,A)` and `F_h=H*`.
The Name-produced carrier is its actual diagonal section. For other admitted
whole-carrier fillings the inlet retains **their own** admission evidence;
the domain is not restricted to Name returns. All genuine `Act(v_h,U,r_h)`
decompositions are checked. No convenient U is chosen existentially.

An event is `(eta0,history)` with the history's live `C_e,w_e`. The initial
assignment and source witnesses remain fixed at their original scopes; live
configurations can change with compatible histories. Quantification is

```text
for every original j and lawful assignment at its original binders,
  for every independently compatible current event/history,
    for every retained actual-provider decomposition,
      for every independently admitted complete checked challenge d,
        for every finite zero/admin/pending/return development delta,
          and every independently admitted Response/Resume/FutureUse extension.
```

No existential moves outside a binder it depends on. All clauses at one
event use the same `xi`, context, provider, operation witness and current
tuple. Independent arms keep their own original witnesses and dependent
output providers; they are not paired with a separately selected source
world. Positive recursive references descend only through finite original
derivations; universal future obligations stay inside the original leaves.

## 4. Explicit candidate declaration

This section is a **reviewable unadopted record**, written in paper dependent
type notation. The primitive predicates below are the named original
judgments, not fresh predicates asserting whole-Call success. `M` denotes the
one original semantic interpretation fixed for the target theorem. It is not
a quantifier over arbitrary newly chosen languages. Any foreign components
already quantified in M retain those original quantifiers.

The parameter record `Parameters` contains the exact `j,q_h,Q,F_h,D_h`, the
original result descriptor, and `e_value/e_arg/e_result` from `G_call`.
It contains the solved WF/inclusion components when used by reconstruction;
when used by introduction, §5 constructs those components from the children.
The candidate has the following **exhaustive top-level fields**, in order:

```text
CallEvidenceCandidate_M(Parameters) :=
  (formation, frame, primitives, sourceProtocol, independentClauses,
   nativePackets, packetAction, routing, accounting, interpretation)
```

Their dependent types are specified below; there is no additional opaque
certificate field.

### F1. `formation`

The actual resolved Call formation, original callee/argument registrations,
whole reify origin, canonical Gen-Call-0 records and selected `Role_0`; the
authentic operation-reference/unfolding `SpecCall(Q)`; actual O0 output edge;
and, where the source route has the selected upper exposure, O1 constructed
by `OShared-Register`, `OSlot-SharedInvoke`, `OOwn-Upper` and
`OOwn-Upper-Checking` from that same registration, route, O0/source tuple
and actual `SeedExposure`. The last two rules introduce **separate**
`Own(...,u_f,...)` and checking-u facets and retain the actual exposure
link; neither takes an Own judgment as a premise. A known external Name
does not acquire `SeedExposure` from annotation absence at its use. It stores
actual declarations, not existence of some root with matching endpoints.

Consumers: original Call rule; IF Call formation; C-Call authenticity;
J-Owned's fourth accounting condition; A-UpperCallRef/L-UpperCall.
It does not include semantic `C0(Q)` as an assumed field.

### F2. `frame`

The selected `FrameCall(q_h,Q)`, including every field of IF §4:

```text
callee       : IF(actual CalleeRef)
argument     : open WholeCarrierSlot(actual WholeArgRef), with capture/latent IF
calleeResult : actual returned (v,U,r,current C1), dependent on callee
receiver     : IF(ExecuteCallable(U,argument,current C1))
result       : actual complete result (v_result,r_result,current C2)
future       : actual result-provider's dependent future interface
arms         : all original ArmDecl insertions and scoped references
source       : q_h, CallEff, u_f, u, exposure, ElimOrigin
```

Each slot retains its original complete parameters, hard constraints,
licenses, scoped binders and field maps. It includes the equations for
projections of actual contextual insertions, the shared Bind result/rebind
middle, all ordered pending suffixes, and lawful whole-map action. All
original source and non-source arm tags remain. A source diagonal does not
replace the open whole-carrier slot.

Consumers: selected source realization/complete observation; all IF
inclusions; native `Op` operand/field partition; J-Owned's conditions 2–3.

### F3. `primitives`

For each actual primitive/import/annotation leaf **already occurring** in
F1/F2, retain its original whole dependent contract, declaration identity,
license and scope, ordinary descriptor/hard-envelope proof function under
its original premises, provider/future and admission actions, and lawful
restriction/substitution actions. The field is a dependent product over the
original leaf occurrences, preserving multiple witnesses at the same slot;
it asserts no inhabitance of a primitive's observation or guard fiber.
It does not add a leaf called
`CallIsTyped(q_h)` or populate an empty license fiber.

Consumers: original primitive rules, active annotation interpretation,
source realization, independent admission, IF's genuine leaf premises,
and PF/NPR's primitive cases. Foreign leaf contracts stay foreign.

### F4. `sourceProtocol`

A dependent function under exactly the §3 quantifiers. For each original
source observation derivation `delta : M_E(q_h,O,w;j,e)`, it returns the
following stage-indexed original evidence. This is a data presentation of
the old constructors; it does not define `M_E` by the evidence being built.

| Actual original phase | Required fields of `sourceProtocol(delta)` |
| --- | --- |
| Initial / lookup | Hereditary binding and the complete suspended future suffix; no premature Delay, challenge, receipt, or output value. |
| CalRet | The same actual `v_h,U,r_h,C,w` returned by the original callee, its H* membership at that live event, and identity same-value checking. |
| Actual Delay formation | The actual whole Name code/capture/reify evidence, inert formation and its universal designated-execution function; exact whole inlet checking. |
| Checked challenge / entry | The independently assembled original d; same-provider `ActualAdm`; actual Invoke transition with its actual receiver/receipt and original typed paths/current preconditions. A precondition is not stored as an already executed receipt. |
| Value entry | Actual designated Force/pending development; on its actual Return only, the same value/root/current-world rebind and typed body environment. |
| Retained entry | Original RetainBind of that same carrier and typed body environment, without adding an entry Force. |
| Body / designated consumer | Original U-owned body, native delimiter and one-layer consumer evidence; operation providers retain native request-carrier return before the declaration-derived result consumer. |
| Request / raw resume at any phase | Actual operation instance/origin/payload, typed response interface, the same saved raw handle, the actual resumed current world, and exactly the unfinished ordered suffix. The proof function covers every admitted response, repeated resume and finite continuation. |
| Final Return | The actual result value/root/provider/current configuration, its ordinary complete descriptor and hard-envelope evidence, and original result correspondence. |
| Later use | That returned provider's own dependent latent/future packet, current compatible history and designated port; no invocation of h or maker's expired grant is substituted. |

The final result projection of this family is

```text
delta : M_E(q_h,O,w;j,e)
  |-> DescMem(ReadInvoke(H*,D_h,IF_h),O,w;j,e).
```

It is the selected source-image `CIncl` action. Its phase projections supply
the extra receipt/operation/observation fields instead of re-proving them
from scalar endpoints. EI-Name transports the very same packet to
`EvalInvoke(C_Read(H*,h),H*,D_h,A_h,IF_h)`; it does not extend ReadInvoke to an
arbitrary computed callee. The computed EI case needs its genuine callee
packet and actual CalRet first.

Consumers: original Call/Bind/Return/consumer rules; typed-core execution
and §8 guarantees; ReadInvoke/EvalInvoke introduction; suspended `Op.typing`.

### F5. `independentClauses`

For each actual declaration address alpha and its original ordered telescope
`Delta_alpha(j)`, retain

```text
inputs_alpha       : the original predecessor/operand tuple at that telescope
P_alpha            : original input/guard/license evidence
A_alpha(...,O;z)   : original whole output relation and witness
R_alpha            : independently declared complete output contract
local_type_alpha   : P_alpha -> A_alpha(...,O;z) -> DescMem(R_alpha,O;z)
domain_alpha       : original admission action for changed live coordinates
providerFuture_alpha : actual output-dependent provider/future interface
```

The field stores the **functions** over these original parameters and proof
inputs; it does not assert every P/A fiber inhabited. The actual declaration
also retains its finite predecessor list, scopes, constructor, original
whole-map actions, and whether closure is iterated. Z has no predecessor;
W uses its actual predecessor's original typed-input checking map and its
own new output packet. An opaque arm retains its entire original interface
as one declared leaf. Neither may be forced through a source trace.

Union composition uses the actual branch tag and original result injection.
Conjunction uses both original laws on one shared tuple. If a fixed result
target is imposed on the entire operation, each alpha's **actual target
inclusion** is required. A law into R_alpha alone cannot be relabeled as a
law into ReadInvoke. EI-All is available only at its adopted generated-result
case and preserves all original arm slots.

Consumers: full `C0` construction where required, C-Call/CallMem, complete
source-interface accounting, native Op independent license fields, and
EI-All/GC4. These inputs cannot be inferred from the existence of the slots.

### F6. `nativePackets`

For every original licensed key

```text
ell : L(I;Omega,beta_r,s,p,c), k : constituent of Omega,
field : its governed field, w : the original field-license witness,
```

retain the full packet at `(ell,k,field,w)`, its original local/inherited
origin, source and receiver attribution, scope/typed position, policy,
permission and original constraints/evidence. Unreached and unselected
schemas remain in F2; a key requires an actual license witness.

At a genuinely local unannotated governed field the policy is exactly
`FullProtection/NoConcreteRemovalGrant`. Every other key retains its
independent original leaf packet. This field is PF1's NP output, using PF2's
actual local operator functions and GC4 when the complete declaration needs
it. Printed owner equality does not classify an inherited field as local.

Consumers: selected native profile formation and L/DeclContribution
eliminations. This field is not an assertion of dynamic `Active` or a foreign
annotation predicate.

### F7. `packetAction`

The same original packet family's lawful action under each independently
compatible future extension, scoped renaming and selected whole certificate,
with original scope/incidence/provider dependencies. For generated native
fields its restriction is the NPR construction and satisfies

```text
NP(restricted original leaves, transported same license development)
  = restriction(NP(original leaves, original development))
```

at each transported actual key. Identity/composition act at the one shared
tuple. This does not assert surjectivity onto newly introduced future keys.
The six actual whole certificates are whole injective freshening, legal
uniform graft, the actual locally proved equivalent rewrite, total
fresh-coordinate definition, unchanged client conjunction, and original-scope
joint hiding with its real admission. Opaque original actions remain F3/F5
inputs. NPR derives composite native transport rather than assuming it.

Consumers: future Name/capture, ValueBind, pending suffix, typed packet
transport, scoped generalization/use where its original certificate applies,
and §8 future guarantee/routing retention.

### F8. `routing`

The original typed packet presentation and its **actual** edge relations:
boundary introductions, typed `Flow`, actual `Receive`, and source-derived
`Observe`. Its maps retain the whole `(v,t,chi,K,D,L)` with

```text
chi_out = union_i M_i* chi_i; D_out = union_i M_i* D_i;
K_out = the same shared K; L_out = inherited original identities.
```

Each image witness retains its original i,p and flow proof. A result takes
the actual returned value packet and the corresponding declared-result
packet at their respective typed paths. Equal value pointers do not union
unrelated alias views. The complete Call effect and latent-result effect
positions remain distinct.

For every original exposed request q and every original candidate handler
g at the **actual search configuration C**, retain the defining original
calculations:

```text
Path(q,u,b,p) = original matching Flow/Observe/Receive path evidence
Inc_C(q,g,b,p) <-> Path(q,owner(g),b,p)
   and Active(g,C) and Active(owner(g),C) and Active(b.receiver,C)
Protected(q,g,C) <-> exists b,p. Inc_C(q,g,b,p)
Grant(q,g,C) <-> exists b,p. Inc_C(q,g,b,p)
   and b.receiver=owner(g) and Gamma_b explicitly admits q.operation at p
Visible(q,g,C) <-> Active(g,C) and Active(owner(g),C)
   and Covers(g,q.operation) and (not Protected(q,g,C) or Grant(q,g,C)).
```

The current original handler order, exact coverage, outside-context
pattern/guard/arm subderivations and selected-operation compatibility remain
those of the admitted context/primitive. No statement says that an arbitrary
g is live, covering, visible, or selected. The field preserves the evidence
needed to **evaluate and transport** those predicates at every actual event.
It does not infer their truth from a static profile.

Consumers: typed-core §8 routing; common typed-view transport and lifetime;
ordinary shallow selection and current-state raw resumption. It is a
candidate presentation of those explicit reviewed consumer equations,
retaining the original event-edge evidence, not a claim that the native
signature adoption also adopted every typed-boundary clause or that an
independent Gamma_M has those equations.

### F9. `accounting`

The selected `C-Call` and `J-Owned` constructions at this exact Q, O1 and
IF frame: fixed `c_q,a_q` formed before an observation, original lexical and
checking incidence at their separate indices, and the four simultaneous
accounting conditions for every z in the unchanged full family. Complete
typing used here is **constructed** from F4/F5 and the original result
correspondences, where those actual laws are available; it is not an input
named complete C0. Every actual arm has its original complete placement and
attribution. No new mark, grant, receipt, Observe, or liveness is produced.

Consumers: original selected `Contrib/Inc/Cover`, A-UpperCallRef/L-UpperCall,
and any subsequent source condition explicitly using those selected cases.

### F10. `interpretation`

The original target M's binding of these selected presentations to its
**fixed** predicates. Where M literally uses the selected definitions,
the field is their identity action. Where M has a separately fixed component,
the field consists of its actual typed maps, at the same complete scope:

```text
profile_M : selected governed packet -> original M profile/permission packet
phase_M   : original source/operation phase fields -> M's same typed-state fields
j_C       : CallContract(Q) -> Contrib_M(rho_U)
j_I       : OwnedCall(o,q_h,c_q,IF_h) -> I_M(X)
```

The laws of these four maps are explicit, not an additional `AllConsumers`
field:

| Map | Required law at the original complete tuple |
| --- | --- |
| `profile_M` | Erasing the map returns the same governed field, boundary, source/receiver identity, scope, K/D and lineage. It retains the actual boundary-realization and governed-port correspondence and takes each original selected protection/annotation/permission witness to M's corresponding witness. When §8's fixed-domain routing comparison is the consumer, profile presence agrees and `Admits_selected(nu,p,op) iff Admits_M(nu,p,op)` for every original request point op; restriction uses the same original action. |
| `phase_M` | Erasure retains the same O,w, provider, current C, operation witness and phase. The original challenge and response/resume/future domains are identical, not filtered. Each original typed-state/hard-envelope witness is mapped at those indices. |
| `j_C` | For each full `CallMem_Q(h,O,w)` witness, give M membership at `j_C(c_q)` over that same h,O and mapped whole witness. In a claimed exact-fiber use, retain the actual back map on that fiber and both inverse equations, without quotienting equal observations. A merely forward use claims only its forward law. |
| `j_I` | For each of the two original indexed incidences, give `Inc_M(j_I(a_q),beta,s,p0,u_f,j_C(c_q))` or its checking-u counterpart at its own index. For every original z, map all four accounting witnesses to `Cover_M(j_I(a_q),z)` at the same tuple. |

For a consumer asserting exact preservation/reflection of an **active
existential**, the additional law is the exact named formula at that
consumer, for example preservation/reflection of
`exists a in I. Inc(a,beta,s,p0,u_f,c)`. Its quantified I includes the
unchanged original cases, not only the new OwnedCall image. This is a
specific original §9 compatibility requirement when such an exact claim is
made; F9 alone does not imply it. The present source-forward construction
does not claim this stronger reflection. A consumer with no selected
completion still uses its unchanged independent interpretation.

This is **the nonconstructible field in the general original-host reading**
from the supplied Name/GC/PF/NPR inputs. Its exact types come from original
complete-Call §4 and its construction §9, not from a newly proposed safety
requirement. It is not available merely because a proof object exists.
Nor is it required as a new arbitrary all-model comparison when the original
consumer is already definitionally the selected constructor interpretation.

## 5. Constructing the candidate's generated fields at the actual Name call

The following is an introduction algorithm for F1–F9 in their selected
interpretation, retaining F3/F5's genuine independent leaves. It is not an
introduction rule for the original undeclared `TypedCallCert_Dec`.

**Actual environment.** Apply VB1 to the genuine returned tuple and fresh
rebind:

```text
E1 = ValueBind(E0 restricted to e1, d_x@kappa, r_a, A,
               actual rebind origin).
```

Its h projection is exactly `(v_h,r_h)` and its x projection is exactly
`(v_a,r_a)` at `(C1,w1)`. Old bindings and histories are retained. Restrict
each projection by its own original hereditary action at an arbitrary later
compatible event. VB-NP supplies the selected native profile part of this
same restriction, including the new binding and pending dependent suffix.

**Formation and frame.** Use the actual Resolve/capture and reify records
to apply Gen-Call-0 and IF. At an actually supplied selected upper exposure,
`OShared-Register` and `OSlot-SharedInvoke` form its shared slot; the two
OOwn-Upper rules form its lexical/checking facets from the same original
seed, with no Own premise. For a route lacking that original seed there is
no own-upper case; its actual inherited/primitive provenance is retained.
F1 is those original records. F2 is the full IF Call constructor:
construct child frames, the whole carrier slot, the dependent CalRet/receiver
middle, result/future slots, and every actual arm's IF-Insert/IF-Use. These
are actual contextual insertions. Projection gives each original field, and
the Bind middle on both sides is the same returned tuple. This is GC1/GC2,
not endpoint-matching reconstruction.

**Same-value and carrier checking.** Name lookup restricts the actual h
child; `WF_Dec(H*)` is its independent formation and `VIncl(H*,H*)` is
identity on every represented decorated value. Name x followed by the
original Delay constructor supplies inert formation and universal
designated-execution validity from the actual x binding. Exact inlet
identity supplies whole checking. For any independently admitted open
carrier filling use that filling's original admission field instead.

**Protocol.** Define one function by inversion of the actual original finite
Call/Bind development. Initial/lookup retains pending obligations. CalRet
retains the actual decomposition and live world. At Delay use the preceding
carrier proof. Assemble each challenge from its independent context,
other-value, incidence and carrier inputs; apply R at the same provider.
Only the actual Invoke transition establishes receipt. E supplies the
complete actual receiver's entry/body/consumer evidence. At every Request
use

```text
Request(q,C,k) >>= S
  = Request(q,C, lambda(response,C'). k(response,C') >>= S).
```

Apply the same recursive proof to the shorter resumed development at C'.
Use the real typed Return for Value rebind; retained entry preserves the
carrier. At final Return use its actual provider's future packet. These
are all F4 phase cases. ReadInvoke-Desc applied to them is GC3. EI-Name
retains every field in either direction, not a second execution proof.

**Complete arms.** Keep F5's original declaration-local functions. For an
actual Union witness use GC3 on its source tag or the corresponding original
arm law and its actual result injection on its arm tag. For an original
Conjunction apply both laws at the shared tuple. Where a primitive consumes
a typed predecessor, use exactly its original input checking map; a union
result does not prove an arbitrary input type. Non-iterating arms stay
non-iterating; a finite declared positive development permits structural
recursion without moving future quantifiers. This is GC4's composition,
conditional on the actual complete signature and all actual target laws.

**Profiles and action.** Insert that suspended function in the existing

```text
Op(q_h,k,intro_h,typing_h,operand_interfaces,original_license_fields).
```

PF1 supplies F6 by induction over the actual L/DeclContribution derivation.
PF2 supplies the required local functions from genuine children. NPR, now
accepted independently, supplies F7. The constructor coverage is explicit:

| Original constructor | Packet introduction/restriction |
| --- | --- |
| Primitive, import, annotated leaf | Retain its actual whole packet and lawful original action. |
| Genuinely local unannotated field | Use the selected constant policy only at that licensed introduction. |
| Operand | Apply the actual whole field insertion and retain source provenance. |
| Ref, Scope, Rename | Retain the same registered antecedent and one original lawful scoped substitution. |
| Alt/Union | Preserve the actual branch tag, all schemas, and the selected witness only. |
| Pair/Conjunction | Keep the two proofs and shared equations at one tuple. |
| Op | Combine its actual operand partition and new-local partition; retain independent licenses. |
| Bind | Wait for the actual Return to append its typed rebind; before Return retain the dependent suffix. |
| Call | Compose all the preceding fields in the actual order, including every independent arm and actual future provider. |
| Record | Compose actual ordered children; latent fields are inert and share the resulting current tuple. |
| Result, Delay, Lambda/capture, designated consumer | Use their actual field insertions and genuine child functions, with only the original one-layer demand. |
| L-DeclaredPort, L-Reference, L-Annotation | Use actual insertion, reference, or governed-field annotation action. |
| L-UpperCall | Retain exact Q/SpecCall, constructed complete typing when available, O0/O1, IF and original license fields. |
| L-Whole | Apply precisely the six original whole certificates listed in F7, with their actual independent evidence. |

Registered cycles reference the original interface; induction is on finite
evidence development, not infinite graph unfolding. This covers the selected
native grammar; additional original source forms remain outside this local
construction, without being excluded from the parent language.

**Routing and accounting.** F8 is formed from the original child packets,
source phase edges and actual current configurations, using the explicit
image equations. F9 then applies the selected C-Call/J-Owned introductions
to the authentic Q, full IF, actual O1 and the composed complete law. These
actions construct the selected records before an arbitrary observation.
They are not obtained by choosing an owner or contribution separately for
each observation. The next section checks F8's actual consumer projections.

## 6. A derived routing calculation; limits of what it proves

For the same generated native graph, the F8 calculation is stronger than
just saying that profiles commute. It supplies the data read by the ordinary
routing consumer from the assembled packets.

Fix an actual observation phase, its exact request q, current candidate g
and live configuration C. Compare the original selected packet at a source
slot with its **same contextual copy** through IF/GC1. Each path-indexed
field is copied with its source tag. A witness of

```text
chi_out(p',b) = exists i,p. chi_i(p,b) and M_i(p,p')
```

is the very same `(i,p,source witness,flow witness)` on both presentations.
The corresponding D witness retains its original K identity; L is unchanged.
Composition of actual insertions concatenates the same matched intermediate
paths. The receipt edge occurs at the actual receiving binding; the Observe
edge occurs at the actual source phase. Consequently every assembled Path
witness has the same boundary, request event, receiving occurrence and
matched path on these two presentations, and projection recovers it.

This is a fiberwise statement about the actual copied slot. It does not
claim every path of an unrelated target graph is in the image, or collapse
other aliases/arms that happen to print the same endpoints. Shared Pair
fields keep their original shared equations; independent arms use their own
original slot, witness and local correspondence.

Substitute these identical Path fields and the **same actual** activity,
owner, coverage and original annotation evidence into F8's equations.
The selected `Inc_C`, `Protected`, `Grant` and `Visible` predicates agree
under that copy. Ordered selection therefore reads the same candidate
predicate in the same order; its actual outside-context match/guard/arm
derivations remain the admitted context's own. This neither proves such
an arm succeeds nor chooses a handler in advance.

For a later compatible event, NPR/VB-NP and the original leaf actions repeat
the same calculation at its current C'. They do not transport `Active(g,C)`
as if it were `Active(g,C')`. At receiver/handler expiry the latter facts
are absent and the equations yield no stale grant. On raw resumption the
saved handle and event correspondence persist, while the candidate
configuration is current. A latent future observation uses its own actual
provider/path and newly established Observe edge.

Thus the selected Name-call packet supplies **the copied-field routing
calculation for the candidate's explicit equations**, including the
current-state operands of the routing consumer when their original event
evidence is supplied. This is a derived calculation on F8's presentation,
not a newly proved source-to-native boundary-realization theorem. No
independent premise named generated-routing coherence is needed for that
calculation. A separately fixed
`Gamma_M`, `Path_M`, `Inc_M` or active source-family predicate is outside
this identity calculation and belongs exactly to F10. The result does not
derive primitive annotation truth or any live grant.

## 7. Exact unresolved declaration choice and discriminator

The original sources distinguish three operations that cannot be conflated:

1. assemble the selected constructor records;
2. use those records with the selected consumer meanings;
3. transport them into a separately fixed active interpretation.

F1–F9 make (1) and the relevant (2) explicit. F10 is required only for (3),
at the original interpretations actually retained by the target. The
unresolved owning declaration must say which named certificate fields are
definitionally selected meanings, and which are independent host fields.
It must then either expose their lawful original maps or leave that instance
open. Naming all fields without this choice does not identify the original
judgment.

The exact review questions are:

- Does the original `TypedCallCert_Dec(c,F,e;xi)` for this selected case have
  precisely F1–F10 as its introduction/elimination telescope, with the WF and
  inclusion facts supplied by the surrounding G_call conjuncts? If a field
  has a different type, name its actual consumer and refine that field;
  do not silently redefine the original predicate.
- For each F10 component, is the target's original meaning the selected
  constructor interpretation, an independently supplied primitive/foreign
  meaning, or an already proved typed interpretation map? The answer is
  fixed at the target's semantic owner, not selected independently at each
  request or after a query succeeds.
- Does a claimed exact use need a full membership back law or active-consumer
  reflection? If so, retain it at the corresponding F10 component. Forward
  observation preservation does not imply it.

There is a concrete discriminator, explicitly exposed by the original
[owned-Call construction §9](2026-10-07-owned-call-contribution-construction.md#9-conservation-and-separately-fixed-original-interpretations).
Take an actual selected `a_q=OwnedCall(...)` with all four accounting
conditions. Keep the same Q, source code, typed children, challenges,
execution, original profiles and original observation witnesses. Consider
the old active consumer

```text
exists a in I_M(X). Inc_M(a,beta,s,p0,u_f,c_q;X).
```

A fixed interpretation having no corresponding old I_M/Inc_M constructor
does not satisfy this formula merely because a new selected OwnedCall was
formed. The selected extended interpretation with its actual J-Owned
constructor does. The operational reduct and F1–F8 can be the same on the
compared Call while this active formula differs. Therefore erasure,
ordinary typing preservation, GC3 result inclusion, and NPR cannot furnish
`j_I` or the applicable back/reflection law.

This is a separation of the proposed inference between those interfaces,
not two complete Authority-consistent models of Yulang, a bad source program,
or permission to choose an empty host interpretation for a real instance.
It identifies the exact test the owning declaration must pass. The same
test at a separately fixed governed profile uses its own original
annotation/permission predicate; equal native field indices do not prove
that predicate. F10 cannot be dropped without verifying identity there.

Conversely, when the original target literally uses selected C-Call/J-Owned
and selected native governed-field semantics, F10's relevant components
are identity and should **not** become a new all-model premise. This prevents
the present boundary from becoming an unnecessary blanket blocker.

No global progress field can be inferred as another hidden component:
§2.2's actual typed reachable stuck state refutes that inference for the
existing formal fragment. Source/core initialization, machine completion
and the original progress proof keep their own owners.

## 8. Original solved-G_call reconstruction without a new certificate rule

Fix the original representation-preserving decorated Call rule used in
generation §5, at the same source occurrence and interpretation. Let the
actual callee and whole-argument child derivations be reconstructed at their
original source interfaces and scope; this is the legitimate recursive
induction input, not the desired judgment for the whole Call.

Suppose a full solution a satisfies the **original** relation

```text
exists_sigma(F_c,e).
  WF_Dec(F_c;xi)
  and VIncl(A_f,F_c;xi,e_value)
  and WholeArgCompatible(J_x,CarrierContract(F_c);xi,e_arg)
  and CIncl(ExecuteCallableImage(J_f,Delay(J_x),F_c,e;xi),
            original Comp(E_c,A_c);xi,e_result)
  and TypedCallCert_Dec(c,F_c,e;xi)
  and Role_0 and canonical Gen-Call-0 records.
```

**Local reconstruction theorem.** Those actual children and that full
solution construct the original decorated Call derivation at c, preserving
the same scoped assignment and witnesses.

**Proof.** Eliminate the scoped existential **inside sigma** to obtain its
one F_c,e and all conjunct proofs. Do not project the value, carrier and
result coordinates into separately hidden witnesses. Apply same-value
checking to the reconstructed callee using e_value. Reify the actual whole
argument at its original source reify origin and use e_arg at its exact
carrier contract. Apply the original decorated Call rule with its supplied
WF, complete source-image e_result, original `TypedCallCert_Dec`, role and
Gen-Call-0 evidence. This rule's conclusion has the original source Call,
not a newly defined selected subset. Its witness consists of those same
scoped F_c,e and the children's original witnesses. Pack it under the
original sigma. All projections to the solved source occurrences are the
ones just eliminated from a; hence the local original `sameScoped`
correspondence holds, including shared captured roots and rigid imports.
Here this is the rule-level scoped correspondence in original generation
§5; the generic Lean `SourceProblem.sameScoped` still has no concrete original
source interpretation, so the paper argument is not a Lean instance of it.
This is direct original-rule introduction, with no native correctness,
successful execution, or final Call source judgment among its premises. □

The certificate telescope need not be reintroduced in this proof: it is
already a conjunct of the full original solution. Equally, a scalar native
solution cannot be substituted for this full solution. The construction
does not show that arbitrary satisfying decorations are native outputs.

The induction extension must be stated with its exact source coverage:

| Original constructor | Reconstruction from its actual original generation clause |
| --- | --- |
| Name | Use its resolved lexical/shared root and the full solution's corresponding original environment interpretation; retain the same scoped use. A raw name ID does not prove membership. |
| Result | Apply the original Return/forwarding rule to the reconstructed child, keeping the source Value/Computation tag and actual result/provider port. |
| Lambda | Reconstruct the body under its original formal and capture telescope, retain actual entry and designated consumer, then apply the original closure rule. Do not obtain recursive membership merely from registration. |
| Bind | Reconstruct first and second children at the original dependent result/rebind telescope; use its one shared middle and original ordered suffix. |
| Call | Apply the local theorem above at the exact original full G_call solution. |

These are precisely the Name/Result/Lambda/Bind/Call decorated rule envelope
named by generation §5. A finite derivation induction applies when each
actual original generation clause carries these independent decorated
premises. It is not a new global generation definition by typing.

For completeness of the audit, the original source documents also name
Literal/primitive, immutable Record, Operation, Reify/Delay, designated
Eliminate, Handler with patterns/guards/arms, explicit introductions,
registered recursive references, annotations/checking and admitted
conversions, generalization/fresh uses, and stateful/imported interfaces.
Some have selected IF/native constructors and local typing proofs, but
generation §5 does not present an exhaustive solved-constraint reconstruction
clause for all of them. The original full-scope theorem must include their
actual clauses and non-source conservative alternatives, not relabel the
five-row envelope as the source language. In particular:

- Operation must keep native return and its explicit declaration consumer.
- Handler must keep exact coverage/ordered outside match, guard and arm
  derivations and raw continuation/world semantics.
- Recursive references require their original source realization, rather
  than unfolding a static graph as a proof of semantic membership.
- Generalize/use must retain rigid imports, one hidden witness, all original
  use/future dependencies and the selected scoped transformation evidence.
- Executable conversion cannot be replaced by same-value checking or erased
  by a solved-shape rule.

The existing `SourceProblem` has no concrete declaration of these original
predicates in Lean. A new Lean structure that assumes the Call rule or the
desired reconstruction action would only repackage this paper inference.
No such module is introduced here.

## 9. Parent application and next concrete integration test

This packet removes ambiguity about what a proposed Call evidence producer
has to expose to the existing consumers. F1–F9 have a concrete construction
order and complete phase/arm/profile field types. The candidate routing
calculation explicitly consumes GC/PF/NPR and the retained original
event-edge evidence at the real current event; it does not assert a new
boundary-realization result.
F10 identifies the exact independently interpreted seam, with a discriminator
that can be checked at the declaration owner. It is not another unnamed
local-profile or complete-certificate premise.

The next review can make a concrete determination: compare the owning
original certificate introduction/eliminations against F1–F10; identify
the actual M interpretation of each field; mark identity fields as such;
and supply or reject a specific `profile_M`, `phase_M`, `j_C` or `j_I` action
where the consumer is separately fixed. A field requiring an original
predicate unavailable from genuine leaves cannot be waived. If this
candidate misses a consumer, the consumer must name its demanded field and
the declaration must be revised before adoption.

Separately, the actual native bridge must construct the full G_call solution
with those source/decorated meanings. The local reconstruction in §8 can
then consume it without manufacturing the certificate again. Actual
recursive child realization, complete independent arm laws, all-source
generation/reconstruction, original solver/source correspondence and generic
machine safety remain open. There is no production/cutover promotion.

## 10. Verification and stop boundary

Read the original consumer definitions, not only earlier seam reports:
typed-core §§2–4, 6–9; typed-view transport §6; original generation §§3–7;
complete Call and its active-consumer boundary; O1 §§2–4; native signature
formation §§1–4; IF §§3–6; contextual Function
membership and semantic-input R/E/W/D; selected ReadInvoke and EvalInvoke;
VB1/HC1/HC2; GC1–GC4; PF1/PF2; NPR/VB-NP and its independent acceptance;
the exact Lean CallTerm/subrecords, typing/preservation/progress declarations,
`Contracts` and `CoreComposition`.

Verification is paper constructor/consumer coverage and source-byte hashing.
No Lean module or executable checker was needed: the original semantic
predicates are not represented by a concrete Lean source instance, and an
opaque replacement would not verify this declaration. No compiler test,
benchmark, network, Git mutation, shared-status edit or child dispatch ran.
Only this note and the assigned handoff were written. The candidate is not
self-certified; primary independent review is required. Hashes and frozen
write cessation are recorded in the handoff.
