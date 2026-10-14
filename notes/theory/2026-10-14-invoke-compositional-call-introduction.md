# `invoke`: compositional complete-Call introduction

Date: 2026-10-14
Status: Draft mathematical constructor completion; the earlier conditional derivation and prior §6.3 / complete-image amendments were independently reviewed; §6.5's direct BOUND application was independently reviewed; the shared-result-port amendment in §§6.1, 6.3 and 6.4 remains unreviewed; no production or parent certification
Baseline: `add2fdf4c12e7379e1c5ad2c24b5023320262ae3`
Branch: `research/simple-sub-intrusion`
Definition authorization: the user's current instruction, "定義が必要なら定義すればいい"
Scope: the new source case is strictly
`Apply(Name(resolved unannotated Value formal), Integer literal)`, specialized
below to the body of `my invoke f = f 1`, from its source children and
independently declared local primitives. This is a definition/proof domain,
not a compiler support restriction. No new inference search, public type
constructor, or production cutover.

## 1. The change in method

Do not take `OriginalGenCall0(c)`, `TypedCallCert(c)`, `C0(c)`, or a complete
already-typed Call kernel as an input. Define the missing compositional
introduction and prove its typing by cases on its constructors.

The primitive signature remains the one in Source Generalize L1: local
primitive meanings, typed operand/result interfaces, licenses, guards and
world/provider/future laws, fixed independently of this source Application.
That signature is not a certificate about `f 1`. In particular a primitive
called `CallIsTyped(c)` is not an admissible way to discharge this construction.

The important design choice is **branch-preserving result synthesis**. The
result contract is assembled from the receiver's complete result contract and
each independently declared alternative's own complete result contract. It is
not the receiver's contract imposed as a filter on all other alternatives.
This choice avoids both a missing whole-Call typing premise and silent deletion
of alternatives. The exact whole membership relation is retained alongside
this result contract, so taking a result union does not uncorrelate the Call.

This completes one new source-constructor case. It leaves old source-rule
cases available. It does not identify the new case with a separately fixed
opaque historical relation whose constructors have not been provided. The
source/native representation theorem and public principal projection are not
claimed here.

## 2. Existing constructors used, without replacing their meanings

The governing interfaces are:

- [Source Generalize](2026-10-08-source-generalize-definition-and-proof.md),
  L1-L5 and sections 3.1-3.3: primitive, Name, Literal, Parameter, Lambda,
  Result, Delay, Bind, checking, and their original ordered telescopes.
- [The source-owned Lambda](2026-10-11-invoke-original-call-proof.md), 4.1:
  `F_L = Strict(I_f, formal:A_f, R_L, IF_L)` and the same-frame entry map.
- [Contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md),
  2-3: independently formed challenges; acceptance and complete observations
  at each genuine actual provider; hereditary immutable membership.
- [Complete Call](../design/2026-10-07-complete-call-contribution-definition.md),
  2-4, and [source interfaces](../design/2026-10-08-call-source-interface-definition.md),
  2-3: callee Bind, actual receiver execution, all original alternative clauses,
  IF-Insert/IF-Use, open carriers, and output-dependent future interfaces.
- [Constrained presentations](../design/2026-10-05-source-contracts-and-common-allowance.md),
  2.1-2.2 and 3.7: joint conjunction/union, scoped binding, constructor images,
  independent descriptor membership, and evidence-preserving abstract arms.
- [Application_N](2026-10-08-flat-application-owner-completion-decision-object.md),
  4-6: useful static source spine, not a proof of complete Call typing.

Only Call composition and its source-owned formation are completed here.
`Return`, `Delay`, primitive validity and complete Function membership are not
redefined as membership in this newly generated source program.

## 3. Types of the local inputs

### 3.1 One dependent frame

Fix the actual source nodes `L,d_f,u_f,c,a` and `Resolve(u_f,d_f)`. All objects
below are indexed by their original binder tree and one joint `xi=(nu,K,D)`.
Write `h : H_c` for a full independently valid input frame of the Call. Its
fields include the original environment, event/world, callee hole and the
**open** whole-carrier hole with its declared contract. They are not independent
per-port existential choices.

Write `o : Obs_c(h)` for the full original observation tuple. It includes the
Return or pending prefix, current guards, actual providers/worlds, receipt,
response, raw resumption, ordered continuation and compatible future-demand
interface. This is an abbreviation for the existing dependent observation
interface, not a new runtime object.

The actual source argument is one section of this open input frame. The domain
`H_c` is not restricted to that section, successful invocation, or Return.

### 3.2 Local alternative declarations, not a whole-Call oracle

At the generic operator declaration, retain every original alternative's
actual declaration address and complete interface. A declaration `j` has:

```
Delta_j(h)                  original ordered local telescope
P_j(h,delta,inputs)         original input/guard/license evidence
A_j(h,delta,inputs,o;z)     original whole-tuple relation and its witness
D_j(h,delta,inputs)         independently declared COMPLETE output contract
local_type_j               the declaration's local output typing law
```

Its typing law has the precise shape

```
local_type_j :
  P_j(h,delta,inputs) -> A_j(h,delta,inputs,o;z)
  -> Mem(D_j(h,delta,inputs), o).
```

Every parameter and result occurs at its original scope. `inputs` may contain
the predecessor observation of a W clause. It must contain that predecessor's
original typed input/guard evidence when the primitive requires it. Mere
membership of a predecessor in the Call is not substituted for such evidence.
An output-changing clause retains its own domain action and output-dependent
provider/world/future interface. A source-independent schema may be
instantiated at this source use; it may not require the conclusion
`C0(c)` or an unprovided whole-source preservation law.

These are precisely the existing L1 primitive contracts. Their meanings and
witnesses are kept, not guessed from effect rows. An opaque declaration is
permitted; an unspecified predicate with a promised result endpoint is not.
The construction below is uniform in these declarations: no new choice of W
or Z, no enumeration of observations, and no assumption that their domains
are empty is needed.

The source kernel's complete clause signature is part of its declaration.
When forming its use, copy the complete signature, not a list of arms selected
by a successful query. An absent signature is not an empty signature.

## 4. Definition: a dependent union of complete result contracts

For complete contracts `D_j` over the same incoming frame, define their
scoped union using the existing union and scoped-binding clauses:

```
Mem(Join_j D_j, h, o)
  = sum over the original arm addresses j,
    with delta and inputs bound at THAT ARM'S original positions,
    of (P_j(h,delta,inputs), Mem(D_j(h,delta,inputs),o)).
```

This notation keeps the whole tuple, not just its ordinary value/effect
projection. In particular, its output future interface is the dependent union
of the actual branch's future interface. It does not reuse another branch's
future proof. The arm address is proof/source incidence, not a runtime sum tag.
For fixed-schema input/output aliases the same fields are shared, not copied.

There are explicit introduction maps `inj_j` and a case eliminator. Both are
just the existing logical union/scoped-binding constructors. They preserve
all operand identities and the complete dependent evidence. They do not
identify two different witnesses just because their observation projections
are equal. The union can be a finite graph of references to opaque/infinite
families; it need not enumerate their members.

The binder order is essential. `h -> (j,delta,inputs,...)` is a dependent
elimination under `h`, never `(j,delta,inputs) -> all h`. The generated graph
is built before events, while these variables remain underneath their
original event binders in its interpretation.

## 5. Definition: complete Call from its constructors

### 5.1 Structural constructor

For actual source callee code `n_f` and an admitted whole carrier `kappa`, put

```
S_c = Bind(n_f,
  (v,U,r,current_world) => ExecuteCallable(v,U,r,current_world,kappa)).
```

This uses the original Bind and ExecuteCallable relations and their full
observation witnesses. Its suffix includes receipt, the actual U's entry,
body, designated consumers and invocation return. It does not install a
Value entry or a Pure role on the supplied callable. Callee-pending and
receiver-pending suffixes remain distinct. Let `D_s` be the complete Bind
contract formed from the callee contract and the checked Function's complete
receiver-result contract, with the original dependent port maps.

The structural typing map `type_s : S_c(h,o;s) -> Mem(D_s,h,o)` is NOT an
input to source elaboration. Section 7 constructs it for this actual source.

### 5.2 Independent clauses and full operation membership

Define the new complete Call witness family by these constructors:

```
Struct(s)             where s : S_c(h,o)
Z(j,delta,p,z)         where p : P_j and z : A_j(h,delta,(),o)
W(j,q,delta,p,w)       where q : Call_c(h,x), p : P_j,
                            w : A_j(h,delta,x,o)
```

Equivalently the exhaustive generic alternative constructor is

```
Arm(j,delta,q_1,...,q_n,p,z)
```

where the declaration fixes the finite original predecessor-reference list
and its dependent telescope; the q_i fill exactly those references, and p,z
are the original primitive premises and output relation evidence. Z has no
predecessor and W has one. An opaque independently declared arm can occupy
one atomic declaration with its entire original interface and witness family;
it is not forced through Struct. Universal future obligations remain inside
that original interface, not new recursive universal premises on Call_c.

Use W's finite positive closure only when the declared operator has W
closure. A declared non-iterating arm is used once, not silently changed into
iterated closure. The typed reference graph retains those distinct roots.
Existing primitive guards and evidence remain exactly in p,z,w; no extra
output-success test is added.

This defines the missing composite operation from its declared clauses. It
does not take an already formed `Call_c` operation or its typing as a premise.
The new source use is the scoped instantiation of this generic declaration.
Its arm-to-root and root-to-source incidence are IF-Insert followed by IF-Use.
An independently fixed old root needs its actual constructor identification;
this definition is not a cast from any arbitrary old predicate.

Define the synthesized complete result contract to be

```
D_call = Join(D_s, all original D_j at their original scopes).
```

The independently interpreted ordinary descriptor conjunct is still present.
The retained complete constrained root uses BOTH `Call_c` and `D_call`.
Section 8 proves `Call_c -> Mem(D_call)`, rather than defining descriptor
membership to mean `Call_c`. Consequently that conjunct discards no generated
or independently licensed Call witness.

**No guard trick.** In particular, do not replace a Z or W output with
`A_j(...) and Mem(D_s,o)`. An alternative whose own contract differs from
`D_s` is retained through its own injection into `D_call`.

## 6. Definition: the source-owned demand and formation rule

### 6.1 Parameter and application descriptions

Reuse the existing Parameter declaration `A_f` and actual registration at
`d_f`. In the new owner's pre-challenge source description region specified
in section 6.3, introduce the result/effect holes required by the Application
rule program, with complete descriptive sorts and their original
free-dependency telescopes. The function's result and the Application's value
result use the same source endpoint `A_c`, as in the ordinary Application
rule's single result type. Invocation effect `E_i` and whole-Application
effect `E_c` remain distinct. A native row number alone does not determine
these complete telescopes. No actual returned provider/world, response or
body witness is moved into a description binder.

Let `J_a` be the argument's complete declared carrier interface. Form `R_i`
using the existing complete computation descriptor constructor, with the
shared Application result endpoint `A_c`, invocation effect-description hole
`E_i`, and its typed observation interface. Thus
`R_i = CompleteComp(E_i,A_c)`. The whole Application output remains
`CompleteComp(E_c,A_c)`. A Return port binds its actual value/provider
and current world; a Request/pending port binds its actual packet, response
and raw suffix instead, without an invented returned value. The future port
is a dependent family over that actual output and the original compatible
extensions. Forming these binders is not choosing any of their inhabitants.
All original K/D, authority, path and hard-envelope predicates remain in the
complete descriptor. The holes are descriptions, not alleged proofs of those
predicates. This is not reconstruction of R_i from four native scalars.

The new demand constructor is

```
F_c = FunctionDemand(J_a, R_i, IF_c).
D_Fc = independent complete checked challenges for (J_a,IF_c).
P_Fc = the complete observation contract R_i at that same challenge.
```

`IF_c` is the demand-owned interface defined in section 6.3. The separate full
Call incidence graph retains the actual source ports and every complete
declaration/reference interface by IF-Insert/IF-Use. The full checked
challenge formation uses its
original context, other bindings and checked whole carrier. Neither actual-U
acceptance nor invocation-output safety is a challenge-formation premise.

Function membership is the existing contextual membership at these interfaces:
each actual decomposition must accept every such challenge and satisfy `R_i`
on every complete/pending observation and compatible future development.
Thus FunctionDemand completes the source descriptor's formation, not a new
callable-membership axiom or runtime wrapper.

The Application generates its original same-value bound `A_f <: F_c` at the
actual checking occurrence. In a symbolic source derivation the local inclusion
witness is a parameter of the generated constraints. It is not manufactured
from native query success. This is the ordinary inference obligation on the
unknown formal, NOT an additional premise asserting that the whole Call is
already well typed.

### 6.2 Gen-Call-Syntax: use the actual argument constructor

The formation rule is

```
actual Apply c = Apply(Name u_f, Integer a k); Resolve(u_f,d_f)
actual unannotated Value Parameter d_f; Parameter/Name derivation at d_f,u_f
Integer Literal derivation at a,k; Result and Reify/Delay derivations
complete demand F_c and actual checking occurrence
complete instantiated operator declaration and source-reference graph
-----------------------------------------------------------------------
Gen-Call-Syntax(c):
  original beta=(d_f,R_f), callee lexical use, actual argument-source use,
  checking occurrence, invocation and complete-Call output ports,
  ElimOrigin, and the complete dependent Call rule program
```

The new argument premise is the actual Integer Literal constructor, with its
`Data(a,Value(Int),...)` conclusion. For this source k=1. This is the selected
Name/Integer extension of the old Name/Name Gen-Call-0 spine; it does not
fabricate an argument lexical resolution. The old source constructors remain
available with their original domains and premises.

More precisely, extend the original formation judgement by this new
constructor, using the argument coordinate

```
SourceArgumentUse = NameUse(actual lexical derivation)
                  | IntegerLiteralUse(actual Integer literal derivation).
```

The old Name/Name constructor embeds with NameUse unchanged; every other old
constructor is retained unchanged as well. IntegerLiteralUse is admitted by
this new formation rule only at the resolved unannotated Value-formal seam
displayed above. It introduces no case for other non-Name data constructors
or computed callees. It cannot be projected to a nonexistent lexical witness.
The `OriginalGenCall0` request for c is discharged by this extended formation
judgement, not by a cast to the old Name-only input record. Its Rust input
interface must be updated at the owning definition when implementing this
case; the current `ArgumentLexicalUse` enumerator is not that implementation.

The formal shared root, immediate invocation position, whole-Call result
position and result-latent positions retain distinct roles even if a later
representation uses the same native term. Source-owned seed/exposure records
use the existing policy at their actual lexical/checking occurrences; they
create no dynamic receipt or authority. No proof of final ownership/coverage
is asserted by the static record alone.

### 6.3 Definition amendment: demand prefix and dependent Call-site suffix

This is a Draft owner-rule amendment for the new Name/Integer constructor,
under the current definition authorization. It retains every old source rule.
It defines the scope of this new Application inference introduction; it does
not hoist an existing event-local declaration or identify an independently
fixed foreign Function interface. Native correspondence remains separate.

The decisive distinction is supplied by the selected contextual Function
constructor, not by erasing a callee certificate. In
[semantic input realization](2026-10-08-call-semantic-input-realization.md)
section 2, the independently typed punctured context has a callable hole
typed at the checked F, without requiring membership of the tested callable.
Its challenge inputs are that context, its other valid values, the registered
hole values/incidences and whole-carrier admission. The callee Name/Result
certificate at A_f is an input of the enclosing Call's Bind/check, not an
additional input of this Function challenge constructor.

**Actual descriptive inputs and owner equation.** Let Delta_0 retain the
complete dependency-closed static signature inputs used below: the actual
Integer declaration and fixed source operands a,k, the independently declared
Result/Delay port schemas and original license families, and the independently
interpreted complete Function/computation signature. This retains their
original K/D, authority, scope, hard-envelope
and action declarations. It neither supplies their semantic inhabitants nor
replaces them with four scalar sorts. The actual argument description is the
whole-carrier schema J_a from section 6.1, whose ordinary projection is
Comp(empty,Int); that projection does not define or truncate its complete
interface. Its independent open fillings, latent fields and inherited
origins remain bound at their original challenge
positions. The source-produced Delay(Return(k)) is still only its section.

The new Application owner emits its result/effect descriptions before
challenges, with actual source owner c and type-scope node sigma_c := sigma_f,
the enclosing Parameter's type scope. It introduces the result endpoint once
as `A_c` and reuses it in both the Function demand and whole Application
output. This is the ordinary Application rule's one result type, not an
equality inferred from solved endpoints. Invocation effect `E_i` and whole
Application effect `E_c` keep their distinct roles. This common scope is a
choice in this new owner rule, not a claimed scope equality supplied by
Application_N's Demand-N. Source Generalize section 3.3 explicitly permits an
independently specified inference introduction to declare ordinary endpoints
and records their owners, sorts, type scopes and free dependency telescopes.
Its table's ViewLogic and EventProof rows separately place
logical/interface proofs in their source description or event regions. These
are the rules used here:

```
Delta_0 |- A_c : ValueDescription
Delta_0 |- E_c : EffectDescription
Delta_0 |- E_i : EffectDescription
Desc(C,(c,application-result),ValueEndpoint,sigma_c,Delta_0):A_c
Desc(C,(c,application-effect),EffectEndpoint,sigma_c,Delta_0):E_c
Desc(C,(c,invocation-effect),EffectEndpoint,sigma_c,Delta_0):E_i
Delta_D = Delta_0; A_c; E_c; E_i
Delta_D |- R_i = CompleteComp(E_i,A_c) : CompleteComputationDescription
Delta_D |- R_c = CompleteComp(E_c,A_c) : CompleteComputationDescription
Delta_D |- IF_c = DemandInterface(J_a,R_i) : CompleteFunctionInterface
Delta_D |- F_c = FunctionDemand(J_a,R_i,IF_c) : ValueDescription
```

ValueDescription and EffectDescription here are the existing complete sorts
with the retained signature dependencies. These are ordinary flexible Desc
introductions, with actual owner c and source type scope in that description
region. A body's EventProof can subsequently use them under its original
invocation telescope. Source Generalize section 3.3 permits an independently
specified inference introduction to supply precisely these records. The
owner selects this pre-challenge introduction for the new constructor; its
permission for other body-owned introductions inside events remains intact.
The actual Result/Delay applications and their event-local license witnesses
remain in Site_c, at their original source events. Delta_0 retains the
independent declaration families with those variables still under their
original binders; it does not copy an actual body-event application into the
description prefix.
The source-owned Lambda section 4.1 already forms its body rule program
before challenges while retaining its post-Force/rebind event telescopes.
This amendment adds the displayed pre-challenge description records to that
program; it leaves all those original event telescopes inside it.

DemandPrefix_c is the dependent record of these three Desc introductions and
their constructor-defined R_i, R_c, IF_c and F_c, over the one retained
Delta_0 input. It is formed by the displayed Application owner constructor;
its eliminator returns those same descriptions, provenance records and terms.
It has no inclusion, acceptance, observation or whole-Call typing proof field.

DemandInterface is the following ordered schema, using the existing complete
Function/challenge and complete computation constructors:

```
description: J_a, R_i and their complete original descriptive dependencies;
challenge: the original independent punctured-context/other-value/hole/
           carrier-admission telescope for J_a;
invocation: the same callable hole, actual Act(v,U,r), original receipt,
            entry/consumer/ExecuteCallable and their dependent action ports;
observation: the whole R_i telescope at that challenge, with Return and
             pending alternatives, their actual worlds/providers/responses/
             raw suffixes, and all original compatible future extensions.
```

Every runtime operand in the last three rows is bound by its original
challenge, actual-decomposition, observation or future constructor. Original
primitive/relation references retain their complete signatures and actual
dependent parameter maps there. In particular ExecuteCallable is parameterized
by the bound actual U, not by the source expression Name(u_f). Its operation
and every receiver-local alternative remain the actual U's complete operation.
The signature of a tested callable is not obtained by reading its source
callee's A_f certificate. The callee Name/Result reference is absent from
this schema because it is absent from the selected Function challenge and
observation constructors, not because its evidence was declared irrelevant.

**Dependent full graph, with no discarded slot.** The Application also emits
the complete Call-site suffix Site_c(A_f,F_c). It retains the original formal
registration and Name-use interface; Result at Comp(empty,A_f); argument
Result/Reify; the actual VIncl(A_f,F_c) checking occurrence; the callee Bind
result/current-world tuple; receiver, complete Call result/future ports; and
every original declaration/Arm/IF-Insert/IF-Use substitution. All its fields
retain their original dependencies. The checking occurrence is an OPEN
obligation, not a proof of inclusion produced during formation.

In particular callee_result still has its A_f-dependent original result
interface. The receiver uses its same returned raw value/provider and current
world through the existing checking/Bind map. No A_f certificate is erased,
and no callee result is cast to F_c during graph formation. The typing schema
uses the eventual witness of the generated inclusion at this exact map,
as in section 7. This use does not participate in forming F_c.

Define the new owner's full graph by ordered dependent pairing:

```
Full_c = (D : DemandPrefix_c; S : Site_c(A_f,D.F_c)).
pack(D,S) = FullCallGraph_c(D,S)
demand(FullCallGraph_c(D,S)) = D
site(FullCallGraph_c(D,S)) = S
unpack(G) = (demand(G),site(G))
unpack(pack(D,S)) = (D,S)
pack(unpack(FullCallGraph_c(D,S))) = FullCallGraph_c(D,S).
```

These are constructor beta equations. FullCallGraph_c retains the same
registered nodes, contextual slots, original field types and cross-references
as its two inputs, with no independent copying of a shared middle tuple.
Grouping nodes into two records changes no original clause, binder, parameter
map, witness or graph edge. In particular this is a dependent pair, not an
assertion that the Call-site suffix is independent of its callee or demand.
Every whole-Call arm remains in S; a receiver-local arm remains in the bound
actual operation of U as well as its original contextual placement in S.
Their output-dependent interfaces remain separate. The new equations claim
no erasure equivalence for an independently fixed historical graph.

**Unchanged Function fields.** Apply the original checked-challenge
constructor to fixed original input fields. It returns the same context,
other-value evidence, callable/carrier holes, incidences and carrier-admission
fields in either grouping. None of its constructor arguments is S's callee
Name certificate or generated inclusion witness. Apply its existing
observation/future constructors at that same challenge and actual U: their
arguments and dependent fields are likewise the same bound operands and R_i.
Thus factoring the caller slots out of the descriptor changes neither an
admitted challenge nor any complete/pending observation or future field.
The original full Call still needs its callee prefix and inclusion to USE
that descriptor. The statement concerns these actual selected Function
constructors; it does not assume proof irrelevance, license weakening or a
projection of arbitrary active old constrained-root predicates.

**Scope and independence derivation for this amended owner.** Delta_0 is a
declaration/signature telescope, with runtime variables retained inside the
original schemas.
The literal has no callee reference. The complete Function/computation schema
uses its own description parameters and bound callable/context/observation
fields. The new Application parameter maps substitute J_a,A_c,E_c,E_i and their
complete signature dependencies, never the source operand A_f. This is an
equation of the new owner applications, not an inference from the chronology
of an opaque declaration. Consequently neither A_f nor an enclosing Lambda
EventField occurs free in Delta_D's demand
applications. Traversing the complete explicit and implicit arguments gives
the same conclusion: no actual callee Name/Result reference occurs there.
Those references occur, unchanged, in Site_c.

Take Gamma_desc to be the joint original description region containing
Delta_0, the original Parameter Desc(A_f), and these new Application Desc
records. Retain the Parameter's actual Delta_f through its original inclusion
at sigma_f; the new records use their declared Delta_0 inclusions at that
same node. Thus Gamma_desc has the original Parameter dependencies and both
new declaration dependency closures. A reference to an original static
dependency denotes the same original binder in all these inclusions; it is
not an independent copied witness. These descriptions do not gain an A_f
dependency merely because A_f is visible in that region. No
original dependency is reordered or removed. This constructs the requested
joint pre-challenge telescope. The four Function demand coordinates are the
existing argument value Int, argument effect empty, invocation effect E_i and
result value A_c, with their complete J_a/R_i interfaces. The separate whole
Application output uses E_c and the same A_c. Their free operands are
descriptive/static fields in this region; actual EventFields remain bound
inside the interface schemas.

For each original body event e, let i_e be the ancestor-context weakening
from Gamma_desc at sigma_f into the original Event(e,parent,Delta_e)
telescope and its post-Force/rebind extension. This is the existing lexical
binder inclusion: it fixes every ancestor descriptor/static field and adds
that event's original challenge, receipt, Force/rebind and runtime fields.
It creates no body binding on a Request/divergence branch. Let rho_e denote
substitution along i_e on the retained description syntax. The owner emits
exactly

```
J_a[e] = J_a[rho_e]    R_i[e] = R_i[rho_e]
IF_c[e] = IF_c[rho_e]  F_c[e] = F_c[rho_e].
```

No per-event Desc introduction is performed on this new path. Substitution
of the displayed constructor terms proves these equations; every embedded
IF reference substitutes its complete original parameter map, and every
event/future binder uses the original lifted substitution. Identity and
composition are inherited from those same original actions. Thus all body
events use restrictions of one F_c. F_c's definition has no free A_f
reference, so substituting for A_f cannot recursively insert F_c into itself.
This establishes the scope/independence law for the amended source owner.
It does not choose a satisfying assignment at A_f's original dependency
telescope or prove an inhabited complete demand. The result-value coordinate
and native Function4 result port are addressed by the constructor calculation
below; complete arm-output discharge and the parent theorem remain open.

### 6.4 Shared result coordinate and the native Function4 constructor

Ordinary Application has one result type: if the callee has type `Int -> B`,
the Application expression has type `B`. The imported Simple-sub rule already
uses this same `B` in T-App. The source owner above therefore introduces one
value description `A_c` and uses it in both positions:

```text
callee demand result       = A_c
whole Application result  = A_c
```

This is a shared constructor field, not an equality obligation added after
generation and not a choice of solved endpoint. Complete effect roles remain
distinct:

```text
callee invocation effect  = E_i
whole Application effect = E_c
```

The current native constructor has exactly the corresponding shape. At
`shadow_apply.rs:1345-1366`, the Apply recipe obtains `result` from the
Application's value component, allocates a fresh invocation-effect row, and
constructs `NegativeFunction(argument,argument_effect,invocation_effect,
result)`. `candidate_call.rs:332-340` checks that the negative Function's
result child is the same term retained as the Apply result. The same owner
retains the distinct application-effect endpoint, and emits
`callee_effect <= application_effect` and
`invocation_effect <= application_effect` at `shadow_apply.rs:1426-1443`.

The result and effect coordinates line up directly. The literal's value and
evaluation-effect endpoints are flexible native rows, so the two argument
coordinates line up by the literal's already generated Simple-sub bounds:

```text
Int <= v_a <= Int
BottomEffect <= e_a <= EmptyEffect
E_i -> native fresh invocation-effect row
A_c -> native Application result component
E_c -> native Application effect component
```

Here `v_a,e_a` are the actual argument endpoints retained in the negative
Function4. `candidate_source.rs:336-349` emits the displayed value/effect
bounds for the actual integer child. The four Function subtyping children use
contravariance for argument value/effect and covariance for invocation
effect/result. Therefore
the literal bounds give both ordinary inclusions between the source-projected
demand `Function4(Int,EmptyEffect,E_i,A_c)` and the actual native demand
`Function4(v_a,e_a,E_i,A_c)`:

```text
Function4(Int,EmptyEffect,E_i,A_c) <: Function4(v_a,e_a,E_i,A_c)
  uses v_a <= Int and e_a <= EmptyEffect
Function4(v_a,e_a,E_i,A_c) <: Function4(Int,EmptyEffect,E_i,A_c)
  uses Int <= v_a and EmptyEffect <= e_a
```

These are existing literal constraints, not a selected solution assigning
`v_a := Int` or `e_a := EmptyEffect`. The complete `J_a` carrier and its open
challenge interface remain intact; the calculation concerns only the
ordinary coordinate projection.

The Function/Function consumer at `lib.rs:12493-12520` then emits the four
correlated children from the same positive/negative pair. In particular its
result child ends at the native Apply result component, which is the shared
source `A_c` by this owner equation. This is the direct use of the ordinary
Simple-sub Application result sharing plus its existing literal bounds; it
does not rederive T-App, pick a satisfying assignment, or infer a complete
inclusion from endpoint equality.

This calculation closes the source result-port alias for the selected new
owner and the current native Apply term. It does not prove that every
independently declared Call arm's complete result/effect/future contract is
represented by the two native effect edges, that `e_out` is satisfied, or
that Function4 erasure preserves the complete residual. Those are separate
remaining parts of the source/native gate.

### 6.5 Apply the existing complete-bound theorem at the generated edge

For each original body event `e`, the owner rule emits the same-value
constraint at its actual source map:

```text
e_f[e] : VIncl(A_f[rho_e],F_c[rho_e];xi_e).
```

Instantiate the reviewed complete-bound theorem BOUND, section 5 of
[`2026-10-10-simple-sub-complete-bound-accumulation.md`](2026-10-10-simple-sub-complete-bound-accumulation.md),
at these exact endpoint references and comparison context. BOUND's input is
the emitted edge itself; it does not require a typed Call certificate, a
selected provider, satisfiability, or `e_out`. Its conclusion is

```text
F_c[rho_e] in Upper_{sigma_e}(A_f[rho_e]).
```

For every original scope-respecting assignment `eta` and full residual
witness `w`, BOUND attaches its computed view and its erase map returns that
same `w`; both composites are identity by record projection/construction.
Thus this source Application constructor directly supplies the complete
Simple-sub upper-bound occurrence, with the original dependent residual
retained. This is an application of the existing theorem, not a second proof
of ordinary `lambda f.f 1` typing.

The result closes the source-edge-to-complete-upper-bound step. BOUND does not
identify a complete Function descriptor with a native Function4 term, prove
the open residual inhabited, discharge `e_out`, or account for every
independent arm in native output constraints.

An independent proof review checked this instantiation against BOUND §§3–5,
Source Generalize §3.3, and the original `VIncl` scope/action definition at
SHA-256 `51747e5b5d3679b9a473a47162bf4946b9ff9f6e9475e4334089f0b3b676c99b`.
It confirmed that `e_f[e]` is the original scoped proof slot, that BOUND stores
the same `F_c[rho_e]` in the original comparison context, and that the full
residual is preserved fiberwise. This review covers §6.5 only; it does not
review the shared-result-port amendment or establish native Function4
correspondence.

## 7. Actual derivation of the structural `f 1` branch

All the following proof construction is uniform in the original typed body
environment and the generated complete inclusion witness.

1. The existing source-owned Strict Lambda rule introduces `I_f` before its
   challenges. For every independently admitted outer challenge, its proved
   same-frame entry law gives the actual post-Force/rebind binding
   `ValueBind(Empty,d_f,r_f,A_f,entry_origin)` on Return. On Request/divergence
   it retains the pending suffix and manufactures no body binding.
2. Resolve and Name select that SAME binding. Result returns the same `v_f`,
   actual provider and current world. From its A_f membership and the actual
   generated same-value inclusion witness derive membership in F_c. There is
   no instantiation of the lambda-bound formal.
3. Literal at a constructs the original Int primitive value k (k=1 here).
   Result forms `Return(k)` at its actual port. Its complete local typing law is the
   primitive/Return law. Reify at the Application's original argument port
   forms `kappa_a = Delay(Return(k))`. Inert formation has empty lexical
   capture; designated execution is proved by the same closed Literal/Return
   derivation at EVERY independently compatible future demand. The proof is
   a family under those demands, not a selected successful execution.
4. Keep the full `J_a` as well as that actual section. The printed
   `Comp(empty,Int)` does not identify J_a with the single returning carrier:
   all carriers admitted by its complete contract stay in the open slot.
   For an arbitrary h in the open frame, construct the checked challenge
   from h's OWN carrier-admission field, original punctured context and source
   port maps. Step 3 constructs that field for the source diagonal; it is not
   substituted for another carrier's field. This construction uses neither
   acceptance by v_f nor its output safety.
5. Eliminate F_c membership. For EVERY genuine `Act(v_f,U,r)` and each such
   independent challenge, obtain actual acceptance and the full `R_i`
   observation proof. Keep U, its entry/role, current world, receipt, response,
   raw continuation and output-dependent future fields from THAT elimination.
6. Apply the existing Bind constructor to the Name/Result proof and this
   receiver proof. On the actual Name Return branch it binds that same tuple
   and uses the receiver proof. Before that Return it retains the original
   callee pending prefix/suffix. Within receiver execution it retains the
   receiver's pending suffix. No argument receipt is replayed and no latent
   result is forced by inspecting its type. This constructs `type_s` at D_s.

For finite prefixes the proof follows the actual Bind cases. For future
validity, fix an arbitrary compatible original extension and apply the same
hereditary Name/carrier proof and Function elimination at that extension.
This retains `forall history; ...` under its original binders, rather than
choosing a history during elaboration. Nothing here assumes that f is a
source-known closure, total, pure, or Value-entry.

## 8. Complete-Call typing theorem and proof

**Conditional constructor theorem.** Fix a source occurrence in the selected
Name/Integer domain, its original binder tree and declarations, and one lawful
joint assignment at those scopes. Given its actual typed body environment,
the local constructor laws of sections 2-3, and its generated same-value
inclusion witness `A_f <: F_c`, for every independently valid original frame h,
observation o and full witness q of `Call_c(h,o)`, construct
`Mem(D_call,h,o)`. Neither `C0(c)` nor `TypedCallCert(c)` is an input. This
statement quantifies over satisfying assignments; it does not assert that
the open generated constraints have such an assignment.

Define its proof by constructor elimination:

```
type_call(Struct(s)) = inj_s(type_s(s))
type_call(Z(j,delta,p,z)) = inj_j(delta,p,local_type_j(p,z))
type_call(W(j,q,delta,p,w)) =
    inj_j(delta,p,local_type_j(p,w))
type_call(Arm(j,delta,q_1,...,q_n,p,z)) =
    inj_j(delta,inputs_j(delta,raw(q_1),...,raw(q_n)),p,
          local_type_j(p,z))
```

Here the shorter Z/W injections suppress their original inputs coordinate.
`inputs_j` is the declaration's actual predecessor/operand substitution, not
a newly selected tuple. For each predecessor reference q_i, retain its exact
raw observation, dependent scope map and existing typed input/guard evidence
in p. Where the original input is a typed Call-result reference, recursively
construct `type_call(q_i)` at q_i's own original telescope and use precisely
the declaration's existing input checking map retained in p. A union
membership proof alone does not supply a different primitive's operand type
or its guard. Any other required typed input is the original evidence already
retained at that reference; it is not manufactured by this recursion. Thus
each required input is either retained or constructed by the actual declared
consumer at its own scope, before applying the original `local_type_j(p,z)`.
This handles any declared finite predecessor list, including zero references
and non-iterating arms, with no strengthened guard or added closure case.

In the W case, `p,w` retain the original predecessor `raw(q)` and its
required original typed guard/input evidence. They do not substitute the
structural branch's provider/future certificate for the new output's one.
Any original additional premises of the clause are eliminated at their own
positions. Positive predecessor occurrences preserve the original derivation
by structural recursion; no universal future quantifier is moved into the
positive-closure operator. Primitive future/domain laws remain the actual
local laws under their original event binders.

Every right-hand side is an introduction of the existing complete union;
every input proof is either constructed in section 7 or supplied by that
independent primitive's own local law. This proves the theorem for all
constructors, including every declared Arm, unanchored Z and arbitrarily
long finite W chains.
It never chooses an arm to establish a universal result.

### 8.1 Exact Kernel image at the new Application owner

Application_N §5 already forms `Q_N(c)` as a reference to its actual complete
Call Kernel, with the original source operands and an open whole-carrier
inlet. Make that same reference the single owner of the complete Call family,
rather than keeping a second, merely similarly shaped relation:

```text
delta_K                  actual independently supplied complete Kernel
mu_c                     its original complete scoped use substitution
K_c                      delta_K[mu_c]
Q_N(c)                   Ref(delta_K,mu_c)
Call_c(h,o;q)            Witness(K_c,h,o;q)
Image_c                  OutputImage(Q_N(c))
Mem(Image_c,h,o;q)       Eval(Q_N(c),h,o;q)
```

`OutputImage` is the existing evidence-retaining constructor image at the full
original output interface. It keeps the full operation witness `q` together
with its observation and dependent fields; it is not an existential quotient
that erases arm evidence or a projection to value/effect support. The exact
left operand checked by `e_out` is this `Image_c` at the same `mu_c`. The
`e_f/e_a` entries are the original checking evidence at their existing
positions, not additional output guards on independently declared arms.

This is a constructor definition for the new source use, not selection of a
replacement Kernel. The structural `Struct` witness is the original C-Call
Bind followed by ExecuteCallable at the actual returned provider and current
world. Each generic `Arm(j,delta,q_1,...,q_n,p,z)` uses the exact declaration,
ordered telescope, predecessor-reference list, licenses, guards and
substitution from `delta_K`; `Z` and `W` are its zero- and one-predecessor
cases. Non-iterating arms stay single-use and W closure is retained exactly
where the original declaration provides it. Pending prefixes/suffixes and
future fields remain the original dependent Bind and arm witnesses.

For every original joint assignment and complete open frame `h`, the
reference beta law gives the full-fiber map

```text
theta_c(q) = fold_Ref(q)
theta_c(q) : Mem(Image_c,h,o)
unfold_Ref(theta_c(q)) = q
```

and the reverse composite is identity. With transparent reference notation,
`theta_c(q)=q`. This preserves the particular admitted carrier filling (so
`Delay_a` remains only its source diagonal), actual provider/world, request
and response, raw continuation, every original arm witness and its future
interface under the original binders. No satisfying assignment, C0, output
typing law or successful Call is assumed to form this map.

Therefore `e_out` can now be applied directly to `theta_c(q)` for every
`q : Call_c(h,o)`, yielding `Mem(Comp(E_c,A_c),h,o)` for the same complete
observation and assignment. This proves the outer result-readout part of the
source Call construction. It does not prove `e_out` itself, native
Function4 correspondence, satisfiability, or the original parent theorem.
An independently fixed foreign Call/Image root still requires its own
complete constructor identification; this definition does not cast to one.

**Closing the actual Lambda, conditional on that assignment.** The proof is
uniform for every body binding
obtained by the already selected Strict entry rule. Use it as that rule's
body premise, with `R_L` equal to this complete body rule program at its
original event telescope. The resulting source closure has
`Strict(I_f, formal:A_f, R_L, IF_L)`, retaining the outer entry effects as well
as the body Call. This is a complete source derivation under the ordinary
generated local bound `A_f <: F_c`, not just a diagram for a hypothetical Call.
No proof for an outer Request/divergence branch creates a body binding; the
existing entry rule instead keeps its original pending body suffix.

**Unestablished satisfying assignment after the owner amendments.** The
assignment `A_f := F_c` and the claimed nonempty identity-closure instance are
withdrawn. Reflexive inclusion is lawful only after both sides are proved to
be the same descriptor at the same scope; it cannot solve a dependency/scope
obligation by itself. Before the section 6.3 owner amendment, the selected
constructors established only the following:

- Source Generalize section 3.3 places
  `Desc(C,d_f,ValueEndpoint,sigma_f,Delta_f):A_f` before the Lambda challenge.
  It permits a body inference declaration at its owning invocation telescope.
  The source-owned Lambda section 4.1 likewise places `A_f,I_f` before
  challenges and `R_L` at the post-Force/rebind telescope.
- The earlier section 6.1 formed `J_a,B_i,E_i,R_i,IF_c` at c's original description scope,
  without selecting actual output fields. Application_N section 4, Demand-N,
  places its demand/result/effect descriptions in `Delta_c`; it supplies no
  equality with `sigma_f` or lifting map to that earlier scope. Its section 5
  expressly separates formation from inhabitance.
- IF-Insert/IF-Use are formed before observations but retain every original
  dependent substitution. The complete Call frame in
  [source-interface construction](2026-10-08-call-source-interface-construction.md)
  section 4 includes `IF(CalleeRef_e)` and its whole interface;
  the selected Name interface references `A_f`. Static formation alone thus
  does not establish that all descriptive dependencies of `IF_c` exclude
  `A_f`, or that its event-indexed fields occur only bound inside the demand.

The prior section 6.3 owner amendment supplied the missing source formation
and IF-Use substitution: one pre-challenge `Gamma_desc`, a demand prefix
independent of `A_f`, a dependent Call suffix retaining the caller operands,
and one `F_c` restricted across all body events. The current amendment changes
the result port as well: it reuses `A_c` in the Function demand and complete
Application output, then matches that port to the actual native Apply result
term by §6.4's owner equations. The effects remain separate as `E_i` and
`E_c`. This source/code result-port calculation is new Draft work pending
independent review; it does not construct a satisfying assignment or prove
that native Function4 preserves the complete residual.

The assignment `A_f := F_c` is still not asserted. Having all Desc records in
a joint description region does not permit the earlier `A_f` assignment to
refer to later endpoint declarations outside its original dependency
telescope. Reusing `A_c` resolves the Application result coordinate but does
not establish a joint satisfying assignment or inhabitance of the complete
demand. Those still have to respect the original scopes and independent
formation obligations.

The current native source owner allocates Parameter/expression endpoints once
in `candidate_source.rs` and traverses Lambda/body at the same numerical
level. `shadow_apply.rs` and `candidate_call.rs` establish the same Apply
result term in the native Function4 and expression output; §6.4 now maps the
shared source `A_c` port there. This does not establish complete interface
formation, every independent arm's output projection, a satisfying
assignment, or demand inhabitance. Source satisfiability and the parent
source/native gate remain OPEN; no caller is restricted to identity or
purity.

**Evidence retention.** Erasing the newly added type/placement witnesses
recovers the same structural witness or original j,delta,p,z/w and every
actual predecessor reference q_i. This is a literal projection, not equality
after observing
only the returned value or effect support. Induction preserves every
original member of the declared constructor family. No statement about a
different unspecified historical predicate is inferred from this projection.

**Dependent actions.** Rename/restrict every original operand and telescope
once. Each constructor above commutes with this operation by the existing
local action laws and union constructors. In particular an EventField remains
under its Event; the older Parameter description is not freshened for an
inner use. This supplies the local Call rule's source transport, not the
entire compiler Generalize or public-principality theorem.

**Non-circularity.** D_call is assembled from independently interpreted
contracts before observing Call_c. It is not defined as the set of this
program's successful runs. The implication from Call_c to D_call was proved,
so retaining the independent descriptor conjunct does not silently filter
any branch. Primitive laws cannot contain the missing whole-Call theorem.

## 9. One implementable elaboration, with existing owners

The source generation result is an OPEN constrained rule program and a
constructor derivation schema. Given genuine witnesses for its generated
constraints and its actual typed environment, the schema constructs the
complete typing proof above. Generating the schema is not solving its
constraints and must not return a closed `TypedCall` certificate.

For the selected new Name/Integer seam, use the existing source traversal,
with all old constructor cases retained:

```
Parameter: retain existing registration and its full source interface
Name:      reference the same registered endpoint and source binding
Literal:   apply the actual primitive/Result construction
Apply:
  Reify the actual argument under its source argument port
  form FunctionDemand and emit the ordinary complete callee bound
  form Bind/receiver source spine and instantiate ALL declared arm refs
  construct D_call by scoped full-contract union
  emit Gen-Call-Syntax and IF-Insert/IF-Use at the same source occurrence
  retain the complete rule program beside its existing native recipe
Lambda:    use this body root in the already selected Strict construction
```

The interfaces/constructor applications are a finite source/constraint graph,
with references to complete primitive families. No model search, per-carrier
enumeration, fabricated proof token, empty default contract, or duplicate
provider representation is necessary.

Ownership at the baseline:

- `crates/yu-hir/src/module/local_source.rs`: actual Lambda/Parameter/Apply
  nodes, resolution, argument identity and lexical scopes.
- `crates/yu-solver/src/candidate_source.rs`: Parameter registration, source
  traversal, actual literal/Name bounds, LambdaRecipe and ApplySourceInput.
- `crates/yu-solver/src/shadow_apply.rs`: the existing native Apply demand and
  the distinct argument/callee/invocation/application effect positions.
- `crates/yu-solver/src/candidate_call.rs`: borrow the actual source/native
  incidence. Its current PendingCallConstruction is not promoted to evidence.

When the source result is checked against a chosen ordinary result/effect
presentation, retain the exact complete root. Union elimination reduces a
check on D_call to checks at the actual constituent contracts and their
original source positions. Successful checks must use the existing local
checking constructors. Merely printing the union's value/effect projection
is not a proof of those checks or of latent-interface compatibility.

## 10. Exact remaining compiler obligations; not missing Call definitions

The construction above does not establish that the CURRENT native Function4
implements the new complete source rule. In particular:

1. Construct and retain the complete primitive/source interface references at
   their real owners, rather than deriving them from endpoint equality.
   The existing source handles suffice for locations, not for semantic truth.
2. Extend the §6.4 result-port equation to a complete interpretation of the
   native demand/effect endpoints and original Call root at their original
   scopes. The ordinary result coordinate is now shared by construction; the
   full interface and both source/generated directions for one joint
   assignment remain open.
3. Check every independently declared arm in that projection. Current Apply
   emission adds callee and invocation effects to the application effect; it
   does not by itself show that every separate arm's result/effect/future
   constraints are represented. An arm already covered by an inherited hard
   envelope needs its genuine local inclusion; an independent contribution
   must not be silently dropped. Whether more native constraints are needed
   is an implementation/representation question, not a Call-typing axiom.
4. Preserve this complete rule program at source Generalize, replay/extrusion
   and eventual native discharge. The existing BOUND theorem can be applied
   to the generated complete callee edge; §6.5 now performs that application
   at the original occurrence and preserves its full residual fiber.
   Function4 erasure alone is not its converse and does not prove public
   principality.

The relevant source typing theorem is under the ordinary generated local
constraints, not under a new premise called "the whole Call is safe". No
claim of native satisfiability, production acceptance, all-source completeness
or public principal output is made by forming this open program.

## 11. Review and integration status

This file is the constructive mathematical work, not a completed parent
theorem. The producer's checks include: no whole-Call proof input; no invented
argument Name; no actual-provider selection during description formation;
no source-diagonal restriction; no borrowed future certificate for another
arm; no post-hoc structural-output guard; no closed proof from open constraints.

The initial independent compiler_referee/spec_auditor review identified the
generic Arm proof case, an overbroad DataUse domain, and an unestablished
same-scope satisfiability witness. One batched repair added the actual Arm
elimination, confined the new case to resolved unannotated Value-formal
Name/Integer, and withdrew the witness while exposing its exact scope law. A
fresh compiler_referee and spec_auditor delta review passed those repairs.
This independently reviewed conditional constructor theorem does not establish
source satisfiability or the parent source/native theorem, which remains OPEN.
The prior section 6.3 owner amendment and corresponding section 8 derivation
were independently reviewed by `compiler_referee` and `spec_auditor` at frozen
SHA-256 `1f72ddb332ace004f9d7ac2a5ee935e7267238591bcdc82b801bf535b51c9ebe`;
both passed with no findings. That review predates the shared-result-port
amendment in §§6.1, 6.3, 6.4, 8 and 10. The new amendment uses the ordinary
Application result-sharing rule and the current native same-term constructor
equation; it is unreviewed. A separate scoped review passed §6.5 as recorded
above, but that direct theorem application does not prove the missing
complete-demand-to-native-Function4 map. It closes no parent or production
gate. No
production code, test expectation, public type language or cutover status
changed. Shared task/laboratory synchronization is owned by primary
integration.
