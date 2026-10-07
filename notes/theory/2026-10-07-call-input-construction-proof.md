# Constructing the captured Call input from its source derivation

Status: independently compiler-referee-reviewed constructor and fragment theorems; no semantic adoption or implementation authority
Baseline: `370bb4634d0b5eb413c01bb984b995f74a743f59`
Branch: `research/simple-sub-intrusion`
Exclusive producer lease: this file only
Claim classes: D (retained source evidence) and A/B (its semantic interpretation)

**Review and checkpoint disposition.** The initial independent compiler-referee
found an incomplete static grammar, a missing same-branch source-membership
step, an omitted inert-carrier conjunct, and historical/live-state ambiguity.
A fresh researcher repaired all four in one batch. A fresh compiler-referee
delta review passed without remaining blocking, major or minor findings on
frozen SHA-256 `bb0eba03945024cf5de16d01e0c55e83eccebe77c29396bedcdaa128a75a322f`.
The primary accepted that verdict. The reviewed §§1–9 remain verbatim below;
their repair-pending language is the producer's historical freeze state.
All 24 recorded dependency hashes match the stated baseline and integration
HEAD `465c2af15dfb8ae5f603fea4dc4533e99f9b0c5a`. Theorem S is complete on its
stated source-derivation envelope; Lemma N/Theorem I are complete in the
explicitly defined fragment under its genuine semantic inputs. The reviewer
checked the repair's direct dependency cone, not production implementation or
unrelated O0/O1 mathematics. No original C0, model-realization or canonical
gate closure follows. This disjoint research checkpoint preceded the primary's
shared navigation integration, now recorded in the
[completion review](../progress/2026-10-07-source-constructor-completion-review.md#7-completed-source-inputs-and-actual-return-consequence).
That synchronization does not claim that the full compiler gate is complete.

**Later original input interpretation selected (2026-10-08).** The
[contextual membership definition](../design/2026-10-08-contextual-function-membership-definition.md)
selects the missing original immutable world, Return/carrier and same-provider
Function cases. Its [reviewed realization](2026-10-08-call-semantic-input-realization.md)
constructs the telescope from hereditary binding inputs, proves the full Name
Delay and actual CalRet membership, and obtains actual-U argument acceptance
without this note's additional raw ViewInlet premise. The original independent
context and semantic input requirements remain. This does not adopt §5.4 as
a mandatory production rule or supply full C0, arbitrary descriptor/model
realization, newly constructed closure introduction or foreign-kernel equality.

## 1. Result and precise boundary

This packet constructs a **typed source input object**, including its Name,
Return, Delay, checked-view and ordered entry interfaces, from the actual
source derivation. It proves an induction theorem for those constructors and
an exact actual-return instantiation theorem. There is no supplied `RunCert`,
`CI-Operands`, `CI-ArgFrame`, completed invocation inclusion or `TypedCallCert`
in the constructor premises. A Delay stores the argument's constructed code
derivation. Lookup is elimination of a retained binder/capture derivation.
The argument derivation is instantiated at the actual returned world, and the
actual provider is selected by the retained CalRet witness, rather than by the
source demand's descriptor spelling.

For a minimal independently specified semantic fragment, this packet also
proves Name/Return/Delay soundness and the actual-input consequence. The
fragment's whole-carrier criterion is independent of source construction and
allows arbitrary independently valid carriers. Its checker-to-actual-provider
rule is a **proposed uniform introduction clause**, not an already adopted
meaning of the original Function membership. The clause exposes a contract's
inlet action on a retained provider witness. It does not assume completed
invocation membership. This is a precise semantic clause requiring justified realization and any
applicable adoption, whereas the source constructors and their
substitution/erasure proofs are
ordinary definitional formalization of retained derivations.

Consequently the maximal unconditional result is construction of the complete
static Name/Return/Delay/entry input interface. The actual semantic consequence
holds in the defined fragment, and in the old interpretation if that fragment
has an evidence-preserving realization there. No original C0 closure, old-model
existence, inhabitance, O1, contribution realization or production conformance
is claimed. The advance over the previous C1–C7 packet is a source-directed
constructor induction and explicit delayed-code proof, followed by an
actual-witness elimination; it is not another list of laws to assume.

## 2. Governing semantics and why a fragment is necessary

The [nested-block Authority](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3 fixes exactly

```text
lambda(f, bind(step,
  result(lambda(x, call(result(name f), result(name x)))),
  result(name step)))
```

The [inferred call-view Authority](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 retains one shared dependent demand, actual role/entry separation and
Q-independent admission. Its §5 explicitly leaves exact construction and
semantic rules open. The [charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
§§16–18,21 fixes receipt before entry, inert whole-argument reification,
one-layer consumption and Value versus retained parameter roles. The
[typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§§3,6,9 supplies the conditional complete invocation expansion, including an
operation's designated consumer after native return. It remains Draft.
These clauses govern the execution used below; this packet changes none.

The [source generation construction](../progress/2026-10-06-source-call-generation-construction.md)
§§4.2,5 supplies the actual Gen-Call-0 demand record and the semantic argument
and same-value checking obligations. Its full `G_call` also contains completed
image inclusion and supplied decoration. **Only its independent operand
conjuncts are used here**; `CIncl(ExecuteCallableImage,... )` and
`TypedCallCert_Dec` are not used to prove a Call input. O0 is already adopted
by [the narrow definition](../design/2026-10-07-original-call-formation-definition.md)
and proved by [O0-selected](2026-10-07-adopted-call-formation-o0.md); no O0
reconstruction occurs here.

The fixed-cut, operand-context, closure, computation-entry, pending-closure,
local-law and round-4 notes named in the dependency table establish the
boundary that must be respected. In particular, C1–C7's proposed `RunCert`
was not derived; the later demand-family correction says a free event forest
is not an independently valid joint world. The actual-provider audits also
show why checking at `F_c` cannot silently become compatibility at `U`.
The [priority leaf audit](../progress/2026-10-08-successor-priority-leaf-attacks.md)
Call section requires checked membership of the **same returned value**
before an actual-inlet bridge. The construction below follows that order.

This is a localized unspecified-grammar claim: the cited documents declare
those independent descriptor/world and checking clauses open. It is not a
repository-wide absence or impossibility theorem. Defining their missing
semantic cases is legitimate proof construction, but does not prove that an
unselected old interpretation already has those cases.

## 3. A source certificate grammar with no semantic conclusion in its premises

Fix the original resolved binder graph `B`, source `X`, original scopes,
registered provider roots and `xi=(nu,K,D)`. Endpoint variables may depend on
local binders. They are never closed or freshened individually.

A lexical telescope has constructors

```text
Empty
Import(E, captured binding certificate b, source Resolve/Capture edge)
ValueBind(E, original declaration d, root r, endpoint A, entry/rebind origin)
RetainBind(E, original declaration d, root r, computation view R, receipt origin)
ResultBind(E, original declaration d, root r, A, RHS-result origin).
```

A binding certificate records its declared source interface and its original
root, not semantic value membership. Import retains exactly the imported
certificate and its dependencies. For this source it imports `f` from
`sigma_apply` into `sigma_step`; it does not replace the outer root by a local
copy. These are finite resolved graph constructors, including references to
registered roots; this packet's proof does not accept a cyclic typing proof.

Define `Name(E,u)` by induction on the actual resolution derivation: a local
case selects the declared binding; an imported case follows the retained
capture edge and recursively selects its original binding. Its result is a
dependent pair `(b, use-to-binding evidence)`. There is no rule from equality
of source IDs, endpoints or canonical type nodes.

### 3.1 Judgments, origins and inert data

Use two distinct judgments, `Data(E,d,I;q)` for an inert source descriptor
and `Code(E,c,R;q)` for computation code. `I` is `Value(A)` or
`Computation(Eff,A)` and `R=Comp(Eff,A)`. The final index q is the retained
finite derivation, not a membership witness. `T_D` and `T_C` erase to the
fixed `V` and `X` translations of typed-core §3. Every formation-origin
premise below is a constructor/registration/scope derivation in the actual
source graph, with its symbolic interface; it is never satisfaction of an
emitted constraint, value membership or a complete execution certificate.

```text
Name(E,u)=(b,edge), b.interface=I
------------------------------------------------------------- Data-Name
Data(E,name u,I; b,edge)
T_D = lookup(the same resolved binding)

Data(E,d,Value(A);q), original result node/port o_result
------------------------------------------------------------- Code-Result
Code(E,result(d),Comp(empty,A); q,o_result)
T_C = Return(T_D[d])

Data(E,d,Computation(Eff,A);q), original designated port p,
ConsumerOrigin(d,p,Comp(Eff,A),original profile,K,D,scope)
------------------------------------------------------------- Code-Consumer
Code(E,eliminate_p(d),Comp(Eff,A); q,p,ConsumerOrigin)
T_C = Execute_p(T_D[d])

Code(E,c,R;q), ReifyOrigin(o,c,r,R,scope,lexical incidences)
------------------------------------------------------------- Data-Reify
Data(E,reify(c),Value(ComputationData(R)); q,o,r)
T_D = Delay(T_C[c],the same lexical references)

Code(E,c,R;q), ReifyOrigin(o,c,r,R,scope,lexical incidences)
------------------------------------------------------------- Carrier-Delay
DelayCode(E,Delay(T_C[c],references),r,R; q,o)
T_carrier = Delay(T_C[c],the same lexical references)
```

`ReifyOrigin` uses the original registered carrier root and its exact typed
view. At Call it is the actual whole-argument reification origin generated
by that Call, not an explicit new source wrapper. Data-Reify is the explicit
inert-data introduction case when present. These rules perform no execution,
receipt or entry. Code-NameValue is exactly Data-Name followed by
Code-Result; Code-NameRetained is Data-Name followed by Code-Consumer.
A retained interface is forwarded by that designated consumer, with no pure
Return layer and no recursive forcing of its result.

### 3.2 Capture and parameter-entry constructors

`Capture(E,lambda_node,E_cap;edges)` is obtained by restricting E to the
actual resolved free-binding subgraph and importing every captured binding
along its actual Resolve/Capture edge, including all dependencies of that
binding. Its erasure is exactly the original lexical reference tuple.
No capture can be obtained from endpoint equality. Dependency order is the
original graph order; aliases are shared references, not independently
copied entries. This rule has no lifetime, receipt or authority conclusion. Explicitly:

```text
actual finite resolved free-binding/dependency graph Free(L) in E,
actual Capture/Resolve edges of L, preserving original sharing and scope,
E_cap = ImportRestriction(E,Free(L),those edges)
------------------------------------------------------------- Capture-Lambda
Capture(E,L,E_cap; those edges)
T_capture = the original lexical reference tuple restricted to Free(L)
```

ImportRestriction traverses the dependency-closed original subgraph once,
retaining the original binding certificates and alias references. An empty
Free(L) yields Empty and the empty reference tuple; an imported binding
retains the same original certificate rather than generating a new root.

Generate the ordinary parameter role from charter §21 before the body:
`x` and ordinary `x:A` select `Value(A)`; an admitted explicit outer
computation annotation selects `Computation(Eff,A)`. An annotated endpoint
requires its actual annotation derivation. An unannotated endpoint is the
one generated at its original formal, not an arbitrary new endpoint.
The following constructors produce static entry interfaces:

```text
Capture(E,L,E_cap;edges), ParameterOrigin(L,x,Value(A),r_x),
original received-carrier port r_in and designated entry view,
original receipt/rebind ports of L
------------------------------------------------------------- Entry-Value
Entry(L,Value(A),E_cap,E_body;
      Receive(r_in); Receipt_L; Force_entry(r_in);
      Rebind(r_in,r_x,A))
E_body = ValueBind(E_cap,x,r_x,A,that entry/rebind origin)

Capture(E,L,E_cap;edges), ParameterOrigin(L,x,Computation(Eff,A),r_x),
original received-carrier port r_in and declared computation view,
original receipt/retained-binding ports of L
------------------------------------------------------------- Entry-Retained
Entry(L,Computation(Eff,A),E_cap,E_body;
      Receive(r_in); Receipt_L; Retain(r_in,r_x,Comp(Eff,A)))
E_body = RetainBind(E_cap,x,r_x,Comp(Eff,A),that receipt origin)
```

Their erasures are the original `entry_P` programs in Closure: the Value
case establishes receipt, forces once and rebinds inside the same invocation;
the retained case establishes receipt and binds the same carrier. The
semicolon lists interfaces in execution order, not actions performed during
construction. Receipt ports are declared source ports, not actual receipt
witnesses. The actual activation supplies its own evidence later.

### 3.3 Lambda and sequential Bind

```text
Capture(E,L,E_cap;edges), Entry(L,P,E_cap,E_body;entry),
Code(E_body,b,R_b;q_b),
ClosureOrigin(L,r_L,P,R_b,body/result port,sigma_L)
------------------------------------------------------------- Data-Lambda
Data(E,lambda(x,b),Value(A_L);
     r_L,edges,entry,q_b,body/result port)
A_L = Fun(P,R_b) as the source body/result skeleton
T_D = Closure(entry_P; T_C[b],the same lexical references)

Code(E,c1,Comp(E1,A1);q1),
BindOrigin(B,x,c1,c2,r_x,A1,original RHS-result/rebind port),
E2 = ResultBind(E,x,r_x,A1,that actual RHS-result origin),
Code(E2,c2,Comp(E2eff,A2);q2),
BindResultOrigin(B,Comp(E_bind,A2),original ordered image ports)
------------------------------------------------------------- Code-Bind
Code(E,bind(x,c1,c2),Comp(E_bind,A2);
     q1,RHS-result/rebind port,q2,ordered suffix/result ports)
T_C = T_C[c1] >>= lambda(v,current). T_C[c2] in E[x:=v]
```

`A_L` describes the generated closure's source body/result skeleton, as in
typed-core §6. It does not equate `R_b` with the complete invocation of that
closure. The same closure certificate retains separate received carrier,
entry/rebind, body/result, declared consumer, native return delimiter and
complete invocation ports of §9. Any existing symbolic complete-call view
is retained as its own original interface, without a solved membership fact.
Constructing a lambda constructs its latent body certificate; it never runs it.

Bind retains the **actual RHS result endpoint A1**. Its second computation
uses a Value result binding even if A1 denotes a latent computation or closure.
`E_bind` is the original symbolic Bind-image endpoint, not a row union or an
assertion about observations. The stored suffix is rebind followed by the
entire c2 and the original result delimiter. Its suspended erasure is
`Request(q,C,lambda(response,C'). k1(response,C') >>= suffix)`;
the same operation/raw handle and current resumed configuration are retained.
This is a static ordered-continuation interface, not pending soundness.

### 3.4 Call, checking origins and its continuation schema

Define `Suffix_c(U)` as the finite dependent schema on the **original actual
provider interface** U: receiver/receipt; U's own selected entry; its body
and designated consumer; its native and complete invocation return ports.
For Value entry it contains Force and its result rebind before the body;
for retained entry it contains retained binding before the body. For an
operation it retains native Return of MakeRequestThunk, the native return
delimiter, then the declaration-derived consumer. These are tags and ports
from typed-core §§3,9 and the original producer declaration, not newly
licensed producers. Unknown U is a parameter of the schema, not a solved
provider inferred from F_c. The initial suffix includes inert construction
of the whole argument followed by Suffix_c(U). Entry and later suffixes are
its remaining ordered tails; receipt is never inserted again on resume.

```text
Code(E,cf,Comp(Ef,A_f);qf), Code(E,ca,Comp(Ea,A_a);qa),
actual Application/Gen-Call-0 origin at c with dependent F_c,R_f,
ReifyOrigin(o_arg,ca,r_arg,Comp(Ea,A_a),original scope/incidences of Call c),
t_arg = Carrier-Delay(qa,o_arg),
original symbolic Call result Comp(E_c,A_c) and result port o_c,
actual emitted VIncl-origin(A_f,F_c),
actual emitted WholeArgCompatible-origin(J_a,CarrierContract(F_c))
------------------------------------------------------------- Code-Call
Code(E,call(cf,ca),Comp(E_c,A_c);
     qf,qa,t_arg,Check_c,o_c,initial/entry/body/consumer suffix ports)
T_C = T_C[cf] >>= lambda f.
        let t = Delay(T_C[ca],the same lexical references) in
        ExecuteCallable(f,t)
```

A source operand-check record is constructed by bundling these premises:

```text
Check_c = (e_c,qf,qa,t_arg,F_c,R_f,
           VIncl-origin(A_f,F_c),
           WholeArgCompatible-origin(J_a,CarrierContract(F_c)),
           Comp(E_c,A_c),o_c,Suffix_c(U),
           original resolved roots/scopes and all operand incidences).
```

`Comp(E_c,A_c)` remains the **original complete Call-result interface**,
including callee prefix and actual entry/consumer ports; it is not identified
with closure body effect. Neither Code-Call nor Check_c includes result
inclusion truth, a satisfying assignment, receipt authority, actual-U inlet
acceptance, `RunCert`, `CI-Operands` or `TypedCallCert_Dec`. The Application
origin retains its existing emission inventory, including any separate
result obligation, but only operand origins are projected into Check_c.
An origin is an actual emitted derivation, never its semantic truth.
Bare Gen-Call-0 lacks the additional Application origins: with only that
inventory the Name/code constituents are constructible and Check_c is not
manufactured. There is no claim of completed semantic Call typing in §3.

## 4. Induction and erasure theorem

**Theorem S (source input construction).** For every finite acyclic resolved
source derivation built from the §3 Name, Result, Lambda, Reify, Bind, Call
and designated one-layer consumer constructors, construct its telescope,
data or code certificate at its actual source judgment sort, delayed-code
objects and Call-input records in source order. For every actual emitted Call-check
record, construct Check_c at precisely its original fiber. No satisfying
assignment or execution witness is needed.

**Proof.** Use simultaneous induction on the finite resolved data/code
source derivation and telescope resolution proofs. Data-Name selects the
retained interface by a local binding or an actual capture edge; induction
on that edge sequence terminates at the original binding. Code-Result takes
its data induction result and forms Return at the same result port.
Code-Consumer takes its data induction result and its already designated
port; these two cases are disjoint by the outer source interface.
Data-Reify and Carrier-Delay store the code induction result and actual
registered reify origin without executing it.

For Data-Lambda, restrict the outer telescope by Capture, generate the
source-selected Entry-Value or Entry-Retained, then apply induction to the
body under that extended telescope. ClosureOrigin supplies the original
body/result port, so the conclusion is exactly its inert data interface.
For Code-Bind, first construct q1, extend with ResultBind at q1's actual A1,
then construct q2. BindResultOrigin retains the existing symbolic result
interface and ordered suffix; no solved effect equation is needed.
For Code-Call, construct qf and qa, use the Call's own whole-argument reify
origin to form t_arg, and bundle the actual Application operand origins,
original complete result interface and dependent suffix schema. Those
premises are source constructor records, not semantic conclusions.
These are all constructors of the stated envelope; registered recursive
references can occur as roots but a cyclic derivation is not accepted by
this finite induction. No satisfying assignment or execution occurs. QED.

**Exact erasure.** Every rule displays its erasure. Simultaneous induction
substitutes the children's erasures into its displayed expression: Data-Name
becomes the same lookup, Code-Result the same Return, Code-Consumer the same
one-layer Execute_p, Lambda the same Closure and entry_P, Bind the same
ordered >>=, and Call the same callee >>= followed by whole Delay and
ExecuteCallable. Capture and telescope extensions erase to the original
lexical references, parameter/rebind environment and source binders. The
suffix schema erases to that producer's original invocation expansion,
including operation native return before the declared consumer. Forgetting
checking/result origins erases no actual constraint or instruction; they
were a retained account of the existing source generation. Thus erasure is
exact typed-core §3 code, with no evaluator, role, protection, consumer,
boundary or binder change. This is evidence representation, not
conservativity of future active admission predicates using these certificates.

**Whole-substitution.** Let theta be one legal sorted substitution on the
whole original binder/source graph, preserving fixed imports and incidences.
Apply it to every certificate index and every constraint origin once. Then

```text
theta(Name(E,u)) = Name(theta(E),theta(u))
theta(Data(E,d,I)) = Data(theta(E),theta(d),theta(I))
theta(Capture(E,L,E_cap)) = Capture(theta(E),theta(L),theta(E_cap))
theta(Entry(L,P,E_cap,E_body)) = Entry(theta(L),theta(P),theta(E_cap),theta(E_body))
theta(Code(E,c,R)) = Code(theta(E),theta(c),theta(R))
theta(DelayCode(E,t,r,R)) = DelayCode(theta(E),theta(t),theta(r),theta(R))
theta(Check_c) = Check_(theta(c)).
```

Proof is the same structural induction. The imported case transports its
original root and capture edge together. Role tags, consumer selection and
continuation order are fixed constructor tags, so an endpoint substitution
to a latent value or an empty effect does not retag them. Noninjective
endpoint substitution gives no equation between distinct source uses or
provider roots. Reflection is claimed only for injective renaming on its
image. This is a syntactic theorem; arbitrary semantic substitution still
requires the original interpretation's own lawful substitution action.

## 5. Minimal independent semantic fragment

The following specifies the meanings needed to interpret the preceding
constructors. It is a proposed fragment, explicitly unadopted where it
selects previously unspecified original predicates.

### 5.1 Joint worlds and persistent lexical values

An event index is `(kappa,eta0,h)`, where kappa is the entire original static
fiber, eta0 interprets original coordinates once, and h is an arbitrary
independently admitted finite demand/development history. Its current
configuration `C_h` is the actual configuration carried by that history.
Histories include Initial, Response, raw Resume and FutureUse from the
independent domain. They are not restricted to executions of this source.
Two indices sharing a prefix retain the same original assignment/evidence.
Fixing eta0 fixes creation/declaration coordinates, not the live configuration.

A **valid interpreted telescope** is one dependent family over that domain:
at each event with live configuration C_h and its actual joint witness w_h,
each Value binding is assigned the same retained value/provider/root and an
ordinary `ValueMem_A(v_b,r_b,C_h,w_h)` certificate at every compatible
demand; each retained binding is assigned the same whole carrier and its ordinary carrier
certificate; the family retains the common joint world and all alias/capture
incidences. This is the ordinary persistent lexical-value requirement written
as a telescope, not a product of independently chosen per-port values.
A world validity certificate includes this family when such captures exist,
and retains the interpreted original registration, typed-view, capture,
scope and authority evidence at their original incidences. No new license
or capture grant is created by a telescope entry.
It can be empty or uninhabited; no realization/existence is inferred here.

This persistent interpretation is **a semantic requirement**, stronger than
mere source capture identity. It is not derived from constant source IDs.
Once it is supplied by an independently valid admitted world, interpreting
Import is restriction/reindexing of the same family and interpreting Name is
its binding projection. Neither operation asks for a new witness. It also
covers latent callable/computation values without executing them.

### 5.2 Return observations

The fragment retains the fixed translation's ordinary lexical lookup and
pure Return operational cases. At an event e with environment references
rho_e, define lookup by its resolved edge proof: a local edge to b yields
rho_e(b); an imported edge follows its original capture reference and the
same binding projection. Evaluating `Return(lookup(edge,rho_e))` yields
`Return(rho_e(b),r_b,C_h,w_h)` at its original result port. Lookup and Return
change neither the live configuration nor the joint witness and preserve all
original incidences. Their unfinished administrative prefixes carry those
same fields. These are operational constructor cases, separate from the
membership predicate below; lookup does not consult membership or a query.
Thus a completed branch has this form by inversion of its last lookup and
Return rules, even before its descriptor membership has been proved.

At an original result port define the pure Return case independently by

```text
ReturnMem_A(Return(v,r,C_h,w)) iff
  JointWF(C_h,w) and ValueMem_A(v,r,C_h,w)
  and the original result/provider/world incidence is retained.
```

This is a case of the proposed ordinary descriptor semantics, not a statement
that membership equals a source Return image. Non-source Return tuples can
satisfy it. ValueMem retains its own latent/future-provider obligations.
Return does not discharge or alter them. Pure effect means no executing
request by this code; it says nothing about latent future effects.

For this fragment, an unfinished zero-step or administrative Name/Return
prefix is valid exactly when its current joint world, retained environment
and original code/provider incidences are valid; it asserts no result value
yet. The empty prefix is included. Any in-progress lookup/Return/delay
administration retains those same fields without demanding a latent value.
The completed case is the Return clause above. The fragment has no Request
constructor generated by Name/Return/Delay administration. Thus prefix
validity is specified independently of the source image and the pure Name
proof covers both completed and unfinished prefixes. This says nothing about
pending prefixes of a general effectful carrier admitted at that interface.

### 5.3 Whole carriers, inert-view validity and Delay

At an event e with current `(C_h,w_h)`, define the fragment's inert predicate
independently of source-image membership:

```text
InertCarrierWF_R(t,r,C_h,w_h;eta0,xi) iff
  t is a whole inert carrier at its original registered r and typed view R;
  its original formation/license evidence is valid in this joint world;
  its lexical reference tuple is the interpreted original capture tuple;
  all root/alias/provider incidences, scopes, authority and joint dependencies
    of that typed view and those captures are retained and jointly valid;
  its creation stores references without executing represented code,
    granting receipt, adding authority, or snapshotting a store/handler state.
```

Original licensing is an independently specified part of the fragment: a
registered reify formation at `(o,r,R)` interprets to the inert constructor
at that same root/view with its existing scope, capture and authority
incidences, when those original incidences are valid in the joint world.
It licenses **that original formation only**; it supplies no execution
membership, fresh original root, new authority or compatible inlet at a
different view. Independently licensed Option 2 or other carrier formations
can also satisfy the predicate. This predicate does not require Delay,
source code, a successful comparison or a terminating observation.

**Inert Delay introduction.** Given Carrier-Delay(q,o), an independently
valid interpreted telescope at e interprets the actual reify/root origin o
at the original `(r,R)`. Set `rho_e` to its reference projection and
`t_e=Delay(T_C[q],rho_e)`. The fixed constructor is inert. The interpreted
original origin supplies its registered view/formation evidence; telescope
projection supplies the identical jointly valid references, capture and
alias incidences; its joint-world certificate supplies the unchanged scope,
authority and dependency fields. Pair these fields, without a new witness,
to obtain `InertCarrierWF_R(t_e,r,C_h,w_h;eta0,xi)`. This is conjunction
introduction for the displayed independent predicate. It neither assumes
universal execution safety nor derives original semantic authority from a
source identifier. The original origin and its **valid interpretation**
are both necessary; a bare fresh root or endpoint equality cannot introduce
this case. Reindexing to later compatible events uses the same interpreted
original origin and telescope family, not a new license.

For every independently licensed carrier t at original r,R define

```text
CarrierMem_R(t,r,C_h,w_h) iff
  InertCarrierWF_R(t,r,C_h,w_h;eta0,xi)
  and at every compatible independently admitted event e',
      every complete, pending or zero-step observation of designated
      one-layer Force(t) has ordinary R-membership and joint-world,
      provider/incidence preservation at that event's live configuration,
      including all admitted continuation developments.
```

The quantified domain is the independent Initial/Response/raw Resume/
FutureUse domain, not source-reachable histories, Delay(Name_x), terminating
carriers or successful comparisons. Non-source Option 2 alternatives remain
eligible under this same full criterion. No inhabitance or nonvacuity result
is inferred from a universal clause.

For Delay of Code-NameValue, Force invokes the same Name/Return code on the
retained references at the demand's **live** configuration. Projection of
§5.1 and the completed/unfinished cases of §5.2 prove the universal execution
conjunct at every such event. Inert Delay introduction proves the separate
inert conjunct. Conjunction introduction therefore proves the **full**
CarrierMem criterion; universal execution alone would not suffice. There
is no supplied RunCert: these uniform cases prove its execution consequence.
This exact code generates no Request. Arbitrary carriers at the same view
may request or diverge and retain their own prefix/continuation obligations.

For general delayed code, this inert introduction still proves only
InertCarrierWF. A further interpreter induction is required for execution
membership. This packet proves semantic Name/Return Delay soundness, not
general effectful code, handlers, recursion or State.

### 5.4 Checked callable views expose an inlet action

Let `CalRet(d_f,v,U,C1;w_f)` retain an actual completed callee branch:
the original callee-code observation `Return(v,r_f,C1,w_f)`, its same
interpreted lexical references and joint history, and actual returned U's
ordinary callable/latent/world facts. CalRet does **not** supply membership
at the source endpoint A_f. Its source index d_f locates the binding and
callee occurrence; it is not a membership proof. For the constructed Name
callee, §6 derives that missing membership by operational inversion.

A checked Function view F of that same value is proposed to include the
following independently certified inlet action, indexed by the retained
branch and its historical C1:

```text
ViewInlet(v,U,F,C1;w_f):
  for every compatible event e_h extending this retained CalRet history,
      with live configuration C_h and joint extension w_h of w_f,
  for every whole carrier t and proof a_F of
      Acc(CarrierContract(F); t,C_h,w_h,eta0,xi),
  produce a_U : Acc(CarrierContract(U); t,C_h,w_h,eta0,xi),
  retaining t,v,U, the original CalRet(C1,w_f) history,
      original roots/scopes and all incident evidence.
```

Both sides of **every** action use that event's same live C_h. C1 remains
historical CalRet information; it does not replace a later live state.
Immediate application below selects the CalRet event itself, whose live
configuration is C1. Compatibility preserves the same eta0,xi and retained
value/provider; arbitrary independent later demand histories remain allowed.

This is a contravariant whole-contract component, not complete invocation
membership or an inclusion of complete outputs. It ranges over the full
accepted inlet, including non-source carriers. It is not inferred from IDs,
printed endpoint equality, provisional Handler seeds or Q success. Source
checking may use an argument-specific action instead; the universal action
is the uniform sufficient clause proved here, not a necessity theorem.

Define same-value checking at A_f to F to carry the ordinary pointwise value
inclusion together with this provider-indexed inlet component. Independently
accepted operand assignments reflect the emitted whole-argument checking
origin into acceptance of the constructed argument at F, in the same event
family. Both conditions concern the independent input contract; neither asks
whether this invocation's output satisfies its desired descriptor.

This clause is the genuinely new semantic point. Without it, old VIncl plus
old WholeArgCompatible does not presently prove actual-U acceptance. The
original audit precisely exhibits that gap. Adding this meaning is neither
an adoption nor a proof of an old-family section. It is a minimal uniform
callable-input elimination meaning whose constructive consequence follows
below. Its realization must preserve the old independently fixed families,
not redefine them per source or per successful query.

## 6. Sound source-input theorem in the defined fragment

**Lemma N (same-branch Name/Return inversion).** Let
`nf=Code-NameValue(E,result(name f),Comp(empty,A_f);b_f,edge_f)`
be the constructed callee. Interpret E by the valid joint telescope family
of §5.1. For any retained actual CalRet branch **of this nf under that same
family**, derive `ValueMem_A_f(v,r_f,C1,w_f)` for its exact returned v, root,
configuration and world, preserving its actual U/provider evidence.

**Proof.** Expand Code-NameValue into Data-Name and Code-Result. The erased
code is `Return(lookup(edge_f,rho))`. A completed branch of this code can
only use the lexical lookup and pure Return rules of §5.2; it has no Request,
consumer or value conversion. Invert its lookup derivation along edge_f.
A local step selects b_f; an Import step restricts the same family along its
recorded capture and continues to b_f. Thus the lookup result is exactly the
family projection `rho_h1(b_f)=v`, with original root r_f. Invert the pure
Return step: the branch retains that v,r_f and the event's live configuration
C1 and joint witness w_f. It cannot substitute another value or independent
world. This equality is an operational constructor inversion, not a source-ID
inference or an A_f fact assumed from CalRet.

The branch's retained history is a compatible event h1 of the *same* family.
Project §5.1 at `(C1,w_f)` to get
`ValueMem_A_f(rho_h1(b_f),r_f,C1,w_f)`. Rewrite only by the lookup equality
to obtain the asserted membership for v. U remains the actual provider of
that same v from the retained branch; no new provider or world is selected.
The telescope's ordinary membership is an independently supplied semantic
family assumption, explicitly required here, and the source endpoint is the
one recorded by b_f. Neither comes from mere capture identity. QED.

**Theorem I.** Interpret the constructed Code-NameValue certificates nf and
nx and their actual Carrier-Delay argument tx in one independently valid
telescope family. At every compatible current event their Name/Return
observations satisfy §5.2; tx satisfies full §5.3 CarrierMem. For every
retained actual CalRet branch of nf under that family, an independently
accepted operand assignment interpreting its Check_c as §5.4 gives argument
typing and acceptance at that branch's actual U and live C1, preserving w_f.

**Proof.** For either Name code at an arbitrary compatible event, resolve its
actual edge by local projection/import restriction of the family. The same
binding value/root at that event has its ValueMem proof and joint fields.
Pure Return retains those fields, so §5.2 follows by conjunction introduction.
An unfinished or zero-step administrative prefix uses the same joint world,
environment and original code/provider incidences, hence its explicit prefix
case holds without assuming a result. These exhaust this code's raw prefixes;
latent values are not executed. Universally quantify this argument over the
independent demand/development domain to prove tx's execution conjunct.
Apply the separate inert Delay introduction to its actual reify/root origin
and this same interpreted family, then conjoin both proofs to obtain full
CarrierMem. No RunCert or inert premise is skipped.

Fix now an arbitrary actual `CalRet(d_f,v,U,C1;w_f)` of nf under this family.
Lemma N derives `ValueMem_A_f(v,r_f,C1,w_f)` from **that completed Name/Return
branch**. The retained actual callable facts at U alone would not suffice.
Eliminate the independent same-value check at `(C1,w_f)` on this derived
proof: its pointwise VIncl component yields membership of the same v at F,
and its proposed provider-indexed component yields
`ViewInlet(v,U,F,C1;w_f)`. All these fields use the same assignment and retain
the original CalRet evidence. This is the predecessor membership link
required by the priority-leaf audit, before actual-inlet elimination.

Project x's binding and original argument-reify fields at that same event.
Construct the very tx stored by Code-Call with those references, giving
ordinary Name/Return argument typing and the preceding full CarrierMem
proof at `(C1,w_f)`. Reflect the emitted whole-argument operand origin under
the independently accepted assignment to obtain acceptance of this tx at
F at `(C1,w_f)`. Instantiate ViewInlet at the retained CalRet event h1,
whose live C_h1=C1, and apply it to **that tx and that acceptance proof**.
It yields actual-U acceptance at the same live C1,w_f, alongside ordinary
argument typing and all original incidences. No invocation output membership,
receipt, entry preservation or independently selected witness is used. QED.

This argument cannot be replaced by C1=C0: the binding family is projected
at C1 explicitly. Nor can reflected constraint truth form a source object:
all code, roots, telescope entries and checking origins were formed in
Theorem S before any semantic reflection. Reflection consumes an independently
valid accepted assignment for existing operand obligations. A successful
pending Function comparison is never an input.

## 7. Exact nested-source derivation and entry interfaces

Write c for the original inner Call, with original symbolic result
`R_c=Comp(E_c,A_c)`. Let `P_f=Value(A_f)`, `P_x=Value(A_x)`,
`A_step=Fun(P_x,R_c)` and `R_apply=Comp(E_bind,A_step)` denote the
**body/result skeletons** only; complete callable interfaces keep their
separate entry/consumer ports. The original source origins determine these
symbolic interfaces before solving. The complete derivation is:

```text
(1) Capture(Empty,L_apply,Empty; no free-binding edges).
    Entry-Value(L_apply,P_f) gives
    E_apply = ValueBind(Empty,d_f,r_f,A_f,apply-entry/rebind origin).

(2) Capture(E_apply,L_step,E_cap; actual f capture edge) gives
    E_cap = Import(Empty,b_f,that edge), with b_f from (1).
    Entry-Value(L_step,P_x) gives
    E_step = ValueBind(E_cap,d_x,r_x,A_x,step-entry/rebind origin).

(3) Data-Name(E_step,name f,Value(A_f); actual import/use edge).
    Code-Result gives nf : Code(E_step,result(name f),Comp(empty,A_f)).
    Data-Name(E_step,name x,Value(A_x); actual local/use edge).
    Code-Result gives nx : Code(E_step,result(name x),Comp(empty,A_x)).

(4) Carrier-Delay(nx,actual Call whole-argument reify origin o_arg)
    gives tx at original r_arg,Comp(empty,A_x).
    Use the actual Gen-Call-0/Application origin at c and its VIncl/
    WholeArgCompatible origins, original F_c,R_f and Call result port.
    Code-Call gives qc : Code(E_step,call(result(name f),result(name x)),R_c),
    retaining tx,Check_c and Suffix_c(U).

(5) Data-Lambda(Capture from (2),Entry from (2),qc,
                actual L_step closure/body-result origin)
    gives ds : Data(E_apply,lambda(x,call(result(name f),result(name x))),
                   Value(A_step)).
    Code-Result(ds,original RHS result port) gives
    qs : Code(E_apply,result(lambda(x,call(result(name f),result(name x)))),
              Comp(empty,A_step)).

(6) Code-Bind's actual RHS-result/rebind origin extends by
    E_after = ResultBind(E_apply,d_step,r_step,A_step,that qs result origin).
    Data-Name(E_after,name step,Value(A_step); actual local/use edge)
    followed by Code-Result gives
    qr : Code(E_after,result(name step),Comp(empty,A_step)).
    Code-Bind(qs,that rebind,qr,original Bind-result ports) gives
    qb : Code(E_apply,
              bind(step,result(lambda(x,call(result(name f),result(name x)))),
                        result(name step)),
              R_apply).

(7) Data-Lambda(Capture from (1),Entry from (1),qb,
                actual L_apply closure/body-result origin)
    gives da : Data(Empty,
      lambda(f,bind(step,
        result(lambda(x,call(result(name f),result(name x)))),
        result(name step))),
      Value(Fun(P_f,R_apply))).
```

This derivation constructs the entire exact approved source, including both
Lambda nodes, the `result(lambda(...))` RHS, its **A_step** result rebind,
and final `result(name step)`. The outer source is inert data da; if its
surrounding source use demands a pure result, Code-Result(da) constructs that
separate outer Return. It is not inserted into the approved core term.
Erasing (1)–(7) gives precisely that term's typed-core V/X translation;
the latent step body stores its own complete Call-input derivation without
invoking it. A_f,r_f remain fixed outer imports, while A_x,F_c and the
original complete result ports retain their actual dependencies in Delta_c.
No endpoint or witness is quantified out of its original scope.

For any independent later call of step with **any admitted whole carrier**,
its actual Value entry first executes that carrier. On each completed entry
Return it produces the ValueBind interpretation for x at the actual post-entry
world. If that entry is pending, its raw continuation keeps the rebind and
entire body/return suffix. This packet constructs those ordered interfaces;
semantic preservation of the external carrier's pending entry remains part
of complete provider/Bind realization. It is not bypassed by the inner pure
Name argument.

At the inner f call, take any actual retained CalRet witness, not a canonical
one. Theorem I gives the inner argument's ordinary typing and actual-U
acceptance for that witness. This is the demanded same-witness CI-ArgFrame
consequence in the **defined input fragment**. It does not assume complete
invocation typing. U's actual role and entry are unchanged.

The resulting static entry interface has two cases selected by U's retained
entry tag:

| Actual entry | Constructed input and outstanding continuation |
| --- | --- |
| Value | The same accepted tx, designated one-layer Force interface, result rebind interface, then actual body, designated consumer and invocation-return interfaces in order. |
| Retained | The same accepted tx at U's declared computation view, retained binding interface, then actual body/explicit consumers and invocation return. No entry Force is added. |
| Operation producer | Its declared entry, native Return of MakeRequestThunk, native return delimiter, then its original declaration-derived result consumer in the complete view. |

These are typed static phase interfaces, not a proof that every dynamic phase
preserves its independent descriptor. At a Request, the original remaining
continuation is retained in its existing order: callee-prefix Requests retain
Delay and the whole invocation; entry Requests retain rebind/body/consumer/
return; body/consumer Requests retain only unfinished shells. Receipt occurs
once before entry and is never prepended on resume. Current-state resumption
remains the original operation. The exact Name callee has no executing Request
prefix, but arbitrary actual provider entries/bodies/consumers can suspend.
No upper seed protects a lower provider or pre-receipt callee prefix.

## 8. What remains genuinely semantic

The single joint dependency for importing Theorem I into the original C0
families is an evidence-preserving **realization of this input fragment**
in the original independent interpretation. Concretely its interpretations
must agree on (a) valid persistent telescope/world families over the complete
admission domain, (b) original pure Return and whole-carrier membership, and
(c) same-returned-provider reflection/inlet elimination of the emitted
operand checking predicates at the actual current event. This is one
simultaneous interpretation obligation, not three independently chosen
models or a new atom assumed true. Its concrete content is specified in §5;
this packet proves the consequent by constructors and does not prove that
such an old-family realization exists.

There are also **broader C0 obligations outside the constructed input
fragment**: complete actual receipt authority, general phase preservation,
ordered Bind/pending typing for effectful provider code and external step
entry, and all returned-provider future uses. Their existing statements
remain unchanged. The input theorem eliminates repeated source Name/lookup/
Return/constant-delay reconstruction; it cannot discharge these broader
semantic laws by renaming them. It constructs the code-side evidence that
an eventual joint interpreter consumes. World/model inhabitance, exhaustive
Option 2 membership and full admission realization remain separate.

The semantic §5.4 clause must not be presented as merely retaining a fact
that the compiler already proved. The compiler knows its checked demand and
checking origins; the sound actual-provider inlet action is precisely the
semantic interpretation still to justify. No source rejection or added user
annotation is proposed. Neither the adopted O0 meaning nor the independent
O1 lane is a premise for §5.4. Missing precision alone demonstrates no actual
semantic alternative. This packet exhibits no specific approved-behavior
decision or competing complete meanings and proposes no user vote. Static
constructor review/publication can proceed independently of the original
actual-provider inlet-reflection realization.

## 9. Freeze, checks and commit packet

Method: documentary constructor formalization, structural/telescope induction,
conjunction interpretation and same-witness dependent elimination. No code,
compiler/build/test/Oracle process, executable probe, child, Git command,
question-board write or shared-record edit was used. Producer integrity checks
are dependency hashes, note whitespace and local links; they are not an
independent review or mechanized proof. The declared baseline is the parent
pin; baseline-byte verification is left to the primary because this producer
was prohibited from using Git.

Changed path: `notes/theory/2026-10-07-call-input-construction-proof.md` only.
No other output file is produced. Proposed checkpoint message:
`research: complete captured Call constructors and same-branch input proofs`.

Review status: initial independent compiler-referee findings B1, M2, M3
and minor4 repaired in one batch; independent delta acceptance pending.
The producer does not certify its own repair. Shared task/index/DAG/authority
updates are deliberately deferred to the primary/curator. Suggested exact
status account: static source input constructors and their induction/
substitution are supplied; a proposed independent Name/Return/carrier/view
fragment proves the same-witness actual-input consequence; its realization
in original semantic families, full phase/pending C0 and broader source/
production conformance remain open. No canonical node closure is requested.

Coverage: the full approved nested source's static constructor tree and its
exact inner Name/Name Call; every retained actual CalRet witness under a
valid interpreted telescope and reflected independent operand assignment;
all independent demand configurations for its constant-return carrier.
No generalized recursion, mutable State/import validity, arbitrary annotation,
conversion execution, callback B implementation, arbitrary effectful Delay
soundness, complete descriptors/admission, principality, inverse licensing,
original contribution witness, complete-family association or production
acceptance is proved. The full inlet contract is retained universally in
ViewInlet and CarrierMem; it is not identified with source-generated delays.

The producer stops writing at handoff. The dependency snapshot follows.

```text
ab9a26a0d1115a18e563b0119b919632b385407bea5107d1cecefaed9b07e46e  AGENTS.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442  rules/compiler-engineering.md
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
71202a2ffeb5a4dcf62bbd7731fb20d923ea5626b67647fb1815302b6659e3d8  notes/theory/2026-10-07-adopted-call-formation-o0.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
c9f174dc8d5209f0415b062747d40873d60ee7f679a9b14388eddce8fa15768c  notes/progress/2026-10-07-call-type-fixed-cut-reconstruction.md
0596e702a61ff7f9e182ad2fbd52ba787d55b45a8b8e81f9c678d4746b6bd44e  notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md
ab46864eb3639fb7dab81f42b756e94b2c0c6b958475e00bcdfa7a7264e6898e  notes/progress/2026-10-08-call-type-closure-construction-attempt.md
0c87d266bdc76b061c5c9e09351723c7c1af4da8f3fca41abc1a4aa184c75dc9  notes/progress/2026-10-08-call-type-computation-entry-attempt.md
9220be81922f3ac37a1540041b99e4123d0f314739b458b7086a67b6f02fe426  notes/progress/2026-10-08-call-type-pending-closure-falsification.md
564deef056a8609fb570d7a4a17c33f0ee14d3d49c6eb7f87c1b1d91c3f0fa43  notes/progress/2026-10-07-call-type-local-law-constructive-attempt.md
2d55271aaaaa5d4af7b912116fa3299431bc10cc16926118767182695b2c4977  notes/progress/2026-10-09-original-call-fiber-construction-round4.md
1024fb2095fb18140609e1a1ae8a39ddf0dd1fa3a3c5635f1ee7fa666f027ef6  notes/progress/2026-10-08-successor-priority-leaf-attacks.md
669b82ec5392792be94dc88f41548676b6f3d46f956245e5e5d058139a2080a3  notes/progress/2026-10-07-successor-priority-attack-round11.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3  questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179  questions/2026-10-05-production-function-bound-membership/approved-answer.md
```
