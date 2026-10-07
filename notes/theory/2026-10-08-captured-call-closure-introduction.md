# Captured local Call closure introduction

Date: 2026-10-08
Status: Draft mathematical producer; independent review pending
Claim class: complete scoped constructor theorem in the selected interpretation,
with explicit candidate complete-closure and source-base constructor cases
Baseline: `4b9c6cf50e06e82f364a6293f605bce134997e6f`
Exclusive write lease: this file only
Definition selection / production implementation / cutover authority: none

**Independent mathematical review checkpoint.** A fresh compiler referee
reviewed the complete frozen producer artifact at SHA-256
`76d54ceb51de6836c3ecff1e520fa0ce99b881e10ccca85d75c8a4599b33b410`
and all 23 pinned dependency entries. The verdict is PASS for the stated
conditional constructor theorems, with no blocking, major or minor finding.
The primary accepts that bounded verdict. The mathematical body is unchanged;
the producer's pending-review wording below is historical for this review.
The proposed definition cases are not adopted by this research checkpoint,
and no aggregate theorem, production behavior or cutover is certified.

## 1. Result and interpretation boundary

The theorem below introduces the **newly constructed actual step closure** in

```yu
my apply f = { my step x = f x; step }
```

at a complete contextual Function interface. It does not assume step's
Function membership. Its captured value is the actual f supplied by outer
Value entry, with its original root, capture references and joint witness.
It also proves the local construction/Bind/final Return body and the outer
entry-to-return observations, including arbitrary independently admitted
argument effects, pending entry and divergence. An outer argument need not
be the inner pure Name carrier. The completed body returns step without
invoking it.

The selected [contextual Function definition](../design/2026-10-08-contextual-function-membership-definition.md)
fixes same-provider membership, independent complete challenges, hereditary
immutable bindings and the positive simultaneous interpretation. The selected
[pure-read result constructor](../design/2026-10-08-pure-read-call-result-constructor.md)
fixes `R_c = ReadInvoke(F_c,D_c,IF_c)` at the entire original dependent
interface, for the inner structural pure-read Call. This note supplies the
missing complete closure composition at that interface and explicitly expands
the original source-base Return/Bind/Call derivations needed to apply its
ReadInvoke theorem. Neither IF incidence nor the body/result skeleton supplies
these semantic facts by itself.

Two additions are **candidate pending primary adoption**:

1. The generic complete Value-entry closure descriptor construction in §3,
   composed from the selected Force, typed rebind, body descriptor, original
   invocation-return and pending Bind cases.
2. The explicit source-base prefix/Return/Bind/Call/closure rules in §4 at their
   original source formations. They instantiate the original constructor-image
   inventory; they are not assertions that a sealed foreign `M_E` contains
   these cases.

The relative declared-hole construction in §5 is a mathematical extension of
the selected same-positive-operator proof to one exact newly constructed
value. Its proof is given, rather than assumed. Applying it uniformly to the
independent challenge fields is also part of this candidate introduction case.
No negative recursive clause, new carrier, runtime certificate, admission
restriction, solver rule or source annotation is introduced. No existing
Option 2 alternative is removed. The theorem is not an exhaustive foreign
kernel embedding, production inference result, principality claim or cutover.

## 2. Original objects and exact independent inputs

Fix the actual resolved core derivation approved by the
[nested-source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md):

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f),result(name x)))),
    result(name step)))
```

[Input construction](2026-10-07-call-input-construction-proof.md) §6 provides
its original Capture, Entry-Value, Name, Result, Carrier-Delay, Call, Lambda
and sequential Bind derivations. [Source-interface construction](2026-10-08-call-source-interface-construction.md)
Theorem IF constructs their complete frames and actual reference-use,
return/future and declared-arm placements. These are construction results,
not complete semantic typing premises.

Fix the original binder tree B, source X, static assignment eta0, original
`xi=(nu,K,D)`, all of Delta_c, and their one joint dependent witness. An event
`e=(eta0,h)` has actual live configuration C_e and witness w_e. Preserve

```text
Idx(c) = (B,X,xi,Delta_c;
  d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
beta=(d_f,R_f).
```

Here lexical u_f and checking u are distinct occurrences; neither is an
endpoint. Each new parameter/result witness appears only at its original
licensed binder and event. Overlapping coordinates agree. This is not a
product of independently selected marginal witnesses.

The following are the independent contract inputs. They are fixed before
constructing the proof or consulting Q.

| Input | Exact scope and purpose |
| --- | --- |
| Original raw operation and source-formation rules | The actual core graph, registration/capture references, inert Lambda/Delay, pure Name/Return, ordered Bind, receipt/entry, complete ExecuteCallable and invocation-return equations. They supply raw observations and original incidence guards, not a complete Call soundness assertion. |
| Independent context/history kernel | All originally admitted typed compatible punctured contexts and Initial/Response/raw Resume/FutureUse developments, with their typed paths, continuation, current authority, scope and shared dependency evidence. The domain is fixed independently of the tested membership and Q. |
| Hereditary background and carrier proof fields | Their complete value/world/observation/carrier interpretation is the selected positive operator, with the exact declared-value assumption described in §5 while constructing the new value. Every external binding, carrier result, pending world, typed response and continuation field is included. There is no world/carrier/authority hole. |
| Captured f | At a completed outer entry, the **actual** carrier Return supplies hereditary `ValueMem(A_f,v_f,r_f,e_f)` and its result incidence. For the local theorem this is an independent value input at the preconstruction world. It is not membership of step. |
| Same-value operand inclusion | The independently valid original VIncl(A_f,F_c) at the actual inner use, with its original decorated-value action, and hereditary/legal event restrictions. It changes neither f nor its actual provider decomposition. |
| Inner whole-carrier checking | The independently justified WholeArgCompatible action at F_c, at its original incidences: on the diagonal it checks the actual Delay(Name x) constructed by the Name/Return/Delay proof; for an open filling it checks that filling's independently valid whole-carrier certificate. A static checking origin alone is not proof of this action. |
| Entry interfaces | Original whole-carrier I_f and I_x, including their designated Force view, result endpoints A_f and A_x, response/raw-continuation/future families, bounds and original receipt/context guards. They do not assert that Value entry is pure. |
| Complete result definition | The selected original pure-read `R_c=ReadInvoke(F_c,D_c,IF_c)`, with all dependent decorations. A different independent R_c needs a genuine complete result inclusion and is outside the identity-result theorem. |
| Independent primitive and alternative contracts | Every original additional W/Z/opaque arm at each retained region, with its actual full typing, guards, domain/admission actions, scope and output-dependent provider/future contract. This is an arm-local input, never global structural Call soundness or a source-execution anchor for Z. |

Immediate registration/profile/path/receipt/authority guards and their lawful
source transition actions must be true at their actual original incidences.
They are independent kernel contracts, not inferred from membership or source
labels. A false immediate guard cannot be repaired by coinduction. A world
with unknown mutable State is usable only with its independently provided
transition contract; immutable capture does not justify arbitrary mutation.

No premise is `ValueMem(F_step,v_step)`, `ViewInlet(F_c,U_f)`, complete C0 for
the structural Call, `forall O.M_E(c,O)`, desired output typing, Cover, Q
success or a source image for every complete-production observation.

## 3. Complete Value-entry descriptors, independently of the source image

### 3.1 Generic composition case (candidate)

Given an original whole-carrier entry interface I with result endpoint A,
a body descriptor R under the **actual result-extended** formal binding,
and original complete entry/return/future interface IF, construct

```text
Strict(I, formal:A, R, IF)
  = ContextualFunction(Pure,ValueEntry(I),
      receipt;
      Force_I(wholeCarrier) >>= (a,r_a,C').
        typed-rebind(formal,a,r_a,C');
        R[formal:=(a,r_a),current:=C'];
        original-invocation-return)
```

This is a complete descriptor constructor, not a lambda's pure body skeleton.
Its D domain is every independent complete challenge of this declared I and
IF. Challenge formation requires registered tested-hole data, valid other
fields, I's whole-carrier admission and the original receipt/path/context
preconditions. It requires neither membership of the tested closure nor
actual-provider acceptance/output safety. Actual receipt remains a subsequent
operational transition.

Its P contract is the complete dependent ordered image of these interfaces:

- At initial/receipt/entry prefixes: the actual current world and immediate
  phase/receipt/path/authority guards, no parameter result before Return,
  and the unreached body/return/future interfaces as suspended obligations.
- At a Force Return: that same I-result value/root/provider, hereditary
  result membership and current world, the original typed result-rebind
  edge, then R instantiated at this exact dependent tuple.
- At a Force/body Request: the typed original request, response and raw
  handle, the actual current world and the original unfinished continuation
  with only the remaining suffix appended. All independently admitted raw
  developments, administrative and zero-step prefixes are included.
- At final Return: the same actual result/provider, original lawful invocation
  return and dependent result/future ports. Returning a latent value executes
  none of its future interface. Future demands use their own live event.
- At any declared independent alternative: that arm's original complete
  tuple/evidence and hard guard, its own changed-domain action where needed,
  and its own result-provider/future interface through the original maps.

Return and pending composition are relations on the original **whole tuple**.
They do not union outward effect rows or independently conjoin different
worlds. The descriptor applies to any actual Value-entry callable realizing
these interfaces; it is not defined as successful observations of step.
Its membership is still the selected contextual Function realization clause.
Registration alone therefore does not introduce membership.

All recursive occurrences of hereditary V/W/T/Car in this case are positive.
Admission domains, actual operation, immediate guards, source M_E and opaque
arm predicates are independent fixed parameters. No challenge is filtered
because the tested candidate relation failed. This permits the same selected
positive operator to include the case without changing its raw challenge
or observation domain. Positivity does not supply a missing guard or license.

### 3.2 The actual constructed local interface

Define before execution, at the original source-owned ports,

```text
R_c = ReadInvoke(F_c,D_c,IF_c)
F_step = Strict(I_x,x:A_x,R_c,IF_step)
R_local = original Bind image of
  PureReturn(F_step) and PureReturn(F_step)
  at the actual step RHS/result rebind and final Name result ports.
```

IF_step is generated by the authentic local declaration, capture/entry/body
formation and Theorem IF; its body slot is IF_c at the original instantiated
f capture and x result binding. Its return/future slot is indexed by the
**actual result of f's complete invocation**, including any latent provider.
This descriptor has no assertion that that result is step or has f's root.
A supplied additional hard bound needs its independent checking proof.

A_f and A_x remain their original symbolic value endpoints. F_step is the
complete semantic refinement at the local A_step port. If an independently
fixed interpretation of A_step is different, conclude membership at F_step
and use an independently justified same-value inclusion to A_step. Merely
printing `Fun(Value(A_x),R_c)` does not identify those complete interpretations.
The theorem's local result/binding ports use this constructed complete
interface; an arbitrary unrelated A_step is not silently overwritten.

## 4. Source-base derivations before descriptor typing

This section constructs source-base witnesses. It is separate from the
hereditary descriptor proof. The [original source-contract inventory](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1–3.3 uses independently interpreted constructor images and finite source
base derivations. The following expansions specify the missing local cases
as candidate rules at the source constructors. They preserve prior cases and
introduce no semantics derived from Q or from `DescMem`.

### 4.1 Pure data, closure and Return cases

A source Name witness is the original resolved read edge and the actual
binding projection `(v,r)` at its current event. It witnesses that exact
lookup, without executing a latent value. A source Lambda witness is its
actual registered `Closure(Pure,ValueEntry(I),code,captureReferences)`, the
original ClosureOrigin and capture edges, with the stored source derivation
and its declared complete ports. Formation is inert. This is an M_E data
constructor, **not** a Function-membership premise or latent-body soundness.
A source Delay witness is similarly its actual registered inert carrier,
original reify license and stored code/reference derivation. It is not an
execution certificate.

`ME-Result` takes that data-constructor witness and the raw Return/prefix
rule. A completed Return retains `(v,r,C,w)` at the original result port;
a zero-step/administrative prefix retains its actual code/capture/world
incidence without fabricating a result. These raw witnesses do not require
DescMem and carry no requested effect. Later returned-provider observation
uses the stored original reference/future port and the independent
FutureUse history rule; it does not invoke that provider at Return.

Thus every raw observation of `result(name f)` and `result(name x)` has a
finite ME-Result proof at its original use. The Lambda RHS of step likewise
has a finite closure-data/ME-Result proof even before step's membership is
proved. This distinction is necessary: assuming a *typed* RHS result as the
starting point would assume the conclusion of this paper.

### 4.2 Ordered Bind cases

For `bind(y,q1,q2)` retain q1's source derivation and q2's derivation under
the original actual-result binding interface. Its raw source-base rules are:

```text
ME-Bind-Return:
  q1's actual Return witness (a,r_a,C',w'),
  original result/rebind witness at that SAME tuple,
  q2's finite source witness under that result-extended environment
  ---------------------------------------------------------------
  original full ordered Bind witness at its actual output/prefix

ME-Bind-Request:
  q1's actual Request(q,C,k) source witness,
  original Bind formation and q2's suspended source interface
  ---------------------------------------------------------------
  Request(q,C,(response,C').k(response,C') >>= suffix_q2)
  at the original whole Bind tuple, with its original pending witness
```

Initial/administrative Bind prefixes store only their actual phase and
unreached dependent suffix. A body Request after completed q1 appends only
q2's remaining suffix; q1 is not restarted. The raw result-binding witness
records the actual RHS value/current-world assignment to its source binding;
its semantic ValueMem readout is proved later. Raw M_E does not assume that
readout to identify the Bind operation.

Induction on a finite raw observation/development gives these witnesses:
Return removes one completed first leg and uses the actual suffix observation;
Request retains its current evidence and on each admitted raw resume uses
that handle's current C' and the same suspended source derivation. Repeated
requests repeat this case. Administrative prefixes use the actual stored
phase. Pure divergence contributes each finite unfinished prefix, with no
Return rule application. There is no claim of a finite proof of termination
or of a single finite proof containing an infinite trace.

### 4.3 Inner Call and receiver witnesses

The authentic Call source rule expands at its actual Application origin to

```text
result(name f) >>= (v_f,C1).
  inert-form-the-actual-whole-carrier;
  ExecuteCallable(v_f,actualCarrier,C1;
    original dispatch,return/future interfaces).
```

The callee witness is §4.1's Name/Return proof. On the actual source diagonal,
the Delay witness is §4.1's inert formation of `result(name x)`. The receiver
premise of the source-base Call image is the **raw original actual-operation
observation witness** `o_U` at the retained `Act(v_f,U_f,r_f)` and carrier.
Every actual observation already has this witness by the original operation
relation's definition; inversion identifies the invocation instance and
retains its full tuple. This is neither a semantic safety theorem nor a
request to prove that U_f's implementation came from this source. An
independently supplied callable may be opaque or have its own operation's
native consumer. Its raw observation relation is that original operation.
A claimed source-base rule that instead requires complete Call soundness is
not this constructor-image case and cannot justify this proof.

Apply §4.2's ordered Bind rule to the callee witness and this receiver
witness at exactly C1. The resulting `ME-Call-Structural` proof retains all
receiver entry/body/consumer/native delimiter/invocation-return phases,
pending shells and future-provider ports. For a prefix before callee Return,
use the stored Call formation and unassembled suffix; do not manufacture an
actual Delay/challenge early. For a receiver prefix, use its actual o_U and
the completed same-provider callee/carrier witnesses. Every finite raw resume
has the corresponding original operation witness and the same Bind shell.
No `M_E` of the *complete* Call was supplied as a global assumption.

For the original open whole-carrier slot, the independent port-formation
witness selects the actual filling, including inert/license/reference fields;
use that same filling in ME-Call-Structural. This is the generic source
operator's hole-parametric constructor image. It does not falsely claim that
an arbitrary filling was constructed by source `Delay(Name x)`; the latter
supplies only the diagonal section. Its carrier execution may be effectful,
pending or divergent. Descriptor safety for that filling still requires its
independent whole-carrier certificate and checked admission.

An unanchored Z arm has its own original arm membership witness and tag;
it receives no ME-Call-Structural source-execution witness. W retains its
own original input/image witness and changed coordinates. The full relation
keeps the source base and all those independent alternatives separately.
Arm-local evidence is used at its actual region and composed with surrounding
Bind if that original clause places it there. A whole-Call arm is not forced
through the callee/receiver source rule.

### 4.4 Outer body and entry source witnesses

After an actual outer carrier Return, the raw entry/result-rebind rule
installs its exact returned f. The local Lambda data rule constructs the
actual step with a reference to that f. ME-Result gives its actual RHS Return;
ME-Bind-Return installs that same step at the original RHS-result port;
ME-Result on the final resolved Name edge returns that same step. This derives
the body's source-base witness, including zero-step/administrative prefixes,
from the approved original constructors.

For a pending external outer carrier, its original whole-carrier execution
witness is an **independent input-port** witness. The original entry/Bind
image appends `rebind-f; construct-step; rebind-step; return-name-step;
invocation-return` to its raw continuation. It is not an assumed M_E of
the outer body, and does not require the external carrier to have this
source's code. This gives every finite entry prefix, including divergence.
The same construction supplies local step entry source witnesses from the
independently admitted I_x carrier, with `rebind-x; inner-Call;
invocation-return` as its remaining suffix.

## 5. No hidden closure validity: exact background and coinduction

### 5.1 Same-operator declared-value background

Use the selected positive family `Phi` on `(V,W,T,Car)` in
[simultaneous immutable introduction](2026-10-08-simultaneous-immutable-root-introduction.md)
§3, extended only with §3's positive complete descriptor composition and the
fixed source-base constructors. External/ground cases and every existing
original descriptor/arm parameter remain unchanged. Source M_E's finite
witness predicate is independent of the candidate relation variable.

For the local theorem, H contains only

```text
(F_step,v_step,r_step,e; actual ClosureOrigin,capture(f),original incidence)
```

and its independently licensed restrictions at the **same actual value**
and original witness positions. No other value is made a hole. In particular,
H supplies no f membership, x/result membership, completed world, carrier,
continuation, license, registration, receipt or current-authority leaf.
Aliases may have their original lawful incidence maps but not a new root.
Define

```text
Phi_H(Y).V = Phi(Y).V union H
Phi_H(Y).W = Phi(Y).W
Phi_H(Y).T = Phi(Y).T
Phi_H(Y).Car = Phi(Y).Car
B_H = greatest fixed point Y.Phi_H(Y).
```

Every independent background proof field of a complete punctured challenge
has its actual full B_H interpretation: other value bindings, external
carriers, typed responses, every complete/pending current world, returned
latent values, raw-continuation developments and all compatible future
restrictions. This is uniform over the **fixed whole independent domain**,
including contexts/carriers that themselves reference the tested value at
its declared hole. No invalid record is filtered out afterwards. A foreign
field without this interpretation needs an embedding proof for that whole
domain; the theorem cannot cure it by restricting the domain.

Existing ordinary V*/W*/T*/Car* certificates embed in B_H by monotonicity
since Phi is componentwise included in Phi_H. In particular the independently
supplied captured f certificate is not relabelled or replaced by H. It has
its ordinary complete clause readout. Every B_H.W tuple contains certificates
for **all** of its bindings in the same operator, not just f and x; B_H.Car
contains its inert obligations and every Force/world/response/continuation
family. This prevents the ground-argument/background omission falsifier of
the earlier two-closure draft.

### 5.2 Relative lift, proved for this exact singleton

If `B_H subset S` componentwise and `H subset Phi(S).V`, then
`B_H subset Phi(S)` componentwise.

Proof. Unfold a B_H certificate once. A non-hole V case and every W/T/Car
case has its corresponding Phi(B_H) derivation, with every dependent field
and universal obligation at its original tuple. Positivity maps that whole
derivation to Phi(S). A hole V case is exactly an H tuple and uses the
supplied H replacement proof. There are no other hole cases. The map retains
all scope/provider/world/witness fields; it changes neither a challenge nor
an operation. QED.

Thus using background certificates in the local proof is not assuming the
new closure's final validity. They can only refer to the precise declared
value assumption; its genuine source Function introduction must replace
that assumption, with all immediate guards and all independent challenges.
The largest fixed point is a semantic hereditary interpretation, not the
least finite source-base M_E relation. The latter is proved independently
in §4 for each finite raw observation.

## 6. Main theorem: introduce the newly captured step

**Theorem Step.** At any independently admitted outer post-entry event e_f,
given the exact actual returned f/root/certificate, the original valid
immutable preconstruction world, original capture/registration/source/checking
contracts of §2, and the fixed full background interpretation of §5,
construct hereditary membership of

```text
v_step = Closure(Pure,ValueEntry(I_x),
  call(result(name f),result(name x)),captureReferenceTo(v_f,r_f))
```

at F_step, and its installed immutable root world, simultaneously. Every
restriction preserves this actual f and v_step at their original roots;
every admitted subsequent complete challenge and finite raw development is
included. Membership of v_step, a completed world containing it, and complete
structural Call typing are not inputs.

**Proof.** Form a coalgebra S consisting componentwise of:

1. the complete B_H background;
2. the exact actual v_step tuple at all its independently compatible events;
3. its actual construction/result-installed and invocation worlds, including
   every old/background binding and each parameter/result binding only after
   its actual typed Return;
4. every actual initial/receipt/entry/body/return prefix and independently
   admitted finite development, plus the actual Name Delay carriers and
   their designated observations at the same joint tuples.

The source base remains the independent §4 relation. S is a proof witness,
not the definition of membership, the challenge domain or safe observations.
We prove `S subset Phi(S)` by the following exhaustive cases.

**Construction and captures.** Raw Lambda inversion gives this exact
Act(v_step,U_step,r_step), its original source registration, actual Pure role,
actual Value entry, body code and immutable capture reference. Immediate
formation guards come from the genuine source/input contracts. Restrict the
actual f's hereditary certificate along that original capture edge using
Lemma W of [input realization](2026-10-08-call-semantic-input-realization.md).
Its independently ordinary certificate embeds in the background, hence in
S.V at its exact A_f/root and event. Unfolding that ordinary certificate
before embedding supplies its non-hole clause readout even if an unrelated
alias happens to share an H tuple. No captured active configuration is stored. Worlds use
PhiW with every actual old binding's S.V/S.Car certificate and the original
joint immediate guards. Installing step adds its S.V tuple at the original
RHS-result binding edge. This constructs Phi(S).W; it does not presuppose
a completed installed W* world.

**Independent actual acceptance.** Take any complete independent challenge d
of step. Actual closure inversion identifies
`CarrierContract(U_step)=I_x`, with the original entry/receipt/path preconditions.
Rewrite d's checked I_x whole-carrier admission at this original equality
and pair its context/receipt guards. This constructs ActualAdm(v_step,U_step,d)
at d's actual event, without executing receipt. Acceptance is not inferred
from a body result, Q or an inferred Function shape.

**Initial and administrative prefixes.** Actual invocation establishes the
one receiver/receipt according to its source transition. Unfold the generic
Strict descriptor's initial/receipt cases. Their immediate guards are the
independent challenge guards and original transition contracts. Their world
is the just-constructed S.W tuple. They retain the unexecuted Force/rebind/
body/return/future slots, with no actual x result asserted. Every zero-step
prefix, including one before receipt, is covered. Source witnesses are §4's
original entry/prefix cases, separately from these descriptor facts.

**Arbitrary I_x carrier progress.** d's designated carrier is a B_H.Car tuple,
not necessarily a Name carrier. Unfold its full carrier case. Every Force
observation has its actual B_H.T evidence, B_H.W current world with every
binding, typed request/response/raw continuation and B_H.V result at A_x
when a result exists. These are in S in their actual sorts. Their Phi(S)
readouts follow from §5.2 once the exact value case below is established;
equivalently the present case uses them as S premises in the postfixed proof.
No foreign certificate is appended to S without its full clause unfolding.
The actual receiver Force uses that I_x interface once, after receipt.
It does not recursively force a latent returned x.

**Pending entry and divergence.** If the carrier produces Request, retain

```text
Request(q,C,k_x) >>= S_x
 = Request(q,C,(response,C').k_x(response,C') >>= S_x)
S_x = actual-typed-rebind-x; body-Call; original-invocation-return.
```

The response/raw-handle/current-world evidence is exactly the carrier's
unfolded background field. The Strict pending/Bind clause uses that evidence
and this suspended dependent suffix. On raw resume use the actual live C'
and original compatible extension; no x is bound before its actual Return.
Repeated requests retain the same unexecuted suffix. Every finite prefix of
an admitted divergence is handled identically without creating a body run
or a completed result. Receipt and completed entry phases are not replayed.
The §4 source rules supply corresponding finite raw entry/Bind witnesses.

**Actual Return and parameter binding.** A carrier Return supplies its same
actual x/root/provider, membership at A_x and current world. Lemma W's result
extension, equivalently PhiW with the original typed rebind edge, installs
that precise x, all old binding certificates and the actual joint witness.
Its S.V result certificate and S.W world are not the pre-entry world. This
is the first phase in which x is bound. In that world f is the same restricted
captured value, and both Name/Return source observations have §4.1 witnesses.

**Body Call: source base, R/E, then ReadInvoke.** The original capture/local
Name edges and Return clauses give f at A_f and x at A_x in this same world.
The independently valid same-value inclusion gives that identical actual
f at F_c. The selected Lemma D gives the actual inner Delay(Name x) both
inert formation and all designated execution obligations, with no pre-receipt
argument execution. Whole-argument checking and the independently valid
punctured ambient context assemble the complete challenge d_c at the actual
callee-Return/Delay event; none is asserted before those constructions.

Apply the complete input Theorem R to that same branch and tuple: the actual
whole carrier is accepted by the actual retained U_f. Apply Theorem E there:
all actual complete/pending/zero-step observations, responses, raw resumes,
consumer/native-return phases and future providers satisfy the full P_F_c.
Here the selected proofs are used as their explicit constructor proofs,
not as a claim that an arbitrary S is already the final semantic model.
Name/Return uses the S world/value fields, Delay separately constructs its
inert case and all execution cases from those fields, and checked-challenge
assembly uses the fixed independent domain and immediate guards. For f,
first use the ordinary independent VIncl action on its actual hereditary
input certificate at A_f to obtain its ordinary same-value certificate at
F_c. Unfold that ordinary certificate to its Phi(V*) Function case, then
map the entire readout into Phi(B_H) by V* subset B_H. This provides actual
acceptance and the entire P_F_c[B_H] family without applying VIncl to an
arbitrary S certificate or selecting an H assumption leaf. It remains valid
even if f and an H value tuple coincide extensionally. Positivity maps
that full family, field-for-field, into P_F_c[S]. This is exactly R's
same-provider elimination and E's complete observation argument, with their
original operation equations; it does not assume final membership of step. Every actual retained provider decomposition
of f is covered; no convenient alternative is chosen after Return.

For each such raw observation, §4.3 independently constructs its finite
ME-Call-Structural witness before descriptor typing. Instantiate the selected ReadInvoke constructor proof with that witness,
staged pure-read prefixes, actual carrier/challenge, IF_c, the just-proved
P_F_c[S] readout and unchanged original guards. Its identity complete-result
constructor has only positive hereditary field occurrences, so the same
constructor proof yields the R_c descriptor's Phi(S).T readout at precisely
this tuple. After the postfixed conclusion below this readout becomes the
ordinary `DescMem(R_c,O,w;xi)` certificate. This states the coinductive proof
order explicitly; it does not call a theorem about final membership on an
unjustified candidate model. Its M_E premise has now been **derived** from the original
callee-Return/Delay/actual-invocation/Bind source-base cases; it was not smuggled
in as global Call soundness. The result provider is whatever this U_f actually
returned, with its own retained latent/future certificate, not necessarily f
or step. At a body Request only the body's unfinished continuation and outer
invocation-return remain. Completed x entry and receipt do not recur.

**Return, independent alternatives and future uses.** Compose R_c with the
original invocation-return map in the generic Strict contract. Its typed
current-world/action guards remove only this invocation's actual occurrence;
a borrowed original occurrence is not popped, and an exited apply maker
activation is not revived. Preserve the actual result/provider/root and
whole dependent future interface. This establishes the final Strict cases,
including administrative prefixes immediately before return. Every retained
independent arm uses its own §2 complete contract and original region map;
a changed admission-live coordinate uses that arm's independent domain
certificate. Source ME proofs are not demanded of unanchored Z. No arm is
certified by the unrelated structural U_f or erased when unproved.

For a later FutureUse of step, restrict the same actual capture certificate
and rerun this proof at that future challenge's actual C_e,w_e. All of its
background values, carrier observations, typed responses and continuation
families are already B_H components of S. Its own parameter/result extensions
are S.W constructions as above. Independent Initial/Response/Resume/FutureUse
rules supply the actual compatible event/action evidence. All restrictions
keep eta0, original xi and overlapping witness coordinates; they do not
choose a new world to reconcile incompatible siblings. A later use of a
provider returned by f's body instead uses that provider's own P_F_c future
field and the selected ReadInvoke return/future embedding, with its later
live configuration. It is never substituted with step's future port.

These cases prove the exact H tuples have Phi(S).V readouts: registration,
captures, actual acceptance, all raw observations and every independent
future restriction. The source worlds/observations/carriers have the stated
Phi(S) readouts as well. The relative lift of §5.2 now proves that **every**
background component has its Phi(S) readout; it discharges worlds, arbitrary
carrier results and continuation families together, not by an assumed global
background-lift law. Thus S is postfixed. Greatest-fixed-point introduction
places S in the selected hereditary V*/W*/T*/Car* family, simultaneously
concluding step membership and its installed world. Each finite source-base
observation keeps its separate finite §4 derivation. QED.

## 7. Local block, outer entry and returned closure theorem

**Theorem Block.** At an actual completed outer I_f carrier Return satisfying
§2, construct the exact local Lambda RHS's full typed Return and prefixes,
its actual sequential result-binding world and the final Name/Return body,
with hereditary membership of the returned actual step at F_step.

Proof. The actual carrier Return and Lemma W install its exact f at A_f in
the actual post-entry world. Apply Theorem Step to the raw Lambda produced
by this binding/capture derivation. Step membership and installed root-world
validity are outputs. Pure Return now combines that proved value membership,
the actual world and original result incidence to type the RHS; its raw
source witness was already §4.1's closure/Result case. Original sequential
Bind installs that same RHS value/root, preserving its proved hereditary
certificate at the local result port. The final resolved Name edge selects
that same step; Name/Return preserves its value/root, actual current world
and latent/future interface. ME-Bind-Return and ME-Result in §4.4 prove the
separate whole body source-base relation. No Call of step occurs in this
block, and no Call of captured f is executed during construction. All
administrative/zero-step block prefixes use the actual unreached interfaces;
they do not assume a completed RHS Return. The original Bind image yields
R_local with all dependent result/future fields. QED.

**Theorem OuterTrace.** For every independently admitted actual outer Value
entry at I_f, every finite initial/entry/body/invocation-return observation
and admitted development is valid in the complete ordered interface

```text
receipt;
Force_I_f(outerWholeCarrier) >>= (actual_f,r_f,C_f).
  typed-rebind-f;
  R_local(actual_f,r_f,C_f);
  original-apply-invocation-return.
```

Every completed invocation returns the actual captured step proved in
Theorem Block. An effectful/pending/divergent carrier remains admitted
exactly when its independent original contract admits it.

Proof. Unfold the actual I_f carrier's full same-operator certificate and
initial/pending world fields. Initial/receipt/Force prefixes use the original
entry guards. An entry Request appends exactly

```text
S_f = typed-rebind-f; construct-local-step; rebind-step;
      final-name-step-return; original-apply-invocation-return
```

to its raw continuation. No f binding, step construction or RHS binding is
asserted while entry is pending. Resume uses the response's live current
configuration; repeated requests retain this same remaining suffix and do
not replay receipt. Each actual typed Return supplies the original f/root
membership at the actual post-entry world. Theorem Block gives the suffix
there, including step's newly introduced membership. Original pending/Return
Bind and invocation-return cases compose these field-by-field in the one
joint original tuple. Their source-base witnesses are §4.4's input-port,
entry/Bind/Lambda/Result/Name constructions. Divergence retains every finite
prefix and never invents a body run. The carrier's arbitrary effects remain
in this **complete invocation** interface even though local Lambda formation
and Name Return are pure. Ordinary future use of the returned step is
Theorem Step's hereditary restriction under the future caller's live state,
with no maker activation restored. QED.

This is a full local block and outer-observation constructor theorem, not
an independent proof of every Function membership of the outer apply value.
To introduce apply at a separately fixed full F_apply, its declared whole
challenge/admission and complete result ports must be exactly the displayed
composition or related by a proved whole comparison; the ordinary Function
introduction then uses OuterTrace on every such challenge. An arbitrary
printed outer Function skeleton does not establish those contracts. This
remaining interface-matching requirement does not reintroduce step membership
or complete structural Call soundness as a premise of the proved theorems.

## 8. Open contexts, source diagonal and complete Option 2 accounting

Theorem Step ranges over every independently typed compatible punctured
caller context and **every admitted incoming I_x carrier**, not only carriers
made by this source, returning carriers or a finite client grammar. It
retains complete histories, typed raw handles, current worlds and the
original joint tuple. The outer I_f carrier is similarly arbitrary. These
quantifiers are the ordinary contextual Function quantifiers, and cannot
be replaced with this one program's initially observed clients.

The inner complete Q_c has an additional independent open whole-carrier
slot. On its actual source diagonal the Name/Return/Delay proof constructs
`Delay(Name x)`. For any other independently admitted filling, use that
filling's original inert/universal carrier certificate, original port witness
and checked admission, and retain its full current-context telescope. The
same-value f membership eliminates on the independently assembled challenge
and Theorem E applies to that actual carrier; §4.3 derives its generic
hole-parametric structural source operator witness. ReadInvoke applies
without replacing that filling with the diagonal. Static IF includes every
filling, including the unreached suffix; it does not claim every arbitrary
filling is a source reification of Name x.

Receiver-local alternatives remain part of f's complete P_F_c realization
when its declared interface exposes them. Callee-local alternatives are not
Name executions and require their own original local contract before the
ordered receiver suffix is composed. Whole-Call W/Z alternatives use their
own complete guard/admission/provider/future certificates and original
arm-root-use placement from IF. This theorem derives complete structural
C0 for the pure-read identity-result branch and combines supplied non-source
local arm contracts; it does not generate those semantic contracts by
registration or execute an unanchored Z. An unavailable independent arm
contract leaves that **full-family C0** application unproved. It does not
shrink the domain, remove the arm, or invalidate the actual source introduction
at its proved independent inputs.

The separation between M_E and DescMem is maintained throughout. Source
constructor-image rules prove M_E without using descriptor membership;
R/E and selected ReadInvoke prove DescMem on the same tuple. A production
root additionally admitting W/Z has its own full relation witness, not an
M_E proof manufactured from descriptor membership. No source-tight production
policy, Q-defined admission or post hoc per-port witness selection follows.

## 9. Falsifiers and scope limits

The proof fails, rather than adding a source restriction, if the actual entry
contract is not I_x/I_f without a valid admission bridge; the original
same-value inclusion or whole-carrier checking is false; an immediate
registration/path/receipt/current-authority guard is false; a restrictive
complete bound omits an admitted argument effect; an independent R_c has
another meaning; or an original arm lacks its required semantic contract.
For example an actual callable that returns Int may satisfy F_c while an
unrelated R_c accepts only Bool. IF incidence and P_F_c typing cannot prove
that R_c. The selected identity ReadInvoke case is essential and bounded.

Named shortcuts are ruled out at their exact seams:

| Shortcut | Required proof case |
| --- | --- |
| Assume typed local Lambda RHS | Raw Lambda/ME-Result first; Theorem Step introduces its membership before Return typing. |
| Hidden tested value in world/background | H has only the exact value hole; every W/Car/T field unfolds in the same operator and receives the proved relative lift. |
| Value implies pure complete entry | Arbitrary I_x/I_f carrier Force, pending and divergence cases retain their complete effects and worlds. |
| Restore construction-time handlers/store | Every entry, raw resume and future use uses its actual live event; capture stores references only. |
| Bind x/f before carrier Return | Pending suffix contains rebind without an installed parameter result; extension uses the actual Return tuple. |
| Global M_E assumed to invoke ReadInvoke | Explicit finite Name/Result/Delay/actual-operation/Bind/Call witnesses in §4. |
| Replace returned provider or joint witness | Actual Act decomposition, original dependent result/current-world/future ports and whole-map restrictions throughout. |
| Delete open or unanchored alternatives | §8 uses the complete open carrier frame and every original arm's independent witness and maps. |

Unknown State, arbitrary computed/effectful callee source, unrelated result
constructors, broader recursive initializers, full host-model inhabitance,
foreign interpretation embedding, exhaustive CompleteMem/KV, generalization,
principal inference, resolver completeness, callback-B implementation,
common allowance allocation and production cutover remain outside this proof.
The candidate changes no canonical DAG gate, production code or compiler
behavior. Its source/capture/entry behavior is the exact approved ordinary
program; no user annotation or proof mode is required.

## 10. Frozen producer packet

Changed path: `notes/theory/2026-10-08-captured-call-closure-introduction.md` only.
No Git mutations, children, compiler edits, shared-record changes, broad build,
runtime experiment or executable mathematical probe were performed. The
producer used original constructor derivations, complete R/E and selected
ReadInvoke, dependent field composition and same-operator relative coinduction.
The checks below establish artifact integrity only; they are not independent
mathematical or specification review.

Baseline: `4b9c6cf50e06e82f364a6293f605bce134997e6f`.
Proposed checkpoint message:
`research: introduce actual captured Call closure through complete Value entry`.
Review status: Draft producer theorem; independent review and primary definition
adoption pending. Shared task/theory/index, adoption and aggregate gate records
are deferred to the primary. Recommended review attacks: source-base versus
raw operation distinction, complete Strict interface composition, exact
hole/background lift and full open-carrier/Option 2 accounting. The producer
freezes this artifact on handoff; the primary owns integration and any adoption.

### Direct read dependency SHA-256 at the pinned baseline

| Dependency | SHA-256 |
| --- | --- |
| `AGENTS.md` | `ab9a26a0d1115a18e563b0119b919632b385407bea5107d1cecefaed9b07e46e` |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/compiler-engineering.md` | `1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md` | `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/theory/2026-10-07-owned-call-contribution-construction.md` | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |

Integrity checks: all direct local Markdown links resolve at the pinned baseline; no trailing whitespace or unmatched code fence; no semantic executable probe was used. The baseline/current dependency equality check found no changed direct dependency bytes.
