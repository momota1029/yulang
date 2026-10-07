# Original Call rule, round 3: finite assembly and the exact constructor head

Date: 2026-10-07 (assignment date)
Baseline: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`
Branch: `research/simple-sub-intrusion`
Status: repaired conditional proof and canonical premise-record delta independently reviewed PASS
Gates: CALL_TYPE / ORIGINAL_ASSOC P2–P4 / ATTACH / licensing
Exclusive leases: this note and `tools/research_call_original_rule_round3.py`
Semantic and implementation authority: none

## 1. Result and difference from the preceding attempts

No supplied source clause constructs the original owned contribution for
`call(result(name f),result(name x))`. This round does not repeat that stop
as a new result. It proves a stricter discriminator: **even original
assembly for every finite observation family, retaining all original
license witnesses, need not yield the required one complete-family
witness**. The preceding two-observation pointwise discriminator did not
test that stronger hypothesis.

There is also a positive alternative. On a fixed owned original fiber with
finitely many distinguishable complete coverage profiles, finite-family
coverage implies uniform complete-family coverage. The proof needs no bound
on history length. This identifies an actual mathematical P3 reduction, but
the finite-profile premise is not established for Yulang. A finite source
graph or finite `Slots(beta)` does not establish it.

Finally, the downstream audit distinguishes source-origin recovery, which
is already contained in the ORIGINAL_ASSOC witness query, from an actual
`Attach_C` introduction and an original `Lic_C` derivation. The latter two
remain independently interpreted rule conclusions. Promoting those nodes
from the existing existential association result would add a missing rule
implicitly. Section 2.1 supplies a possible full CALL_TYPE proof-level
transition: conditional closure with exact smaller semantic law obligations
retained in existing DESC_CLAUSES/SEM_JOINT. It does not supply those laws.
Primary adjudication and independent review precede any status transition.

## 2. Fixed interpretation and source boundary

The source is exactly `my apply f = { my step x = f x; step }`, with the
Authoritative nested interpretation: sequential local binding, inert return
of `step`, capture of the same outer formal `f`, and ordinary local formal
`x`. The Name/Return/Delay/actual-entry/consumer and pending-suffix skeleton
is retained from CALL_REL and is not claimed as new work.

All judgments below use one original `X`, binder tree, source upper `u`,
original typed `p0`, actual providers and `xi=(nu,K,D)`. Compatible local
extensions remain beneath their original binders. The whole-inlet complete
family is independently admitted; it is not restricted to the source
diagonal `Delay(Return(lookup x))`. Callee computation and receiver upper
invocation keep distinct stage incidences. The upper's directional seed
does not backflow to providers, and provider-owned protection survives.

Direct governing locators are FVIEW §§2–5; typed-core §§6–9; source-contracts
§§2.1–2.2, 3.2–3.5 and 6.1; canonical DAG CALL_TYPE through LIC_INVERT;
round-2 original-kernel construction §§3–5; the open kernel candidate's
P1–P4 and assembly sections; and the P2 constructor attack's source-input
cycle. FVIEW supplies approved formation direction, not completed judgments.
Typed core remains Draft and source-contracts remains a conditional package.

The newly integrated Call closure attempt, pending-closure falsifier and
typed-core/shadow correspondence audit were read in full, with truncated
aggregate windows reread narrowly. They establish no new ordinary
constructor typing. Their respective stops are typed phase/Bind closure,
local continuation versus full suffix typing, and retained source operands
versus semantic producer witnesses. Thus P1 remains independent here.

Relevant Oracle notes inspected: ordinary-call source producer archaeology,
Specializer2 consumer reconstruction, per-formal call-upper consumption, and
typed-provenance routes. They supply historical identities, constraint
aggregation, downstream consumer reconstruction and annotation metadata.
None provides a current original-domain constructor or complete licensing
derivation. No Oracle source execution or output is a premise of this note.

### 2.1 Full constructor implication with an explicit Call-input bridge

The initial round-3 composition claim omitted law-instance premises. Its
formal CalRet conclusion supplies only world and callable membership at a
callee Return. It does not supply argument typing at that returned world,
argument/provider compatibility, first-receipt authority, or ordered Bind
interfaces. DelayIntro, Phase and BindTyped can therefore all hold vacuously
while a raw Call output fails its target. The accepted compiler major repairs
this dependency cone only; §§3–6 and their finite-family theorems are unchanged.
The preceding closure-construction-attempt exposes candidate local laws but
does not independently construct these missing instances either.

The corrected result is conditional on both the local preservation laws and
a separately scoped **CallInput/return-frame bridge** below. This bridge is
OPEN semantic work inside the existing DESC_CLAUSES/SEM_JOINT component. It
constructs inputs to ordinary local laws; it has no whole Call, whole receiver,
attachment, licensing or original-association conclusion. No independently
admitted Call is defined by satisfaction of the desired target.

#### Fixed original tuple and shared evidence order

Fix one original source kernel `X`, binder tree `B_X`, captured lexical
reference environment `rho_X`, provider knot, original Call/callee/argument/
receipt/entry/body/native/consumer/result incidences, and `xi=(nu,K,D)`, in
that order. Fix the original result descriptors `R_f,R_arg,R_call`, actual
provider interface `U` when a callee returns, and the original intermediate
phase descriptors and ordered Bind interfaces recorded by CALL_REL. None is
selected afresh to make a comparison succeed. `rho_X` retains its original
references; keeping those references does not freeze the dynamic world.

Work in one independently justified SEM_JOINT interpretation. Quantify over
**every independently admitted operand/world assignment** `(C0,w0)` under
that tuple, without assuming this domain is inhabited. Admission alone does
not explicitly supply captured-value/provider/world or callee Return typing.
The theorem therefore separately requires the OPEN CI-Operands construction
below; it must supply `Typed_X(R_f,J_f,C0;w_a)` and
`Typed_X(R_arg,J_arg,C0;w_a)` with joint environment/world/provider adequacy
at one common extension `w_a >= w0`.
Even granting those initial facts is insufficient for returned-world transport.
`Typed_X(R,J,C;w)` abbreviates satisfaction
of the existing independent descriptor and related world/provider/continuation
clauses for all complete observations of `J` from `C`. It neither defines
membership by a source image nor introduces a new semantic coordinate.

Under each assignment, universally quantify over actual raw callee Returns,
actual producer/phase alternatives, and all independently admitted response,
current-state raw-resumption and returned-provider future-use developments.
Event-local evidence remains beneath the original binders on which it depends:

```text
fixed X,B_X,rho_X,incidences,xi
  -> forall independently admitted (C0,w0)
    -> retained joint CI-Operands extension w_a >= w0
      -> forall actual callee Return witness d_f at C1
        -> retained CalRet extension w_f >= w_a
          -> one common compatible extension w1 of w_f for the whole frame tuple
            -> forall actual phase developments and their Return witnesses
              -> compatible extensions at their original event scopes
```

Here and below `w' >= w` means an allowed original-scope extension retaining
all original coordinates, `xi`, incident dependencies and established facts.
The frame's conjunctions must hold **at the same extension** as the retained
CalRet/phase evidence. If a further extension is needed, it must preserve
that evidence and satisfy every listed conjunct jointly; separate existential
choices of worlds, provider evidence, argument evidence or authorities are
insufficient. Branch-dependent event witnesses form one coherent scoped
evidence family; incompatible branches need not share fresh event coordinates,
but all branches retain the same original assignment. The bridge is required
for every retained local-law result witness, rather than choosing a different
CalRet witness after learning which argument is convenient.

#### Local laws and the inputs they do not construct

The independently interpreted predicates `Adm_X`, `World_X`, `CallableMem_X`,
`CarrierMem_X` and `OriginalBindInterface_X` retain their original meanings.
`Input_r` below is notation for the **complete conjunction of independently
specified local input premises** for actual phase `r`, not a new certificate.
It includes the current world, required callable/carrier/parameter or prior
result membership, original role/entry/typed-port and captured-provider
compatibility, receipt/consumer/operation/handler authority and dependencies
where applicable. The exhaustive DESC_CLAUSES must specify those fields;
this note does not claim that their concrete clauses have been selected.
`Out_r` similarly abbreviates only the local result/world/provider/authority
facts concluded by a phase Return, not the next phase's complete input.

```text
CalRet:
  Typed_X(R_f,J_f,C0;w_a) and original d_f : J_f -> Return(f,C1)
    => compatible w_f >= w_a with
       World_X(C1;w_f) and CallableMem_X(U,f,C1;w_f),
       including the returned provider's original latent/future obligations

DelayIntro:
  Typed_X(R_arg,J_arg,C1;w1)
  and ArgCompatible_X(R_arg,CarrierContract(U);w1)
    => CarrierMem_X(CarrierContract(U),
                    Delay(J_arg,rho_X),C1;w1)

Phase_r, for every actual producer and actual local phase:
  Input_r(original_phase_operands,C;w)
    => Typed_X(R_r,J_r(original_phase_operands),C;w),
       and for each actual Return(v,C',d_r), compatible w_r >= w
       satisfying Out_r(v,C',d_r;w_r)

BindTyped, at each original ordered Bind occurrence b:
  Typed_X(R_i,J,C;w) and OriginalBindInterface_X(b,R_i,R_o,S;w)
  and for every actual Return(v,C',d) of J, with retained local output facts:
      a compatible common extension w' >= w satisfying
      those facts and Typed_X(R_o,S(v,C'),C';w')
    => Typed_X(R_o,J >>= S,C;w)
```

No Phase law concludes that an entire receiver invocation is typed. A body
phase may type its actual body computation at its intermediate descriptor;
that does not type the receipt/entry/consumer/invocation-return composition.
Nor does the name `OriginalBindInterface` entail its own instance: its
original typed-port, ordered operand and world/dependency compatibility must
be constructed independently. No interface contains membership of the whole
composed computation as a premise or conclusion.

#### OPEN bridge: constructed inputs and return-frame compatibility

CallInput consists of the following smaller laws restricted to the actual
CALL_REL expansion. They are additional hypotheses, not consequences already
proved from admission, CalRet or the structural source equations.

**CI-Operands.** For each independently admitted initial tuple, construct the
original independent captured-environment, provider-knot and current-world
adequacy facts jointly with `Typed_X(R_f,J_f,C0;w)` and
`Typed_X(R_arg,J_arg,C0;w)` at one compatible original-scope extension of
`w0`. Alternatively, explicitly identify and invert independently specified
admission conjuncts that supply these exact facts. Neither route is presently
proved. For Name operands this requires lexical-context/lookup adequacy and
ordinary Return introduction; for computational operands it requires their
independent original typing judgment. This law does not type Call or receiver
invocation, redefine the admitted domain, assume whole-source inhabitance, or
infer semantic membership from structural `Gamma`/lookup identities.

**CI-Bind.** From the independently admitted original operand/world tuple and
the relevant retained local input/output facts, construct every actual
`OriginalBindInterface_X(b,R_i,R_o,S;w)` on that same compatible evidence
extension. This includes the outer callee-to-Delay/invocation Bind, every
entry Force-to-rebind/body Bind, body-to-consumer/return Bind, and operation
native-return-to-declaration-consumer Bind, with their exact ordered suffixes
and intermediate targets. Its inputs exclude typing of `J >>= S` and typing
of the complete invocation. For branch-dependent interfaces this law is
indexed by the original branch and current world; it is not permission to
rename the target or reorder the suffix.

**CI-ArgFrame.** At each actual callee Return, for every retained CalRet
extension `w_f`, the original admitted call operands, `d_f` and CalRet facts
jointly yield one compatible `w1 >= w_f` preserving those facts and satisfying

```text
Typed_X(R_arg,J_arg,C1;w1)
and ArgCompatible_X(R_arg,CarrierContract(U);w1).
```

Both conjuncts refer to the original argument computation and `rho_X`, the
actual returned provider `f,U`, the actual current world `C1`, the original
argument/parameter incidence and unchanged `xi`. Any premise requiring an
initial argument judgment uses `C0`; the bridge must separately justify its
world-relative transport across the **actual callee effects and admitted
resumptions** to `C1`. It must also realize the original whole-carrier
argument-to-provider relation there. Callable membership at `C1` does not
imply either conjunct. Delay is formed inertly only after these facts are
available. No purity, termination, eager argument execution, role change,
new typed path or exclusion of divergent arguments is allowed.

**CI-Receipt.** Once DelayIntro produces the original carrier membership,
combine it with the retained CalRet/CI-ArgFrame facts and independently
admitted original receipt/authority operands to construct the complete first
`Input_receipt(f,Delay(J_arg,rho_X),C1;w1)`, possibly at a further common
compatible extension preserving all those facts. This law supplies the
first phase's independent world/role/entry/receipt/authority/dependency tuple.
A Return consequence of Phase_receipt cannot bootstrap its own input.
The required authority is an independently licensed original authority;
it is never created by receiver upper-output protection or comparison `Q`.

**CI-StepFrame.** For every ordered actual phase transition `r -> r_next`,
every independently admitted local development and actual local Return,
combine the retained `Input_r`, the local phase's `Out_r` at its actual
current world `C'`, and the original transition/consumer/dependency operands
to construct the complete `Input_r_next` at a common compatible extension
of the **returned** evidence. Construct its incident CI-Bind interface
jointly. This supplies any new parameter/provider/carrier compatibility,
rebind, operation/declaration consumer authority and shared dependencies
needed by the next phase; previous result/world facts alone are not declared
to supply them. No next-phase typing or complete pending-suffix typing is an
input to this law. Every retained-entry, body/native, designated-consumer and
return-shell transition has its actual instance; native Return is followed
by its distinct declaration consumer when CALL_REL so specifies. Returned
recursive/latent handles keep all independently admitted future obligations.

CI-Bind and the frame clauses also apply at each admitted re-entry/current
state used by the local law's complete continuation/future clauses, under
the same original scoped evidence. This demands input compatibility at those
states; it does not type the pending suffix by assumption. Any general
independently licensed adaptation present in the original interpretation
adds its actual local phase, frame and Bind-interface instances. No adaptation
is synthesized or erased to make this proof close.

This bridge is a constructed-instance obligation, not a freely chosen Call
certificate. Its conclusions are initial operand/environment/world facts,
returned-world argument typing/compatibility, independent local phase-input
tuples and Bind interfaces. None is original
association, whole output membership, whole receiver typing or complete Call
typing. It still needs proof from independently specified clauses and their
joint realization. CI-ArgFrame's semantic argument typing is deliberately
retained: renaming it a frame does not discharge it.

#### Complete pending, prefix and future closure remains required

BindTyped must be independently validated through these smaller observation
clauses with the same interface, frame instances and evidence family:

```text
Return arm: J -> Return(v,C') uses the constructed, typed suffix at C'.

Request arm: J -> Request(q,Cq,k), with original operation evidence,
  plus the stated typed-suffix/interface premises, yields existing DescMem
  at R_o for Request(q,Cq,(response,C') -> k(response,C') >>= S).
  Every (response,C') ranges over Adm_X at the original operation/raw handle;
  original continuation/world evidence and frame inputs hold at current C'.

Prefix arm: every other independently specified finite/zero-step prefix
  constructor preserves its original target requirements while retaining
  the whole outstanding S and original phase incidence.

Returned-provider arm: each latent/recursive handle retains its original
  provider contract and all independently admitted future call/force uses
  at its actual original returned port. No extra Force occurs at Return.
```

The Request law retains legality at the composed target and every admitted
continuation/world dependency; it does not follow from the raw Bind equation.
The Prefix family is universally indexed by the eventual **exhaustive**
DESC_CLAUSES grammar. The present documents supply no closed list to
instantiate it. If further prefix forms exist, their instances are mandatory.
Divergence and nonreturning computations are covered through all finite and
zero-step prefixes, without a demanded terminal Return or inhabited initial
world. An independently selected infinite-observation requirement beyond the
approved finite/response/resume/future basis would require its own closure
law. Nothing here extrapolates from finite histories to that extra requirement.

#### Conditional composition and the exact source-premise stop

**Theorem (repaired full conditional Call composition).** Under CALL_REL,
the independent admitted operand premises, CalRet, DelayIntro, every actual
Phase and BindTyped law (including complete prefix/future arms), **and every
joint CallInput instance above**, every complete output or pending observation
of the original Call satisfies its existing target descriptor/world/provider
requirements. The theorem quantifies over every independently admitted
assignment and does not prove any assignment exists.

**Proof.** CI-Operands constructs the independent typed operands and joint
environment/world facts at the admitted initial tuple. CI-Bind supplies the
original outer interface at that callee input. At any actual callee Return,
CalRet supplies current world and
actual callable facts. CI-ArgFrame preserves those facts while constructing
argument typing and actual-provider compatibility jointly at `C1`. DelayIntro
now has its full antecedent, so forms carrier membership for the original
inert Delay. CI-Receipt combines these facts with the original independent
authority tuple; hence the first Phase law has its full antecedent.

Apply that local Phase law. At each actual local Return, CI-StepFrame combines
its local Out with the retained tuple to supply the complete next Input and
ordered interface at the returned world. Apply the next local law there.
For the finite ordered syntactic phase expansion, construct the typed suffixes
from the last return shell backwards with BindTyped, universally over each
prior Return/current state. Recursive computations remain inside their local
phase preservation and future laws; no bound on recursive histories is used.
Every Bind application has a constructed interface, typed first computation
and complete typed suffix at the common compatible extension. This derives
typing of the actual receipt/entry/body/native/consumer/return composition;
it was not a bridge input. Value entry includes its designated Force/rebind;
retained entry binds the same carrier without that Force. Native return and
declaration consumer remain distinct ordered computations.

Thus for every actual callee Return the outer Bind's whole suffix is typed.
Apply BindTyped to the typed callee and its CI-Bind interface. At a callee
Request the pending suffix includes Delay and all invocation phases before
receipt. At receiver Requests it includes precisely the remaining phases
after receipt; receipt is never replayed. The Request, exhaustive prefix and
returned-provider arms retain every admitted response/current-state resume/
future development. The bridge and local laws provide one coherent evidence
family at the original binders, not separately chosen witnesses. This yields
the complete local CALL_TYPE target conditionally. QED.

After granting the explicit initial operand facts and CalRet, the first truly
missing subimplication in the attempted returning-callee chain is
**CI-ArgFrame**: typed callee plus its actual Return/current callable
world, even together with argument typing at `C0`, does not yet give argument
typing at `C1` and compatibility with that actual provider at one shared
extension. At the outer composition there is also an independently missing
CI-Bind interface before applying BindTyped. Even granting both, CI-Receipt
and CI-StepFrame remain independent construction obligations. No claim is
made that all these missing implications reduce to argument transport.

The additive fixed-cut reconstruction at remote commit
`6cd43ea855acdd1e7f47a46408715a03d192ffd4` was inspected after the first repair.
It independently localizes the earlier CI-Operands gap: canonical admission
does not state whether capture/provider/world or callee Return membership is
a conjunct. Its Name/Return adequacy stop is therefore retained explicitly,
before the returning-callee frame stop. No governing design changed.

The available source clauses do not supply that first frame implication:
source-contracts §2.1 gives generic independently specified constructor
images and shared-tuple operations, not world transport; §2.2 explicitly
requires local typing to prevent the descriptor conjunct discarding outputs.
Its §3.2 fixes callee, whole argument and ordered Call operands, and §3.3 lists
independent source-typed initial/response/resume/future admission, but neither
gives preservation of the argument's captured-environment typing across an
arbitrary computed callee's effects. §3.5 **assumes** local typing lemmas.
Typed-core §6's application row constrains the whole argument to the parameter
and generates the executable skeleton; symbolic constraints and lexical
identity are not their semantic realization at `C1`. Typed-core §7 transports
supplied membership/inclusion; §9's complete actual-Function condition already
requires whole invocation satisfaction and cannot prove this theorem without
circularity. FVIEW §§2–5 gives formation direction and shared original scopes,
while explicitly leaving the constructing/preserving judgments open.

For `result(name f)`, independently adequate lookup and ordinary Return may
make the actual callee inert with `C1=C0`. That special case removes the
nontrivial callee-effect transport step only if the same-world argument and
actual-provider compatibility are supplied; it still constructs no first
receipt authority or Bind interface. It cannot establish the arbitrary
computed-callee theorem, whose Request/resumption branches reach changed
current worlds. These are exact source-premise gaps, not a repository-wide
absence or nonderivability theorem.

A small propositional discriminator in the checker fixes a raw Call output,
initial argument typing and CalRet world/callable facts. It makes returned-
world argument facts, first receipt inputs and Bind interfaces false in three
successive cuts. All stated local implications can hold while target typing
fails. A positive joint-input case instantiates those implications, and a
pair of disjoint evidence sets shows why separately inhabited argument and
compatibility facts cannot supply their conjunction. This tests the repaired
premise accounting only; it supplies no source-admitted counterexample or
SEM_JOINT interpretation.

**Before/after premise accounting.** Before repair the asserted implication
listed CalRet, DelayIntro, Phase and BindTyped while leaving DelayIntro's
returned-world argument/compatibility, the first complete phase Input and
all OriginalBindInterface instances unconstructed. Next phase Return facts
also were treated as complete next inputs without a shared-frame law. After
repair the same local laws remain, plus explicit CI-Operands, CI-Bind,
CI-ArgFrame, CI-Receipt and CI-StepFrame at the original incidences and coherent scoped
evidence. Their exact input-only conclusions stay OPEN in DESC_CLAUSES/
SEM_JOINT. Initial argument typing is distinct from returned-world transport;
phase Out is distinct from next complete Input.

Suggested status: CALL_TYPE may become CONDITIONAL-CLOSED only if the
primary retains **all** these exact local law/bridge obligations under the
existing semantic targets and independent review accepts the repaired
implication. Neither their semantic instantiation nor source-world inhabitance
is proved. No new DAG edge, original association, TypedCallCert or production
authority is introduced. This producer repair does not certify itself.

## 3. First failed subimplication, with exact input/output sorts

Let `delta` be the finite independently typed source/contract presentation
for the whole-inlet invocation. Its complete relational interpretation
`R_delta` includes original pending continuations, current-state responses
and future returned-provider uses. `delta` is proof syntax, not an original
contribution. Let `o` be an independently introduced original static
slot/owner/path witness for `(beta,s,u,p0)`; its introduction remains P2.

The minimal introduction required **for this direct route**, once those
inputs are supplied, is the following original-domain sequent. It is a
candidate obligation, not a newly selected semantic rule:

```text
delta : independent complete typed source/contract presentation at original rho_U
o : original static owner/slot/path witness at (beta,s,u,p0)
original source-stage maps and compatible joint operands at X,xi
---------------------------------------------------------------- OC-Owned-Image [unproved]
exists original c, v, a.
  c has the original contribution type rho_U
  v realizes the entire R_delta in c, retaining every local evidence arm
  a in I_orig(X) owns that same c through o at (beta,s,u,p0)
  original coverage elimination from v,a validates every member of F_C(X;xi)
```

This head is an existence claim about **existing original sorts**. It does
not set `c=R_delta` or `s=p0`. It neither replaces `I_orig` by the image of
this rule nor identifies original witnesses with equal projected outputs.
If the original kernel splits the head into constructors, the first
unproved bridge is their **owned, indexed preimage totality**, not ordinary
relation construction or descriptor typing.

More precisely, even a proved global interpretation preimage
`exists c. Denotation_orig(c)=R_delta` and an inhabited original owner
fiber do not prove a jointly incident preimage at that owner. In the sorted
discriminator, two distinct original slot labels `s_owned,s_other` exist,
one typed `c_full` denotes the whole family, and the incidence relation
contains only `(s_other,c_full)`. All coordinates, including `xi`, are fixed.
Global contribution representability and ownership separately hold; the
required owned preimage does not. This is not an inconsistent per-port
assignment and is not repaired by saying that the coordinates agree.

The source clauses available before this head construct `R_delta` and,
conditional on CALL_TYPE, type it. They contain no conclusion inhabiting
the particular original contribution/owner pullback. Generic constructor
images act on relations supplied in source-contracts §2.1; an image there
is not a total map into this original indexed sort. This precisely attacks
the global-image shortcut, without asserting repository-wide absence.

OC-Owned-Image already supplies coverage through its original elimination
law, so a separate arbitrary complete-family assembly rule is redundant
**under this exact head**. This is a conditional reduction of a proof
package. It does not show that the head follows from source rules, nor
permit deleting P3 from the current DAG without that derivation.

## 4. Strong finite-assembly falsifier, with all licenses retained

Fix a sorted coordinate tuple `q=(X,beta,s,p0,u,scope,xi)` once. This is a
candidate algebra, not an independently justified Yulang interpretation.
Let its observation family be `F={z_n | n in N}`. Each `z_n` is merely a
distinct member indexed by a finite history length; no actual admitted
Yulang history is asserted. There are no infinite executions in `F`.

Use a distinct contribution sort `{c_n | n in N}` and original association
labels `{a_(n,r) | n in N, r in {own,provider}}`. All associations retain
the same `q`, and every `a_(n,r)` retains its distinct original license
`ell_(n,r)`. In this candidate algebra define

```text
Cover(a_(n,r),z_m) iff m <= n.
```

The two evidence arms remain different even when their coverage is equal.
No original license or incidence is removed. `own` records upper origin;
`provider` retains its independent provider origin. No backflow is added.
Those fields are sorted records, not proofs of Yulang protection semantics.

For any finite observation subfamily `Z`, let `n=max(indices(Z))`, choosing
`n=0` for the empty subfamily. Both `a_(n,own)` and `a_(n,provider)` cover
`Z`. For preservation inside each assembly witness as well, allow a finite
provenance-tree payload `tau` in every `a_(n,r,tau)` and its corresponding
license; leaves retain the exact original input evidence. Coverage ignores
this payload. Binary assembly uses bound `max(n,m)` and a parent tree retaining
both child witnesses, with their distinct arms. Mixed-arm inputs retain both
tags in that tree rather than overwriting either. Every finite iteration has
an original output and retains all input evidence plus all existing licensed
associations outside its image. The universe of finite provenance trees is
countable, and every such witness still has a finite bound `n`.

Nevertheless every candidate `a_(n,r)` misses `z_(n+1)`. Therefore

```text
forall finite Z subset F. exists a. forall z in Z. Cover(a,z)
```

holds, while `exists a. forall z in F. Cover(a,z)` fails. The failure is
not witness loss, a changed scope, independently chosen `xi`, or a
pointwise-only assembly premise. It survives **all finite assemblies** and
full retention of the candidate's original licenses.

This disproves a particular proposed implication between sorted coverage
axioms. It does not certify candidate `c_n` as complete Yulang contributions,
admit the displayed histories, or refute CALL_TYPE/ORIGINAL_ASSOC. An
ordinary complete contribution interpretation might exclude every bounded
coverage object; that would discharge this discriminator by an independent
semantic law, exactly as intended.

The corrective premise need not be closure under every arbitrary infinite
union. One intensional original contribution representing the finite source
presentation's **entire** denotation suffices: OC-Owned-Image above. The
distinction is between a finite number of syntactic constructor steps whose
operands already denote complete relations, and extensional assembly of
finitely many observations. The round-2 K-Image rule is adequate only with
the former reading. A bounded checker of the latter cannot establish it.

## 5. Positive P3 reduction: a finite coverage quotient suffices

Let `A` be the fixed original owned/typed association fiber before coverage.
It may retain arbitrarily many evidence witnesses. Define an equivalence
solely for this proof: `a ~ b` when they cover exactly the same members of
the complete family. This does not quotient or replace the original kernel.

**Lemma.** Suppose `A/~` has finitely many classes, and for every finite
`Z subset F` some `a in A` covers all `Z`. Then one original `a in A`
covers all `F`, including when `F` is empty.

**Proof.** Empty-subfamily coverage gives `A` nonempty. If no association
covered `F`, choose for each of the finitely many classes one observation
missed by its representative. Coverage equivalence makes every member of
that class miss the same observation. The finite set of chosen observations
is consequently covered by no member of `A`, contradicting the premise.
Thus an actual existing original witness covers `F`. No original evidence
is deleted, and no source solution or scope is changed. QED.

This is stronger than a finite-observation theorem: `F` can include
arbitrarily long finite histories. It reduces P3 to finite-family coverage
plus a finite number of **semantic coverage profiles**. It requires neither
a singleton slot nor finite original evidence multiplicity. Conversely, the
countable model has infinitely many distinct coverage profiles and shows
that deleting this premise invalidates this proof route.

Neither the finite static profile inventories supplied to typed-boundary
§6 nor a finite descriptor graph establish `A/~` finite. A single symbolic
port can have infinitely many independently interpreted coverage relations.
The current fixed-`X` source inventory supplies no proved completeness bound
on contributions or their coverage profiles. The lemma is therefore a
useful conditional alternative to OC-Owned-Image, not an established
Yulang P3 closure or permission to bound accepted histories.

## 6. ATTACH and licensing: what the existing prerequisite entails

The ORIGINAL_ASSOC query in source-association-falsification §4 supplies
an original witness with source ownership, original slot/contribution,
complete typing/coverage and retained source/provider arms. Given that
witness, projecting its fields and retaining its source origin is ordinary
existential elimination. This bookkeeping consequence is proved without a
new certificate. It does not create an independently interpreted relation.

The whole ATTACH node additionally asks for an actual `Attach_C`
constructor correspondence and its inversion. The earlier attachment attempt
explicitly labels its displayed `Attach-Call` rule **candidate, not
established**. Original-signature-licensing-construction's hypothesis section
says Attach_C and Lic_C are independently interpreted, not definitions of
the candidate generator. Round-2 §3.3 separately requires K-Attach(r).
These are the decisive dependency locators against a silent closure.

The sorted logical discriminator holds an inhabited original association
and full coverage fixed while interpreting the independent Attach relation
as empty. It satisfies the association result and fails the downstream
head. This is an independence test of those displayed premises, not two
complete permissible language meanings. If an actual original Attach rule
is independently identified with the source-owned fiber, that rule excludes
the discriminator and closes this local packaging seam. That identification
is presently the missing correspondence, not a consequence of existence.

Likewise, retained licensing **origin/provenance** is not automatically a
derivation `ell : Lic_C(X,t)`. With the association and an actual attachment
fixed, an independent empty Lic predicate refutes that inference unless a
Lic-introduction rule or an actual retained Lic derivation is supplied.
Thus LIC_FORWARD cannot be promoted from the current ORIGINAL_ASSOC head.
If an original constructor returns an actual Lic derivation, projection
closes its local forward case; that is precisely K-Lic-Intro, not an extra
global adequacy premise. LIC_INVERT still quantifies over every original
licensed witness, including ones outside any chosen constructor image.

No grammar-wide absence theorem, competing complete semantics, or new user
decision is inferred. Conservative Option 2 observations can retain original
contract origins without source executions. They are not new exposures by
default, and no execution witness is demanded for each such observation.

## 7. Verification, proposed transitions and frozen handoff

The checker tests the finite instances of the countable discriminator and
exhaustively checks every 3-witness/3-observation Boolean coverage relation
for the finite-fiber lemma. It also tests the owned-versus-global preimage
seam and the two independent-predicate seams. Its reference consists of
the mathematical definitions above; it supplies no independent Yulang
descriptor, world, admission or original kernel. The countable result and
arbitrary-family lemma are analytical proofs, not extrapolations from counts.

Budget: one lightweight checker process, bounded to 60 seconds and 1 GiB;
zero Cargo/build processes, children, Git mutations or production edits.
Only the two leased paths are written. No random seed, uncovered shard,
runtime performance claim, or independent review is involved.

Suggested shared-record delta: consider the full conditional CALL_TYPE
composition transition in §2.1, retaining its smaller semantic laws as open
DESC_CLAUSES/SEM_JOINT work together with every explicit CallInput bridge
clause, including initial operand adequacy and joint returned-world evidence.
Sharpen P3's assembly condition to distinguish
whole-denotation original constructor closure from all finite-observation
assembly; optionally retain the finite-coverage-quotient lemma as an
alternative conditional route. Retain ORIGINAL_ASSOC, ATTACH,
LIC_FORWARD and LIC_INVERT open. Source-origin projection is a discharged
bookkeeping sublemma, not a whole-node status transition. No new DAG edge,
slot cardinality, coverage meaning or licensing grammar is selected.

Frozen commit packet: exact paths are the two leases above; pinned baseline
is `6fb5d7f697d5d592e0a39532ddb4967b54e18090`; status is unreviewed producer
research with analytical conditional proofs and sorted falsifiers only.
Proposed checkpoint message: `research: distinguish finite Call assembly from complete original introduction`.
Shared maps, task records and any status promotion are deferred to the primary.
Final check results, artifact hashes and dependency manifest follow below.

### Executed checks and dependency freeze

Final checker command: `prlimit --as=1073741824 timeout 60s python3 tools/research_call_original_rule_round3.py`. Exit 0: 64 finite-family assemblies retaining both evidence arms and exact input payloads; 128 diagonal instances; all 512 Boolean coverage matrices, of which 169 satisfy both finite and uniform coverage; three rule-seam discriminators. Two serial checker runs were performed: the first before adding explicit retained-input payloads, and this final recheck after that repair. No timeout or heavy process. Process wall/peak RSS were not instrumented; individual tool commands completed in under one second. No semantic adequacy is inferred from these counts.

At the original producer freeze all 28 direct dependencies below were compared
byte-for-byte to their pinned Git objects and matched. This is the original
snapshot, not a claim that the coordinating task record remains unchanged
after the repair; the repair dependency delta is recorded below.

| Pinned dependency | SHA-256 |
| --- | --- |
| `AGENTS.md` | `c5ab6ebf0d72fda4c025abc3a0ec9d57c9015a0c8e4ba65900ed385fb62fb9b3` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `tasks/current.md` | `a969662a9ba0d8e2256f4e8d8db8e4abd2b7f57380c461229ce0d1ca1a57036a` |
| `notes/theory/successor-proof-obligations.json` | `e866faaf68a813b95c80dcf46904a1e1f8dfbc5906b3ca019cd8e565eca9ffae` |
| `notes/theory/successor-proof-obligations.md` | `1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-07-successor-original-kernel-construction-round2.md` | `daa802bcf61695845718f669c1d35bfd101d2b61d49607ea8c8de82dee662910` |
| `notes/progress/2026-10-08-original-call-kernel-contract-candidate.md` | `b401a3331ab96eb2668fd7d9bb7ec9488482c0550570f24ab3c29e071320246f` |
| `notes/progress/2026-10-09-original-assoc-p2-constructor-attack.md` | `8561d36a2e82c19247c5c73bafc903222e3636c49e1ffd7f9a0e8ce24636a78f` |
| `notes/progress/2026-10-09-original-association-uniform-witness-falsifier.md` | `ab8cf6c40f221e4a33d5eb40dbe612a42bd04cb9cbbe8ef4b2e828a4e1658d74` |
| `notes/progress/2026-10-08-call-type-closure-construction-attempt.md` | `ab46864eb3639fb7dab81f42b756e94b2c0c6b958475e00bcdfa7a7264e6898e` |
| `notes/progress/2026-10-08-call-type-pending-closure-falsification.md` | `9220be81922f3ac37a1540041b99e4123d0f314739b458b7086a67b6f02fe426` |
| `notes/progress/2026-10-08-call-type-shadow-correspondence-audit.md` | `de4b87744a9e791c2483c9fdd7f1f38354d17f223f71500f2196800764f7f172` |
| `notes/progress/2026-10-08-original-association-shadow-correspondence-audit.md` | `91a327aa28cf36f7ec8885fe5e3efde1be74a3bc25ed5fe32f3410c0b29d260e` |
| `notes/progress/2026-10-06-attach-law-construction-attempt.md` | `b94e829e06027c2bd4cc2f0dbf4a33dc954aa10ee058fbc4918da75ad151a241` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |
| `notes/progress/2026-10-07-frozen-oracle-ordinary-call-source-producer-archaeology.md` | `acd3769b77ceb64b8bb0830bdaaf4a9365d416d85eda097c366ed787db957c6b` |
| `notes/progress/2026-10-07-frozen-oracle-specializer-call-consumer-reconstruction.md` | `e8143355fdecb6ba6d2b1101ea7e5d0d626af012702531105c94f9239d610bcb` |
| `notes/progress/2026-10-08-frozen-oracle-call-upper-consumption-followup.md` | `6ef4f2de0ee7b792233a5f577bfa8fe6820a764cd9fe34e1694beadad07b3594` |
| `notes/progress/2026-10-08-frozen-oracle-typed-provenance-route.md` | `b8a748dbd9a8c7baa796d3c16633b942437445c42c5582f588777d209dfbcb16` |

Original executed checker SHA-256:
`58687fa07c854ff7b7e99a505641e316e7d68874f8284ba95e4d187e054fff3e`.

### Accepted-major repair verification and frozen delta

The fresh repair producer changed only this note's §2.1 dependency cone,
the directly related status/handoff accounting, and the leased checker's
Call-input discriminator. §§3–6 retain SHA-256
`ee4bc2b4d0beb23671e340d90a8c93249587b53c08bb073e1ab7e5c035049de4`;
their P2/P3/P4, ATTACH/licensing and finite-family results are untouched.

One additional checker process ran with
`prlimit --as=1073741824 timeout 60s python3 tools/research_call_original_rule_round3.py`.
Exit 0. The original 64/128/512 (169 successful matrices) and three rule-seam
results are unchanged. The added small logical test passes the three named
vacuity cuts, the fully supplied joint-input implication, and the incompatible
evidence-extension case. It adds no enumeration range or source-semantics
claim. Repair budget consumed: one lightweight verification process, at most
60 seconds and 1 GiB; zero children, Cargo/builds, Git mutations or shared-map
writes. Command tool duration was below one second; process wall/peak RSS
were not separately instrumented. These are producer checks, not certification.

Repaired executed checker SHA-256:
`c5b37eeb87dde0359c85cfbd4a72dec79f5687ddb7d3da78eca514b39f72e2d3`.

The 28 original dependency hashes were rechecked locally: all 27 non-task
inputs still match the baseline manifest. The primary-owned `tasks/current.md`
now has SHA-256
`264898ec5a018b5ecc0c575eb86b732b3ee7d72bbabdc935c50540bf59df5158`.
It is a coordination record, not an additional semantic premise; the pinned
DAG and governing designs are unchanged. No baseline meaning is revised.

Additive evidence was read from frozen remote commit
`6cd43ea855acdd1e7f47a46408715a03d192ffd4`:
`notes/progress/2026-10-07-call-type-fixed-cut-reconstruction.md`, SHA-256
`c9f174dc8d5209f0415b062747d40873d60ee7f679a9b14388eddce8fa15768c`.
Its narrow task paragraph was also read. The addition reinforces the explicit
CI-Operands gap and changes no governing clause. The primary retains integration
of that remote note and all shared records. Repair status: frozen producer
conditional implication, independent delta review pending; no self-certification
or semantic instantiation. Proposed repair checkpoint message:
`research: expose joint Call input and return-frame premises`.

### Independent repaired-proof delta review

Fresh `round3_call_delta_referee` reviewed the frozen repaired note at SHA-256
`b04b21f8eea999e3e949753d24c6a47089eb6b9bd9689630ccfbeffc33694744`
and the repaired checker at the hash above. It passed the proof without new
findings and closed the accepted input-vacuity major: construction supplies
each local law's antecedent jointly at the actual returned/current world.

Fresh `round3_call_delta_spec` independently passed the repaired proof while
requiring an exact canonical-record delta before promotion. DESC_CLAUSES,
SEM_JOINT and CALL_TYPE must retain every ordinary constructor law and all
five CI bridges from §2.1, including their coherent evidence-family and scope
conditions. The primary accepted that record omission as promotion-blocking
and assigned its repair to a fresh theory curator. The two semantic-clause
nodes retain their OPEN statuses; the conditional composition claims no
actual instantiation. Both delta reviewers ran the unchanged small checker
successfully. Final canonical verification is recorded in the
[round-3 review](2026-10-07-successor-round3-review.md). The fresh
`round3_dag_delta_spec` audit subsequently verified the frozen generator,
both generated ledgers and both theory maps, and closed the accepted
record-major without findings. The primary accepted that result. The
canonical CALL_TYPE promotion is now reviewed at precisely the conditional
scope above; actual constructor/input clauses remain OPEN.
