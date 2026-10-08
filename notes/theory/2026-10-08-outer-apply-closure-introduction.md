# Native outer apply closure: conditional introduction

Date: 2026-10-08
Status: Draft conditional theorem; independently reviewed
Claim class: conditional constructor theorem in the selected positive interpretation
Baseline: `7706a87db78efdec8cb98f3707404bd26ba8eed3`
Exclusive write lease: this file only
Definition selection / production implementation / canonical gate closure: none

## 1. Objective, authority and exact result

Introduce the actual outer Lambda and its installed immutable world for

```yu
my apply f = { my step x = f x; step }
```

at the native complete descriptor

```text
R_c         = ReadInvoke(F_c,D_c,IF_c)
F_step      = Strict(I_x,x:A_x,R_c,IF_step)
R_local     = original ordered Bind image of local Lambda Return,
              actual step rebind, and final Name/Return at F_step
F_apply^nat = Strict(I_f,f:A_f,R_local,IF_apply).
```

These are the complete constructors of
[captured closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
§§2–4 and [captured introduction](2026-10-08-captured-call-closure-introduction.md)
§§3.1,5–7. Actual same-provider hereditary membership and immutable worlds
use [contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md)
§§2–3. The [approved nested source](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§2 fixes sequential local binding, returned function data and capture of the
same actual f. No interpretation of another source form is selected.

Theorem OuterNat in §5 is conditional on the relative local transfer packet
in §3. That packet is **not supplied by the current source/interface
construction results**. The proof does not assume final apply membership,
final validity of a world containing apply, or ordinary hereditary validity
of every carrier-returned f. It exposes the precise stronger local input
needed in place of those circular premises.

This is a new producer argument. Its dependent Step/Block/OuterTrace results
have the independent reviews recorded by their governing selection. This
outer theorem has also passed fresh compiler-referee and spec-auditor review
for the exact conditional claim below. Those reviews do not supply RT or
certify unconditional outer membership.

## 2. Fixed objects and preserved independent contracts

Fix the approved original core derivation, B, X, eta0, `xi=(nu,K,D)`,
original roots/capture incidences, and one joint dependent witness. Each event
has its actual current configuration and lawful event restrictions. Preserve
all overlapping coordinates. Quantification is over every independently
admitted complete punctured-context challenge, actual provider decomposition,
raw observation, finite Response/Resume development and FutureUse demand.
No domain depends on membership, successful Q, or this proof witness.

The following remain genuine inputs:

- Original Lambda/Name/Result/Delay/ordered Bind/entry/return operations,
  formation/registration licenses, and all immediate scope, path, receipt,
  profile, authority and incidence guards at their actual events.
- Complete I_f and I_x carrier contracts, their designated one-layer Force,
  actual result endpoints, response/raw-handle/continuation/future fields,
  and all bounds, including admitted argument effects and divergence.
- Authentic IF_apply, IF_step and IF_c dependent frames at the original
  source ports, with actual entry/return equations. Static incidence alone
  supplies no semantic action. A differently fixed foreign frame needs its
  genuine whole-interface correspondence.
- Original same-value operand inclusion and whole-argument checking at F_c,
  original carrier licenses and independent checked-challenge assembly.
- The exact selected R_c identity constructor, and every retained additional
  arm's independent full contract, guard, admission action and introduced
  provider/future interface. An unavailable contract remains an open premise.
- Complete background fields in the same positive V/W/T/Car operator and
  uniform coverage of the unchanged independent challenge/history domains.
  A foreign field requires its actual evidence-preserving embedding.

No f or x is installed before its actual carrier Return. Returning step
executes no step body or captured f. Later demands use their later live
configuration, with no maker activation or capture-time authority restored.
The installed apply binding here is at F_apply^nat. An independently fixed
A_apply endpoint additionally requires its genuine same-value comparison.

## 3. Precise missing premise: relative local transfer

Let Phi be the selected positive simultaneous operator, including Strict and
the selected source-base constructors. Define the ordinary interpretation
`M = nu Phi` componentwise on V/W/T/Car. Independent challenge domains,
operations and guards are fixed parameters of Phi.

Let H_a consist only of the exact actual apply value at F_apply^nat, its
original root/declaration incidences and lawful event restrictions. It has
no world, carrier, continuation, guard or authority hole. Define

```text
Psi(Y).V = Phi(Y).V union H_a
Psi(Y).W/T/Car = Phi(Y).W/T/Car
B_a = nu Psi.
```

This is an auxiliary relative-coinduction device, not a different final
language meaning. In particular, a B_a world must still unfold every one of
its binding fields; only the exact declared apply value can use H_a.

For each actual local step s made after an admitted outer carrier Return,
let H_s be that exact step value at F_step with its original incidences and
lawful restrictions. Define the second auxiliary background

```text
B_as = nu (Y -> Phi(Y) with V augmented by H_a union H_s).
```

Monotonicity gives `B_a subset B_as`. No other value, world or carrier is
assumed. Using this two-stage mathematical device does not assert that
previously supplied host certificates already have its meaning.

**Relative transfer packet RT.** Uniformly over every admitted outer carrier
Return, every such actual s, and all subsequent complete step demands:

1. The full independent step challenge/response/raw-resume/future proof
   fields have their actual B_as interpretation, including all other values,
   every current world/binding, carriers and continuations. This is an
   evidence-preserving interpretation over the entire fixed domain, not a
   post hoc selection of cases that embed. The outer fields analogously
   have their actual B_a interpretation.
2. The actual returned f at A_f, its same-value inclusion action, and its
   hereditary restrictions supply a **non-hole Function readout**
   `Phi(B_as).V(F_c,v_f,r_f,e)` at every actual inner use. This includes
   every retained actual decomposition, captures, genuine actual admission,
   and its complete `P_F_c[B_as]` observation/future family. The readout must
   come from independently supplied contract/construction evidence; an H_a
   or H_s assumption leaf is not such evidence.
3. The independent checking/admission actions, guards, primitive/alternative
   contracts and original maps listed in §2 apply at these relative tuples.
   Every governed hereditary field is positive and uses this same operator;
   non-hereditary admission/guard facts stay fixed. The existing constructor
   proofs therefore map their readouts componentwise along relation inclusion.

Item 2 is strictly more than `B_as.V(A_f,v_f,r_f,e)` plus an ordinary
`VIncl(A_f,F_c)` theorem. A theorem on final M certificates supplies no
inclusion action on arbitrary relative certificates. Conversely RT does
not require an ordinary final M.V(A_f,f) certificate: it requires the
specific full callable readout used by the local Call, in the relative
interpretation, with an independently justified origin.

If f is itself the declared apply value and F_c is F_apply^nat, item 2 may
ask for the very outer front currently sought. Treating that instance as
an independent fact would be tautological. This theorem does not exclude
such challenges; RT must be supplied without using the desired conclusion,
or discharged by a genuine mutually postfixed construction. No such
construction for that instance is claimed here.

## 4. Relative Block lemma

**Lemma RelativeBlock (conditional on RT).** In B_a, each actual post-entry
local construction yields the same actual step at F_step, its actual
result-installed immutable world, and the full R_local body observations.
It includes complete later step challenges and every admitted finite prefix
and development. The lemma assumes neither final M validity of apply nor
final M validity of the post-entry world.

**Derivation.** Fix one actual s and its B_as background. Form S_s from all
B_as components, this actual s with its lawful restrictions, the actual
construction/result/invocation worlds, and its source observations/carriers.
The raw source witnesses are the finite Lambda/Result/Bind/Name/Call rules
of captured introduction §4; their derivation remains separate from typing.

Repeat the *constructor proof* of Step (§6) in the auxiliary operator Psi,
retaining every original clause, rather than invoking Step's final-model
theorem on an unproved world. The exact differences are:

- Captures and all old/new bindings use their S_s.V/S_s.Car fields. PhiW
  constructs each world readout from every binding and original guard.
- At f's inner use, RT.2 supplies `Phi(B_as).V(F_c,f)`. Positivity carries
  that whole readout into `Phi(S_s).V(F_c,f)`, with the same provider,
  challenges, current worlds and future fields. This replaces the original
  Step proof's ordinary-f-certificate unfolding; no VIncl action is applied
  to an unjustified S_s assumption.
- Arbitrary I_x progress, raw requests/responses, pending suffixes and
  returned x use complete B_as carrier/world/value/continuation unfoldings.
  Name Delay, checking and challenge formation use the actual S_s fields
  and RT.3's independent actions. ReadInvoke uses the full retained
  P_F_c readout and its positive constructor clauses.
- Actual Value-entry inversion supplies `CarrierContract(U_s)=I_x` and
  actual admission from checked whole-carrier admission with the original
  receipt/context guards. Every retained independent arm has its own RT.3
  contract. Future uses repeat at their actual event.

These are exactly Step's source cases; RT supplies each changed proof field.
They prove `H_s subset Phi(S_s).V`. Each H_a tuple is automatically in
Psi(S_s).V as a declared assumption at this intermediate stage. Unfolding
B_as then gives `B_as subset Psi(S_s)`: non-hole cases map positively from
Phi(B_as); H_s uses the constructed source readout; H_a uses Psi's exact
hole. All additional S_s worlds/observations/carriers have the same ordinary
Phi(S_s) readouts from the displayed constructor cases. Thus
`S_s subset Psi(S_s)` and greatest-fixed-point introduction gives
`S_s subset B_a`.

Consequently s and its constructed worlds are genuine B_a certificates,
with the step hole discharged. Selected PureReturn and sequential Bind now
compose those certificates at the actual RHS-result port; final Name/Return
retains the same step/root/current world. This is the Block proof in B_a.
Its prefix cases retain only actual phases and unreached suffixes. QED.

The lemma constructs the **local** hole away while leaving only apply's
explicit relative assumption. It is not the premise “every outer invocation
is already safe.” Its unresolved content is the independently supplied RT
contract, principally RT.2 and full-domain interpretation in RT.1.

## 5. Conditional outer Function and installed-world introduction

**Theorem OuterNat.** Given the fixed source, complete native interfaces,
independent contracts/guards of §2 and RT of §3, the actual registered outer
closure has hereditary M.V membership at F_apply^nat. Its actual immutable
installed root world has M.W validity simultaneously. Every admitted complete
challenge, pending/zero-step observation, finite raw development and lawful
future restriction is retained. Every completed outer invocation returns
the actual captured step introduced in RelativeBlock.

**Proof.** Form S_a from all B_a components, the exact outer closure with
its restrictions, its authentic root-installation/result/entry worlds, and
all actual outer invocation prefixes/developments. The outer Lambda's raw
source formation determines the same stored provider, actual Pure role,
ValueEntry(I_f), body code and authentic capture references. Its formation
and capture guards are independent §2 inputs. Native construction does not
identify it with a differently fixed foreign callable interface.

For each complete independent challenge, actual outer closure inversion
identifies `CarrierContract(U_apply)=I_f`. Its same whole-carrier admission
and original entry/receipt/context guards give ActualAdm, before executing
receipt. This includes every retained actual provider decomposition.

Unfold the complete B_a carrier fields. Initial/receipt/Force prefixes use
their actual current world and immediate guards. Requests retain the original
raw handle and exactly the unfinished suffix

```text
typed-rebind-f; construct-local-step; rebind-step;
final-name-step-return; original-apply-invocation-return.
```

Resume uses its response's live world. Receipt and completed phases are not
replayed. Divergence contributes every finite unfinished prefix. A carrier
Return supplies its exact f/root at A_f and actual B_a world, without claiming
an ordinary M certificate. PhiW extends that tuple after its actual typed
rebind, using all old bindings and the actual B_a.V result.

RelativeBlock supplies the local step, worlds and R_local suffix in B_a.
Unfold those certificates and map their full positive readouts into S_a.
Strict's selected pending/Bind/invocation-return clauses compose the actual
whole tuples and original maps. All effects of I_f stay in this complete
invocation. Returning step executes no latent body. Its future demands use
RelativeBlock at their own actual events. Original source rules supply the
separate finite ME witnesses. Every extra arm uses its original contract
and provider/future map rather than an invented structural execution.

For installation and every actual outer world, PhiW uses the registered
joint guards, every old/background binding, and the exact apply S_a.V tuple
at its new native binding. This constructs the Phi(S_a).W readout; it assumes
no final world containing apply. Parameter/result bindings occur only after
the actual typed Return and lawful rebind.

These cases establish `H_a subset Phi(S_a).V` with actual admission and the
entire Strict observation/future contract. The selected relative-lift proof
(captured introduction §5.2) now gives `B_a subset Phi(S_a)` componentwise:
non-hole unfoldings map positively; the exact H_a case uses that source
readout. Each additional S_a element has the readout constructed above.
Hence `S_a subset Phi(S_a)` and `S_a subset M = nu Phi`. This discharges
apply's remaining assumption and proves both value and installed world.
QED, conditional on RT and all independent §2 contracts.

## 6. Exact gap, failure conditions and evidence boundary

The selected Block/OuterTrace theorems assume ordinary actual-f membership
and a valid preconstruction world in their stated interpretation. They do
not establish the RT packet over an apply-relative domain. The original
Step proof explicitly unfolds an ordinary f certificate before its positive
map. Static IF or Strict skeleton equality cannot replace that step.

There are two invalid shortcuts at this seam:

```text
B_a.Car Return -> B_a.V(A_f,f)
               -/-> M.V(A_f,f)

post-entry B_a.W containing apply
               -/-> M.W containing apply before apply introduction.
```

The missing obligation is the **uniform evidence-preserving relative input
transfer** RT.1–RT.3, especially a non-hole full F_c readout for each actual f
returned by every admitted outer carrier and its future restrictions. An
ordinary fixed-point VIncl law alone is insufficient. If supplying RT.2
requires the target apply front in a coincident challenge, a different
mutually postfixed/source-contract construction is required. Adding another
trace proof or a checker that assumes this transfer does not close it.

False registration/receipt/authority guards, incompatible original witnesses,
a mismatched actual inlet, restrictive bounds that omit admitted entry
effects, missing arm contracts, negative recursive fields, or failure of
full-domain RT transfer prevent application. No failing challenge is removed.
An arbitrary separately fixed F_apply or foreign kernel still needs its
actual whole-interface/interpretation bridge. General recursion/State,
computed callees, unrelated R_c, full C0/CompleteMem/KV, generalization,
principality, production source acceptance and conformance remain unproved.
No canonical DAG gate or authority record is changed.

This is a documentary derivation from independently selected source rules
and positive clauses. There is no executable semantics oracle, randomized
range, seed, mutation experiment, termination experiment or bounded search.
The checks below inspect artifact bytes, links and lease scope only. They
prove neither source rules nor RT nor independent mathematical review.

Recommended next action: independently inspect the exact source-owned
same-value/checking contract for an evidence-producing RT.2 action, together
with full-domain RT.1 coverage; use the coincident f/apply challenge as the
first circularity test. Review this outer proof only as conditional until
that supplier is constructed.

## 7. Frozen commit packet

- Exact leased/changed path:
  `notes/theory/2026-10-08-outer-apply-closure-introduction.md`.
- Baseline: `7706a87db78efdec8cb98f3707404bd26ba8eed3`.
- Dependency changes: none among the direct read inputs listed below;
  each was byte-compared with this baseline. Unrelated dirty shared records
  and the pending successor-generalization question remain untouched.
- Claim/review status: conditional mathematical producer; compiler-referee and
  spec-auditor reviews passed without findings for the stated theorem;
  RT is an open independent transfer contract, not an established result.
- Checks already run: baseline/current direct dependency byte/hash comparison;
  narrow local Markdown-link, fence and trailing-whitespace inspection;
  exact output/lease inspection. No tests, builds, benchmarks or semantic
  executable probes. No children or Git mutations.
- Resources: lightweight sequential read/hash/inspection commands only;
  no heavyweight process, parallel computation or search. Total wall time,
  aggregate CPU and peak RAM were not measured.
- Proposed one-line checkpoint message:
  `research: derive conditional native outer apply closure introduction`.
- Shared-record deltas intentionally left to primary/curator: index this
  conditional outer result and RT residual if accepted; retain existing DAG
  statuses and production boundaries. No authority promotion is proposed.

### Direct dependency snapshot (SHA-256)

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f  notes/theory/2026-10-08-captured-call-closure-introduction.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6  notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488  notes/design/2026-10-08-pure-read-call-result-constructor.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
```
