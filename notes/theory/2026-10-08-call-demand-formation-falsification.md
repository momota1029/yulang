# CALL_TYPE / DemandFormation: argument-only recovery falsification

Date: 2026-10-08
Baseline: `53c9fc737fd5d197d628d7980cc78c90b663e6a2`
Branch: `research/simple-sub-intrusion`
Status: frozen, unreviewed conditional research artifact
Method: source-rule discriminator and dependency inversion; no executable model
Exclusive lease: `notes/theory/2026-10-08-call-demand-formation-falsification.md`
Authority / implementation / gate closure: none

## Objective and claim classes

Attack the shortcut that a typed argument's complete `Result(I_a)` alone
determines the receiving checked inlet, entry/role and complete `Strict` view.
Here “alone” excludes the callee's declared source interface, selected
receiving occurrence, expected literal context, independent whole-argument
checking and original receipt/context evidence. A formation judgment that
also consumes these fields is a different hypothesis and is not falsified.

**Established source decision:** ordinary and explicitly computation-annotated
parameters have different entry skeletons, fixed before body synthesis.
**Structural discriminator:** one argument descriptor can accompany either
entry skeleton. Therefore its projection cannot uniquely recover entry.
**Conditional theorem:** if both skeletons have independently realized
checked contracts accepting the same registered carrier, no argument-only
formation function can return both correct entry labels at that fixed fiber.
**Unproved:** a complete admitted-source semantic counterexample, exhaustive
DemandFormation, or failure of a richer construction retaining source evidence.
No finite-model characterization or reviewed mathematical result is claimed.

## Exact governing sections and retained decisions

- Canonical [CALL_TYPE](successor-proof-obligations.md#call-type): independent
  CalRet/Delay/phase/Bind laws and joint original-scope CI instances; in
  particular CI-ArgFrame needs actual-C1 argument typing and compatibility
  with the retained actual provider. Its conditional status is unchanged.
- Canonical [INLET_CARRIER](successor-proof-obligations.md#inlet-carrier):
  whole carrier, original inlet, actual role/entry and response port,
  pointwise at every independently valid original world. Initial inhabitance
  remains separate.
- [Call integration](../progress/2026-10-08-call-interface-admission-review.md)
  §§2, 5, 9: constructional interfaces do not prove semantic validity;
  selected receiver admission presupposes genuine whole checking; structural
  ReadInvoke does not type an independently fixed result descriptor.
- [Selected contextual membership](../design/2026-10-08-contextual-function-membership-definition.md)
  §§2–4 and its [source realization](2026-10-08-call-semantic-input-realization.md)
  §§2, 3.1–3.2, 5–6: independently formed complete checked challenge first,
  then same-provider membership elimination. Actual-U acceptance and Q are
  absent from challenge introduction premises.
- [Selected captured constructor](../design/2026-10-08-captured-closure-constructor-definition.md)
  §§2–3 and its [theorem](2026-10-08-captured-call-closure-introduction.md)
  §3.1: `Strict(I,formal:A,R,IF)` takes original whole inlet I, dependent body
  R and complete IF as inputs. Whole checking and genuine background guards
  are retained independent premises.
- [Source charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
  §21 is explicit user source Authority despite the charter's overall
  Reviewed status. Ordinary `x` chooses Value entry; outer computation
  annotation chooses retention. Section 24 separately selects receiver role
  from introduction/expected context, before Function effect ports.
- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–3, 5: one source-correlated view, preservation of actual callable
  role/entry, and no generic Value-entry-implies-Pure rule. Its formal/use
  inference example is not reinterpreted here.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§3.1–3.3: finite decorated source grammar, ordered actual entry and
  comparison-independent histories. Approved inlet-domain q1/d1 items 1–5
  retain all independently compatible contexts, direct whole-carrier holes,
  other bindings, original correlations and Option 2 extras.
- Prior [round 11](../progress/2026-10-07-successor-priority-attack-round11.md)
  CALL_TYPE cut separates argument adequacy and actual-provider compatibility.
  [Operand candidate](../progress/2026-10-07-call-type-operand-context-clause-candidate.md)
  C1–C7 and its parameterization correction remain historical conditional
  proposals; they do not supply a general complete descriptor interpretation.

`tasks/current.md` lines around 2985–2996 and the canonical CALL_TYPE entry
summarize a returned-Function sublemma. The primary confirmed there is no
separate frozen artifact locator for that sublemma. It is not an independently
verified theorem premise here. The selected sources above suffice for this
attack; no producer's unfinished proof or defense was read.

## Minimized structural witness

Keep one original finite static graph, assignment `xi=(nu,K,D)`, enclosing
scope, immutable world and registered argument root. Include these two
source-declared receiver skeletons in that graph:

```text
U_V = lambda(Value(Int),                 result(literal Unit))
U_R = lambda(Computation(empty,Int),      result(literal Unit))
c_a = result(literal 0)
t   = Delay(c_a)
Result(I_a) = Comp(empty,Int)
```

These are decorated-core displays of ordinary value-parameter ignore and
explicitly computation-annotated ignore. They use §21's fixed source roles,
not a new annotation rule. The same t may be tested directly at the two
whole-carrier holes; it is not freshened or converted. The two receivers and
their receiving incidences are distinct coordinates of the same graph.
Nothing selects a fresh xi, world, carrier origin or enclosing scope.

At U_V, §21 requires receipt, one designated Force of t, typed result rebind,
then the constant body. At U_R it requires receipt and retained-carrier
binding, then the same body, without entry Force. Both argument observations
still have the identical displayed complete `Comp(empty,Int)` descriptor.
This is stronger than merely sharing Int payloads or outward effect support.
Any additional argument-owned registered-view evidence can also be shared by
using that same t; receiver-owned incidence/entry evidence cannot be recovered
from that shared projection.

The pair needs only one literal carrier, two one-parameter receivers and one
constant body. No recursive definition, operation, handler, computed callee,
returned closure or execution is required to distinguish their source entry
labels. For this two-entry falsifier, fewer than two receiver cases cannot
show nonuniqueness. This is a minimized structural witness, not a proved
globally minimal admitted-program counterexample.

Role is separately controlled by §24's literal/expected context, and by
actual-provider decomposition in selected membership. This witness keeps
ordinary receiver role Pure in both cases, so it proves no two-role
inhabitation result. Entry nonuniqueness already defeats the proposed joint
recovery claim. A second hypothetical Handler model would add no needed
discrimination and is not constructed.

## Conditional theorem and exact missing premise

Let H be the following additional hypothesis, not a result of this note:
the original independently typed receiving contexts and complete checked
contracts for U_V and U_R are realized at one valid current event, with the
same t admitted as their whole-carrier hole, preserving all other values,
paths, continuations, authority and original dependencies.

Suppose an argument-only function `G_xi(Result(I_a))` must return each correct
complete receiving presentation, including its actual entry label. Under H,
both demands give G the same input `Comp(empty,Int)`. Correctness at U_V
requires its entry projection be Value entry; correctness at U_R requires
retained entry. Those are distinct labels by §21, so no such single-output G
exists. The proof uses the independently selected source rule as oracle; it
does not assume G's intended transition rules. QED, conditional on H.

If formation instead returns a relation of candidates, both may occur. That
relation does not identify which receiving incidence is lawful for this
source call. Selection still needs the source boundary and its retained
checking/guard evidence. No principality or inability to solve those source
constraints follows from the discriminator.

The theorem's entry projection is the original actual receiving entry, not
an assertion that every target view of a receiver must carry that same label.
It proves neither that every cross-role assignment fails nor uniqueness of
the checked Function view. If the proposed shortcut only selects one target
Strict for a restricted Value-entry source lane, this pair does not refute its
conditional adequacy. That lane still owes the independent source-boundary,
whole-checking and context premises in the next section.

H is the precise stop condition for a complete admitted-source counterexample.
The selected complete closure constructor supplies Value-entry `Strict`;
it does not supply a corresponding complete retained-ignore introduction
and all its independently admitted contexts. Draft typed-core §6 gives the
source skeleton and explicitly leaves full annotation/path checking open.
Calling the displayed skeleton fully admitted would assume that missing
supplier. No proof that H cannot be supplied is made.

## Why the reviewed receiver result cannot invert formation

The selected proof has this direction at the original event:

```text
independent argument carrier validity
+ whole-argument checking at declared F
+ valid punctured context, other values and original hole incidences
    -> d in D_F
same-value callee membership at that F, retaining actual U
    -> ActualAdm(U,d) and all actual receiver observations in P_F(d)
```

The first implication forms a challenge of an already declared F; the second
eliminates membership of the same returned provider. Neither reconstructs F
from `Result(I_a)`. `Strict(I,formal:A,R,IF)` also takes I/R/IF explicitly.
An emitted input or source origin is a locator, not the missing whole-checking
truth. Replacing an unknown carrier contract by the argument descriptor,
using successful Q to select guards, or assuming ActualAdm in order to form d
would change these premises or make admission circular.

This result does not forbid a source-directed DemandFormation retaining the
callee declaration/formal relation, actual argument view, original receiving
occurrence, independent boundary derivation, context guards and dependent IF.
It identifies the fields that argument-only projection fails to supply.

## Evidence, independence, omitted cases and failure conditions

Commands: bounded `sed`/`rg` reads; `git rev-parse HEAD` and branch/status reads;
`git diff --exit-code 53c9fc737fd5d197d628d7980cc78c90b663e6a2 -- <dependencies>`
returned 0 with no diff; `sha256sum <dependencies>` recorded the snapshot below.
No Git mutation, tests, builds, formatter, executable probe, Oracle run or
finite enumeration occurred. Seeds/ranges and process/model domains: none.
Mutation executions: none. Named rejected shortcut: recovering receiver entry
and complete Strict from only the argument's result interface.

The independent oracle for the structural discriminator is explicit source
Authority §21, rather than two checkers implementing supplied transition rules.
The conditional semantic theorem shares the selected carrier/context and
membership interpretation. It does not independently validate that entire
interpretation or the truth/nonvacuity of H. A simulated Force/Retain trace
would leave H untouched, so no such toy probe was launched.

Early aggregate captures truncated; exact contract nodes and governing sections
were reread in bounded extracts. One nonexistent guessed theory filename was
discarded; the definition's actual realization locator was then used. No full
repository search, absence-of-rule theorem or exhaustive source audit is claimed.

Failure boundary: if “Result(I_a)” is redefined to include the original selected
callee/receiving derivation, or G also accepts that derivation, this attack's
argument-only hypothesis no longer applies. If a chosen complete interpretation
does not realize H, only the structural distinction remains. A Value-entry-only
lane may select Strict from additional source inputs without contradiction.
Effects/pending/futures, all whole-Call W/Z arms, retained contract realization,
general source checking, foreign kernels, State, production correspondence and
principality remain unverified. All independent Option 2 members remain intact.

Resource usage: static research only; zero build/test/model processes and no
probe output files. Read/hash commands were short-lived; some independent reads
were concurrent. CPU and peak memory were not measured. Exact elapsed wall time
was not recorded; no sustained computation occurred. All unrelated work was
preserved. Writes stop at this frozen note; independent review is pending.

Recommended next action: make the source call's retained receiving derivation
and declared whole inlet explicit inputs to DemandFormation, then review its
forward construction against the selected challenge premises. Do not require
an argument-only inverse theorem or weaken the source entry rules.

## Dependency snapshot and commit packet

All listed live dependencies matched the pinned baseline immediately before
writing. SHA-256:

```text
59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc notes/theory/successor-proof-obligations.md
b679ebc836cc3691854a243444595e5a8f35116a0766503886eebc65a1eb07c4 notes/progress/2026-10-08-call-interface-admission-review.md
669b82ec5392792be94dc88f41548676b6f3d46f956245e5e5d058139a2080a3 notes/progress/2026-10-07-successor-priority-attack-round11.md
0596e702a61ff7f9e182ad2fbd52ba787d55b45a8b8e81f9c678d4746b6bd44e notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f notes/theory/2026-10-08-captured-call-closure-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3 questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
11cd4ba05991408b0bc233c52a46f5f79c9ccbe5e95a71890a542f488b132ee8 tasks/current.md
```

- Exact leased path: `notes/theory/2026-10-08-call-demand-formation-falsification.md`.
- Baseline SHA: `53c9fc737fd5d197d628d7980cc78c90b663e6a2`.
- Changed dependency hashes: none observed; primary revalidates before review
  or checkpoint integration.
- Claim/review status: frozen unreviewed structural discriminator and
  conditional nonuniqueness theorem; no complete admitted-source counterexample,
  semantic adoption, production authority or gate closure.
- Checks run: governing-source reads, baseline/branch/lease status,
  exact dependency diff and SHA-256 snapshot. No semantic execution.
- Proposed commit: `research: falsify argument-only Call demand recovery`.
- Shared-record deltas left to primary/curator: link this bounded discriminator;
  retain CALL_TYPE and INLET_CARRIER statuses; distinguish source-directed
  formation from an argument-only inverse; record H's retained-contract
  realization as unproved only if that stronger counterexample is pursued.
  No shared task/index/authority, question bundle, compiler, manifest, lockfile
  or another worker's path was edited.
