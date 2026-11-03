# R346 original Call prefix — source-equation obstruction, revision 2

Assignment `R346-PREFIX`; worker `/root/r346_prefix`; baseline supplied by Luna
`cc9749635`. Contract `tasks/agent-loop/sprints/original-callee-prefix-r346.md`,
SHA-256 `3edc4e7c15a94d596d042bd96a930144b7b2a0c290a0bf0f0e99dfef218fc0f3`.
Sole author, no descendants. Actual session namespace/model/effort metadata:
UNKNOWN. Exact leases: this inbox, the unused
`notes/theory/lean/YulangClosure/OriginalCalleePrefixRealizationR346.lean`, and
`/tmp/yulang-r346-prefix`; sole isolated checker owner is this worker.

Outcome: **BLOCKED at an independent source-to-Inputs correspondence**, not a
semantic counterexample. No new theorem or Lean artifact; no parent edge closed
or reduced. The inspected source removes the unsupported premise that original
EI itself demands R311's particular primitive-registry encoding. It does not
supply the missing independent callee semantics. Luna acknowledged the exact
boundary and instructed freezing without an additional audit or wrapper.

## Original authority and parent

Read original complete Call definition (2026-10-07) §2 and its selected proof
§4.2; source-interface definition (2026-10-08) §§2–4 and its selected construction
§§3–6; EI (2026-10-24) §§2–5; R159, R310/R311, R330/R331, R335/R336, R342,
and the actual R315 publication/inner-App owners. Research drafts were not used
to override the selected definitions. The R345 EI handoff matches the contract's
`21f3e0e2e300790c657b33bb25213578c1b5c3ac5eca5da16fb831ce94648940`.

`YulangClosure.SourceAppAdmissionR159.app_admission_iff` remains unchanged:
all outer annotation premises at the incoming environment; one admitted
ViewLogic payload and decoder state; every App local, both finite checkings,
and both source children under that SAME candidate extension. Both annotation
cases and the original source language remain in the parent. The selected
R330 source occurrence is the genuine R315 row 13, at the site-1 ViewLogic
owner. Its callee is `OriginalScopedSourceEventMapR314.Fixture.callee`, exactly
`app (site 2) (name (site 4) 8) (literal (site 5) (int 1))`. It is not a Name-only
callee. Independent whole-Call arm inventory/result relations and GR5's
`callableImage → synthesis` Checking remain separate original requirements.

## Stage 1: original prefix equation versus R311 encoding

The complete Call's structural operation is fixed independently as

```text
EvalCall(Q_e,h) = CalleeRef_e(h) >>= S_h
S_h(actual_f,C1) = ExecuteCallable_X(actual_f,WholeArgRef_e(h),C1;...)
Request(q,C,k_f) >>= S_h
  = Request(q,C,(response,C'). k_f(response,C') >>= S_h).
```

EI §3.1 consumes the genuine same-tuple callee `C_f` evidence, full IF fields
and hard guards, retaining the dependent unreached argument/receiver/result/
future suffix. It creates no future CalRet, carrier, receipt or provider.
IF's Bind/Call constructors retain original clause/result maps and lawful
whole-map actions from independently typed contracts; they do not prove them.
Neither source definition specifies R311's `.calleePrefix` registry leaf.

R311 `phaseBody` and R331 `callee_phase_from_original_operands` demand that leaf
because of their particular incomplete encoding. R331
`selected_prefix_requires_original_declaration` proves necessity for that
encoding only. Thus it is not sound to report the absence of this leaf as an
original semantic impossibility or as a mandatory source-law shape. The direct
source route must instead realize the displayed original Bind equation and its
actual dependent world/evidence telescope.

## Stage 2: R342's concrete positive seam and its limit

Inspected `YulangClosure.OriginalSourceContinuationR342.decoded_source_prefix_and_return`
(:262). The prospective specialization is the existing term

```lean
OriginalSourceContinuationR342.decoded_source_prefix_and_return
  origin a receipts 1 suffix result hsuffix
```

Here `a`, all receipt decorations, every `suffix : HigherOrder.Safety.EvalContext`
and `result` remain arbitrary, with the existing independent
`HigherOrder.Safety.ContextTyped HigherOrder.emptyContext suffix
  (.callable a a) result` input. This is a source-inspected application, not a
newly kernel-checked theorem or a new parent application.

The theorem's actual outputs retain: R315's native initializer decoder;
projection of that initializer to `ret (makeValue a receipts)`; eight concrete
prefix steps under the SAME `suffix`; and, for EVERY TypedCall value typed at
the complete tick response type (including all ordered view lists), typed
resumption plus three real steps to `suffix.plug (ret (identityValue a receipts))`.
It supplies no completed suffix as input and does not choose a response sample.

The literal saved consumer is R342 `savedContext` (:158): tick's result adapter,
block discard/final lambda, then make's result adapter, in that order. The
candidate's `Interaction.Saved` has exactly `operation`, `payload`,
`continuation`, `context`; `Saved.request` plugs the request at this context,
and `Saved.resume` substitutes the response into that SAME continuation before
plugging it. An added outer Bind context retains its literal body through both
operations by `EvalContext.plug`. This is useful evidence for ordered pending
syntax and explains the intended analogue of the original Bind equation.

It does not instantiate that original equation's `C'`: this candidate has no
original `Event s` fiber/eta/history/current/joint-witness/scope/authority/
incidence/dictionary coordinates, no original current-world response relation,
and no map to original `Inputs.observationFields` or its lawful restriction.
R342 labels itself a candidate value-typing calculus. Arbitrary typed
EvalContexts and complete tick responses do not provide those missing objects.
Also, decoding make's initializer does not establish the semantic publication
read at relay's distinct site-4 Name in the actual admitted extension.

## Stage 3: exact first missing output and its owners

The direct original clause is already source-resolved, without a primitive leaf:
`YulangClosure.OriginalSourceScopedInterpretationR335.selected_clause_resolves`
(:80) computes the original clause at the actual full callee Key. Its required
semantic output, at a fixed genuine original callee observation `prior`, has
EXACT existing Lean type (names opened as in R335):

```lean
Meaning inputs (.trace (prior.atInterface
  (state.interfaces
    ⟨(OriginalSourceViewRegistrationR330.request origin).original.calleeSite,
      .synthesis⟩)))
```

Variables retain `s : Sorts`, `View : Type`, `inputs : Inputs s`,
`state : Decoded s View`, `origin : OriginalSource.Declaration`, and
`prior : RawObservation s`. The requested construction is for every observation
of the independently specified original `C_f`; it is NOT a claim that arbitrary
raw observations have this membership. R335 `selected_clause_meaning` (:91)
only equates this membership to the truth of the resolved clause. It supplies
no callee contract, execution relation or world action. No authentic independent
producer of this output from the R342 candidate was found in the inspected
source/Inputs owners.

Unfolding the existing `OriginalSourceInterpretation.PhiT` (:409) shows the
concrete obligations, with `row = prior.atInterface (...)`:

```lean
inputs.eventCoherent row.event ∧
(inputs.observationGuards row).Valid ∧
Meaning inputs (.world row.event) ∧
(match inputs.traceForm row with
 | .pureReturn value => value.event = row.event ∧ Meaning inputs (.value value)
 | .unfinished => True) ∧
(inputs.observationFields row).Holds (Meaning inputs)
```

Already `inputs.eventCoherent prior.event` has no output in R342, because no
original event correspondence is supplied. The ten observation guards include
request, response, rawHandle, phase, currentAuthority and jointConstraints;
they are independent propositions, not a typed current-world response telescope.
The result case retains the SAME event; the world clause retains all installed,
alias, capture and shared-witness equations. No `unfinished` default, changed
provider/world, guessed lawful action, or arbitrary registry can fill this gap.

Owner: Luna → original callee/publication semantic owner and original
Call/IF/Bind-to-Inputs realization owner. Concrete next source paths:

- `OriginalModuleContextBindingR315.lean`: `publication_readback` (:704) exposes
  the genuine publication map inputs; `actual_callee_iff` (:736) requires the
  site-2 ViewLogic, all original inner-App locals/literal semantics, and the
  site-4 published-instance admission with `exactWholeInstance`,
  `resolvedSameBinding`, `computedFetchOnce` in that same extension. Native
  initializer decoding does not supply these laws.
- `OriginalSourceScopedInterpretationR335.lean` (:53–103): owns exact full-key
  callee program/clause readback; consume the real semantic output here.
- `OriginalSourceInterpretation.lean` (:23–104, :325–365, :398–419): owns original
  semantic sorts/events, independent Inputs and exact trace/world clauses.
  Supply an authenticated realization at these actual source indices, including
  raw-prefix/response/current-world readout and the whole lawful action.
- `OriginalSourceContinuationR342.lean` (:158–284), `HigherOrderInteraction.lean`
  (:12–22): reusable initializer/prefix/response syntax; require its genuine
  correspondence to the preceding original objects before consuming its proof
  as original callee evidence. Do not add another assumed bridge record.

Mutual TODO `R346-CALLEE-INPUTS-1`: identify the independently interpreted callee
contract at this full Key, publication and admitted extension; produce its
source/Inputs observation and current-world equations, then construct the
original Bind clause from those equations. Falsifier: a proposed bridge derives
original event/world/guards solely from candidate CompTyped/Steps, replaces the
site-4 published Name by its initializer without publication evidence, freezes
C' at capture, or drops an admitted original raw prefix/response.

## Parent effect, execution and freeze

No source contribution or R318 Union derivation was constructed. R306 still
needs the authentic Call contribution/catalogue correspondence. R159's exact
same-extension locals/children/admission and independent target Checking remain
OPEN. The R311 registry requirement was separated from original authority;
this is a corrected dependency diagnosis, not a proved/reduced semantic edge.
All original annotations, forms, worlds, shared witnesses and arms remain in
scope; no case was removed. Represented reusable candidate evidence is the
actual initializer, Value-entry tick consumer and all typed tick responses.
Original all-world source/Inputs/IF correspondence is omitted/unproved.

Actual read-only environment commands in `notes/theory/lean`: `elan which lake`
(exit 0) resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`;
that native executable's `--version` and `env lean --version` both exited 0.
Observed Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No builds/checker runs, new theorem
types, axiom audits, native runs or test receipts. Axiom results: **NONE**, not
an empty dependency list; existing theorem statements were source-inspected,
not freshly audited. The packet permits checks only for substantive construction,
and its independent source-equation stop condition applied before one existed.

Resource ceiling: 1200 seconds, three stages, one checker, `-j1 -M2048`.
Three investigation stages used; zero proof/build/checker processes beyond
the recorded version queries; no build-cache writes.
Elapsed active duration was not instrumented; no unused time is reclaimed.
Repository writes: this inbox only; leased Lean path never created. Scratch:
`/tmp/yulang-r346-prefix/dependency-hashes.json`, `environment-receipt.json`,
`stop-receipt.json`. No descendants, Git, production, tests, toolchain/config,
shared scheduling/status, or other worker writes.

Frozen input manifest SHA-256:
`5561ad18bef80fda21bacfce542faa302f5da07767e533439441ffbe7f2243f1`.
Environment receipt SHA-256:
`be27af23b4f7f3ea6e02c943fee0aea83ef4cefacca1f3c16a5df5f6839b3022`.
R342 source SHA-256:
`b54a3ccbe0f6152333eafad58cc8d8fdc48f07b3587ba5ae8b1cd8d21a46c34d`.
All other authority/direct-input hashes are in the manifest.

Worker state: STOPPED; no active checker/process or descendant; writes cease
after this revision and the stop receipt are frozen. Independent review,
adjudication, records, integration and any further source-construction packet
remain Luna-owned. Preservation-ready obstruction evidence; no proof or
production promotion is claimed.
