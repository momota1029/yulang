# I-65 fixed theorem statements (C365)

Owner decision: I-65 at integration a66b0a57e1cc2120f7b5c97ba84f22f60d015f32, inbox blob 39b54dc2ff590fdcd1af0e249c22557d4cd468e0. Not a footprint-extension cycle.

## Interface and fixed statements

These signatures specify logical interfaces and remain fixed. Namespace: `Yulang.GeneralDeclarativeI65`. Arguments are universal; neither statement contains a fixture restriction, a premise that the local soundness goal is true, or a claim that the checker is complete.

```lean
theorem dictionary_sound
    (s : State) (q : Request) (d : Dictionary)
    (selected : Classifies s q (.selected d))
    (m : Model) (fit : Fits s m) :
    DictionaryEvidence s m q d

def check (p : Problem) (r : Result) (w : Witness) : Bool

theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
      ∀ (m : Model), Fits p.state m → ReportEvidence p.state m p.root r
```

## Representation and proof obligations

- **1: Declarative layer.** `State` carries the actual source and visible declarations, the logical ordinary constraints, observable typed source state, and a declaration-indexed kind/variance table. `Model` carries the ordinary assignment and separate native observations. `Fits` is interpretation of these data, never successful resolution. `Request` keeps occurrence identity and demand. `Classifies` is an ordered finite derivation over source local rules and the existing diagnostic summary, not an invocation of any checker. At the selected node: actual visible source identity and candidate observations first; literal ordered children/associated equations next. Constructor observations must cite actual source rows and original bounds; primitive/invariant remain real ordinary cases, and declared mode obligations use the same context (including inherited invariance) and are proved from the same state's ordinary atoms. `DictionaryEvidence` is recursively defined semantic evidence with exact child order. Reuse C325/C363 finite-tree composition, but do not count that abstract fold alone as (1); the local semantic transfer also has to be proved. No old Local/C334 conversion for typed cases.
- **2: Unified checker.** `Problem` holds one declarative state and root; `Result` holds the concrete diagnostic tree, optional selected dictionary and literal ordered fixed output receipts attached to occurrences. `Witness` is data in a tagged union of existing certificate shapes. All branch inputs must be recovered from or checked against the *same* problem, not an unlinked inner problem chosen by the witness. Reuse the existing checks; an unrepresented form is `false`, not a new rejection rule or a theorem about eligibility.
- **3: Unified soundness.** `ClassifiedAs` requires the exact reported tree to be a derivation and the actual summary dictionaries/diagnostics and ordered fixed outputs to agree with the report. `ReportEvidence` gives same-model meaning of the ordered tree, its selected subtrees/dictionary and fixed output obligations, including original targets. No conversion of values or normalizer-equivalent aliases into exact receipts. Evidence uses the same `State` and fits every one of its models. Combine the existing per-case lemmas only after binding their state, requests and observations to this exact input. Unsupported branches need no additional semantic rule.

Do not close (1) by storing per-model evidence in a constructor of `Classifies`. Do not close (2)/(3) by permanently defining `check` as false or using proof-carrying witnesses that contain their own acceptance/soundness proof. There is no broader fixture work before (3), except tests of the integration. Track 1/2/3 separately. C remains deferred until 1–3 all close.
