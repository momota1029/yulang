# R89 proof pre-execution review and audit authorization

Sprint: `EFFECT-PERMISSION-APP-DEMAND-INCIDENCE/20261101-R89`.

## Independent pre-execution review

Reviewer: `/root/r86_independent_review`, independent read-only reviewer, neither proof author nor primary.

Verdict: **PASS for pre-execution readiness; Lean acceptance remains pending.** The reviewer matched the candidate (`notes/theory/lean/YulangClosure/SourceAppDemandIncidenceR89.lean`, 8,967 bytes, SHA-256 `ae1e029cc2ac1fed98dbb1a9059bb7ed94573df6aa9a35e677bbed51395baa0f`) and proof handoff (`tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-proof.md`, 11,169 bytes, SHA-256 `a529fa1ae1d3dc25f6b986499a5fe93a55ea3122e46ff0a5262ce2bb8b8cc49a`). All four statement texts remain byte-identical to R88. The explicit `AtomKind.roleAndInitialCallOrigin` fixes the reported ambiguity; `app_rule` rewrites the actual `sourceRules` equation before reduction. All original premises, both children, annotations and one shared witness remain. No proof hole or kernel bypass was found.

The reviewer independently matched both the original R89 manifest (33/33 inputs) and amended manifest r2 (34/34 inputs). Scope remains structural App inversion over the parameterized Kernel; native incidence, qualified extrusion, joint lift and A/B remain open. The reviewer ran no Lean, build or tests.

## Primary exact-input authorization — call 1 of at most 2

Authorized by the R89 contract and the fresh PASS above. This records the exact stdin and executable preflight before the primary's first direct invocation.

Flattening recipe, in memory, dependency-first: read the pinned `OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, then the frozen R89 candidate as exact bytes; remove only lines beginning with `import YulangClosure.` from the latter two; retain `import Std`; concatenate without writing an intermediate file. The candidate already contains all three helper `#print`s and four complete `#check @...` / `#print axioms ...` pairs.

- `OriginalSourceSyntax.lean`: 22,040 bytes, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- `OriginalSourceGeneration.lean`: 66,485 bytes, SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- R89 candidate: 8,967 bytes, SHA-256 `ae1e029cc2ac1fed98dbb1a9059bb7ed94573df6aa9a35e677bbed51395baa0f`.
- Exact flattened stdin: 97,404 bytes, SHA-256 `e72174bdab2961be92b3577f2bf7ecf4b88af3ac6edce154a4f74868b023f199`.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; version Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Invocation: `lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, hard timeout 120 seconds.
- No Lake, build, test, cache, scratch, output file, worktree or environment is authorized or created.

This authorization covers only call 1 and these exact bytes. Exit, stdout/stderr, printed theorem types, and complete axiom results are pending execution and will be appended as a new receipt.


## Primary Lean audit receipt — call 1 of at most 2

- Start UTC: `2026-10-31T15:10:20.792056+00:00`; end UTC: `2026-10-31T15:10:31.808716+00:00`; elapsed: `11.016659s`; timed out: `false`.
- Executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean 4.35.0; args `-j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`.
- Frozen candidate SHA-256: `ae1e029cc2ac1fed98dbb1a9059bb7ed94573df6aa9a35e677bbed51395baa0f`. Flattened stdin: **97404 bytes**, SHA-256 `e72174bdab2961be92b3577f2bf7ecf4b88af3ac6edce154a4f74868b023f199`.
- Exit: `1`; child max RSS: `903284 KiB`; stdout: 14578 bytes, SHA-256 `a0f5fa3403dacea7bcf3993cdf08dc0f366f71d545d4a06c09e686abacd8c838`; stderr: 0 bytes, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

### Complete stdout

```text
<stdin>:1677:3: error: Function expected at
  [AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
      AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
    if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else []
but this term has type
  List AtomKind

Note: Expected a function because this term is being applied to the argument
  .map
<stdin>:1707:56: error: Tactic `rfl` failed: The left-hand side
  annotated mark context
    (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
      (RuleTree.rule Rule.app mark.site context
        (premises
            ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
              if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
            mark.site context [callee.site, argument.site] ++
          [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
              (endpoint mark.site Port.descriptor),
            check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
              (endpoint mark.site Port.synthesis)])
        (RuleForest.two (sourceRules context callee) (sourceRules context argument))))
is not definitionally equal to the right-hand side
  match none with
  | none => appCore mark.site context callee argument
  | some target =>
    RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
      (RuleForest.one (appCore mark.site context callee argument))

case none
mark : Mark
context : Context
callee argument : Source Category.expression
⊢ annotated mark context
      (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
        (RuleTree.rule Rule.app mark.site context
          (premises
              ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                  AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
              mark.site context [callee.site, argument.site] ++
            [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
                (endpoint mark.site Port.descriptor),
              check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
                (endpoint mark.site Port.synthesis)])
          (RuleForest.two (sourceRules context callee) (sourceRules context argument)))) =
    match none with
    | none => appCore mark.site context callee argument
    | some target =>
      RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
        (RuleForest.one (appCore mark.site context callee argument))
<stdin>:1707:56: error: Tactic `rfl` failed: The left-hand side
  annotated mark context
    (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
      (RuleTree.rule Rule.app mark.site context
        (premises
            ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
              if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
            mark.site context [callee.site, argument.site] ++
          [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
              (endpoint mark.site Port.descriptor),
            check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
              (endpoint mark.site Port.synthesis)])
        (RuleForest.two (sourceRules context callee) (sourceRules context argument))))
is not definitionally equal to the right-hand side
  match some val✝ with
  | none => appCore mark.site context callee argument
  | some target =>
    RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
      (RuleForest.one (appCore mark.site context callee argument))

case some
mark : Mark
context : Context
callee argument : Source Category.expression
val✝ : Annotation
⊢ annotated mark context
      (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
        (RuleTree.rule Rule.app mark.site context
          (premises
              ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                  AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
              mark.site context [callee.site, argument.site] ++
            [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
                (endpoint mark.site Port.descriptor),
              check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
                (endpoint mark.site Port.synthesis)])
          (RuleForest.two (sourceRules context callee) (sourceRules context argument)))) =
    match some val✝ with
    | none => appCore mark.site context callee argument
    | some target =>
      RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
        (RuleForest.one (appCore mark.site context callee argument))
def YulangClosure.SourceAppDemandIncidenceR89.appPremises : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
      YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
        List YulangClosure.OriginalSource.Premise :=
fun site context callee argument =>
  sorry ++
    [YulangClosure.OriginalSource.Premise.checking
        { mode := YulangClosure.OriginalSource.CheckMode.value, site := site, context := context,
          lower := { site := callee.site, port := YulangClosure.OriginalSource.Port.returnedValue },
          upper := { site := site, port := YulangClosure.OriginalSource.Port.descriptor } },
      YulangClosure.OriginalSource.Premise.checking
        { mode := YulangClosure.OriginalSource.CheckMode.computation, site := site, context := context,
          lower := { site := site, port := YulangClosure.OriginalSource.Port.callableImage },
          upper := { site := site, port := YulangClosure.OriginalSource.Port.synthesis } }]
def YulangClosure.SourceAppDemandIncidenceR89.appCore : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
      YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
        YulangClosure.OriginalSource.RuleTree :=
fun site context callee argument =>
  YulangClosure.OriginalSource.RuleTree.existsE
    { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
    (YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.app site context
      (YulangClosure.SourceAppDemandIncidenceR89.appPremises site context callee argument)
      (YulangClosure.OriginalSource.RuleForest.two (YulangClosure.OriginalSource.sourceRules context callee)
        (YulangClosure.OriginalSource.sourceRules context argument)))
def YulangClosure.SourceAppDemandIncidenceR89.annotationPremises : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Annotation → List YulangClosure.OriginalSource.Premise :=
fun site context target =>
  [YulangClosure.OriginalSource.Premise.atom
      (have __src :=
        YulangClosure.OriginalSource.atom YulangClosure.OriginalSource.AtomKind.finalAnnotationFormation site context;
      { kind := __src.kind, site := __src.site, context := __src.context, operands := __src.operands,
        order := __src.order, names := __src.names, declaration := __src.declaration, annotation := some target,
        annotations := __src.annotations, labels := __src.labels, flag := __src.flag, arity := __src.arity,
        merges := __src.merges, literal := __src.literal, entry := __src.entry, binding := __src.binding }),
    YulangClosure.OriginalSource.Premise.boundary site context
      { site := site, port := YulangClosure.OriginalSource.Port.synthesis }
      { site := site, port := YulangClosure.OriginalSource.Port.writtenTarget }]
YulangClosure.SourceAppDemandIncidenceR89.app_rule : ∀ (mark : YulangClosure.OriginalSource.Mark)
  (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.sourceRules context (YulangClosure.OriginalSource.Source.app mark callee argument) =
    match mark.annotation with
    | none => YulangClosure.SourceAppDemandIncidenceR89.appCore mark.site context callee argument
    | some target =>
      YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.annotation mark.site context
        (YulangClosure.SourceAppDemandIncidenceR89.annotationPremises mark.site context target)
        (YulangClosure.OriginalSource.RuleForest.one
          (YulangClosure.SourceAppDemandIncidenceR89.appCore mark.site context callee argument))
'YulangClosure.SourceAppDemandIncidenceR89.app_rule' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
@YulangClosure.SourceAppDemandIncidenceR89.app_witness_scope_fields : ∀ {Value : Type}
  (environment : YulangClosure.OriginalSource.Environment Value) (site : YulangClosure.OriginalSource.Site)
  (witness : YulangClosure.OriginalSource.ScopedValue Value),
  have next := environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness;
  next.root = environment.root ∧
    next.anchors = environment.anchors ∧
      next.publications = environment.publications ∧
        next.origin = environment.origin ∧
          next.eventPath = environment.eventPath ∧
            next.names = environment.names ∧
              next.frames =
                  environment.frames ++
                    [{ binder := { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic },
                        value := witness, entryPath := environment.eventPath }] ∧
                next.replay = environment.replay ∧ next.initializers = environment.initializers
'YulangClosure.SourceAppDemandIncidenceR89.app_witness_scope_fields' depends on axioms: [propext]
@YulangClosure.SourceAppDemandIncidenceR89.app_core_iff : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (site : YulangClosure.OriginalSource.Site) (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.Judgment kernel environment
      (YulangClosure.SourceAppDemandIncidenceR89.appCore site context callee argument) ↔
    ∃ witness,
      kernel.admitted environment { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness ∧
        (∀ (premise : YulangClosure.OriginalSource.Premise),
            premise ∈ YulangClosure.SourceAppDemandIncidenceR89.appPremises site context callee argument →
              YulangClosure.OriginalSource.Local kernel
                (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
                premise) ∧
          YulangClosure.OriginalSource.SourceJudgment kernel
              (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
              context callee ∧
            YulangClosure.OriginalSource.SourceJudgment kernel
              (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
              context argument
'YulangClosure.SourceAppDemandIncidenceR89.app_core_iff' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
@YulangClosure.SourceAppDemandIncidenceR89.app_derivation_iff : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (mark : YulangClosure.OriginalSource.Mark) (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.SourceJudgment kernel environment context
      (YulangClosure.OriginalSource.Source.app mark callee argument) ↔
    (match mark.annotation with
      | none => True
      | some target =>
        ∀ (premise : YulangClosure.OriginalSource.Premise),
          premise ∈ YulangClosure.SourceAppDemandIncidenceR89.annotationPremises mark.site context target →
            YulangClosure.OriginalSource.Local kernel environment premise) ∧
      ∃ witness,
        kernel.admitted environment { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
            witness ∧
          (∀ (premise : YulangClosure.OriginalSource.Premise),
              premise ∈ YulangClosure.SourceAppDemandIncidenceR89.appPremises mark.site context callee argument →
                YulangClosure.OriginalSource.Local kernel
                  (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                    witness)
                  premise) ∧
            YulangClosure.OriginalSource.SourceJudgment kernel
                (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                  witness)
                context callee ∧
              YulangClosure.OriginalSource.SourceJudgment kernel
                (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                  witness)
                context argument
'YulangClosure.SourceAppDemandIncidenceR89.app_derivation_iff' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

```

### Complete stderr

```text

```

## Independent review of repaired revision 2

Reviewer: `/root/r86_independent_review`, fresh read-only review of the exact revised candidate and handoff.

Verdict: **PASS for second-call pre-execution readiness; successful elaboration remains unverified.** Candidate revision 2 is 8,973 bytes, SHA-256 `27facf01f86f7a0c86e1ef5160667b1e1b283b909a7b0535857abb182c20aeb5`; handoff revision 2 is 12,221 bytes, SHA-256 `fa1043fa1e73adf07deab85243dd76a3559093aa2581fd7d3437ac138f00a2b4`. Reversing only the `appPremises` replacement reconstructs revision 1 exactly. All bytes outside the helper, including all four statements/proofs, are unchanged. Explicit `List.map` now receives the complete parenthesized conditional atom list and preserves atom order, optional singleton-formal clause, operands and both checks. No second Lean call was run by the reviewer.

## Primary exact-input authorization — call 2 of at most 2

Authorized by the independent revision-2 PASS above. The complete first-call failure and its hashes remain recorded earlier in this file. This is the final permitted R89 Lean call.

Flattening recipe is unchanged: exact bytes of `OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, then candidate revision 2; remove only `import YulangClosure.` lines from the latter two; retain `import Std`; concatenate in memory with no intermediate file. Candidate contains the complete helper print and four type/axiom query pairs.

- `OriginalSourceSyntax.lean`: 22,040 bytes, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- `OriginalSourceGeneration.lean`: 66,485 bytes, SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- R89 candidate revision 2: 8,973 bytes, SHA-256 `27facf01f86f7a0c86e1ef5160667b1e1b283b909a7b0535857abb182c20aeb5`.
- Exact flattened stdin: **97,410 bytes**, SHA-256 `aa524e90a0fb92684027d48195961652f402af8c891b434702bc93edd6010141`.
- Pinned executable SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean 4.35.0, args `-j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, hard timeout 120 seconds.
- Amended 34-input manifest SHA-256 `6fe8973a6b5e1aa55d73bb47c85cf4bb11b9a57e1a8b034a167197e7f8697dfa`.

This authorization covers only call 2 and these exact bytes. The complete invocation result, printed types and axiom reports remain pending.


## Primary Lean audit receipt — call 2 of 2

- Start UTC: `2026-10-31T15:13:02.542083+00:00`; end UTC: `2026-10-31T15:13:12.732023+00:00`; elapsed: `10.189919s`; timed out: `false`.
- Executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean 4.35.0; args `-j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`.
- Frozen candidate SHA-256: `27facf01f86f7a0c86e1ef5160667b1e1b283b909a7b0535857abb182c20aeb5`. Flattened stdin: **97410 bytes**, SHA-256 `aa524e90a0fb92684027d48195961652f402af8c891b434702bc93edd6010141`.
- Exit: `1`; captured stdout: 14829 bytes, SHA-256 `1f65f6f7e367731bd8aead9214e2315fab261db25dcf7ffe07f57669ba86b1c5`; stderr: 0 bytes, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. Cumulative child `ru_maxrss` after both calls: 904584 KiB; this is not isolated per-invocation RSS.

### Complete stdout

```text
<stdin>:1707:56: error: Tactic `rfl` failed: The left-hand side
  annotated mark context
    (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
      (RuleTree.rule Rule.app mark.site context
        (premises
            ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
              if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
            mark.site context [callee.site, argument.site] ++
          [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
              (endpoint mark.site Port.descriptor),
            check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
              (endpoint mark.site Port.synthesis)])
        (RuleForest.two (sourceRules context callee) (sourceRules context argument))))
is not definitionally equal to the right-hand side
  match none with
  | none => appCore mark.site context callee argument
  | some target =>
    RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
      (RuleForest.one (appCore mark.site context callee argument))

case none
mark : Mark
context : Context
callee argument : Source Category.expression
⊢ annotated mark context
      (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
        (RuleTree.rule Rule.app mark.site context
          (premises
              ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                  AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
              mark.site context [callee.site, argument.site] ++
            [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
                (endpoint mark.site Port.descriptor),
              check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
                (endpoint mark.site Port.synthesis)])
          (RuleForest.two (sourceRules context callee) (sourceRules context argument)))) =
    match none with
    | none => appCore mark.site context callee argument
    | some target =>
      RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
        (RuleForest.one (appCore mark.site context callee argument))
<stdin>:1707:56: error: Tactic `rfl` failed: The left-hand side
  annotated mark context
    (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
      (RuleTree.rule Rule.app mark.site context
        (premises
            ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
              if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
            mark.site context [callee.site, argument.site] ++
          [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
              (endpoint mark.site Port.descriptor),
            check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
              (endpoint mark.site Port.synthesis)])
        (RuleForest.two (sourceRules context callee) (sourceRules context argument))))
is not definitionally equal to the right-hand side
  match some val✝ with
  | none => appCore mark.site context callee argument
  | some target =>
    RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
      (RuleForest.one (appCore mark.site context callee argument))

case some
mark : Mark
context : Context
callee argument : Source Category.expression
val✝ : Annotation
⊢ annotated mark context
      (RuleTree.existsE { site := mark.site, kind := BinderKind.viewLogic }
        (RuleTree.rule Rule.app mark.site context
          (premises
              ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                  AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin] else [])
              mark.site context [callee.site, argument.site] ++
            [check CheckMode.value mark.site context (endpoint callee.site Port.returnedValue)
                (endpoint mark.site Port.descriptor),
              check CheckMode.computation mark.site context (endpoint mark.site Port.callableImage)
                (endpoint mark.site Port.synthesis)])
          (RuleForest.two (sourceRules context callee) (sourceRules context argument)))) =
    match some val✝ with
    | none => appCore mark.site context callee argument
    | some target =>
      RuleTree.rule Rule.annotation mark.site context (annotationPremises mark.site context target)
        (RuleForest.one (appCore mark.site context callee argument))
def YulangClosure.SourceAppDemandIncidenceR89.appPremises : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
      YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
        List YulangClosure.OriginalSource.Premise :=
fun site context callee argument =>
  List.map
      (fun kind =>
        YulangClosure.OriginalSource.Premise.atom
          (YulangClosure.OriginalSource.atom kind site context [callee.site, argument.site]))
      ([YulangClosure.OriginalSource.AtomKind.descriptorFormation,
          YulangClosure.OriginalSource.AtomKind.wholeArgumentCompatibility,
          YulangClosure.OriginalSource.AtomKind.completeCallCertificate,
          YulangClosure.OriginalSource.AtomKind.sourceCallIncidence,
          YulangClosure.OriginalSource.AtomKind.callableImage] ++
        if YulangClosure.OriginalSource.singletonFormalCall context callee argument = true then
          [YulangClosure.OriginalSource.AtomKind.roleAndInitialCallOrigin]
        else []) ++
    [YulangClosure.OriginalSource.Premise.checking
        { mode := YulangClosure.OriginalSource.CheckMode.value, site := site, context := context,
          lower := { site := callee.site, port := YulangClosure.OriginalSource.Port.returnedValue },
          upper := { site := site, port := YulangClosure.OriginalSource.Port.descriptor } },
      YulangClosure.OriginalSource.Premise.checking
        { mode := YulangClosure.OriginalSource.CheckMode.computation, site := site, context := context,
          lower := { site := site, port := YulangClosure.OriginalSource.Port.callableImage },
          upper := { site := site, port := YulangClosure.OriginalSource.Port.synthesis } }]
def YulangClosure.SourceAppDemandIncidenceR89.appCore : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
      YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
        YulangClosure.OriginalSource.RuleTree :=
fun site context callee argument =>
  YulangClosure.OriginalSource.RuleTree.existsE
    { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
    (YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.app site context
      (YulangClosure.SourceAppDemandIncidenceR89.appPremises site context callee argument)
      (YulangClosure.OriginalSource.RuleForest.two (YulangClosure.OriginalSource.sourceRules context callee)
        (YulangClosure.OriginalSource.sourceRules context argument)))
def YulangClosure.SourceAppDemandIncidenceR89.annotationPremises : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Annotation → List YulangClosure.OriginalSource.Premise :=
fun site context target =>
  [YulangClosure.OriginalSource.Premise.atom
      (have __src :=
        YulangClosure.OriginalSource.atom YulangClosure.OriginalSource.AtomKind.finalAnnotationFormation site context;
      { kind := __src.kind, site := __src.site, context := __src.context, operands := __src.operands,
        order := __src.order, names := __src.names, declaration := __src.declaration, annotation := some target,
        annotations := __src.annotations, labels := __src.labels, flag := __src.flag, arity := __src.arity,
        merges := __src.merges, literal := __src.literal, entry := __src.entry, binding := __src.binding }),
    YulangClosure.OriginalSource.Premise.boundary site context
      { site := site, port := YulangClosure.OriginalSource.Port.synthesis }
      { site := site, port := YulangClosure.OriginalSource.Port.writtenTarget }]
YulangClosure.SourceAppDemandIncidenceR89.app_rule : ∀ (mark : YulangClosure.OriginalSource.Mark)
  (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.sourceRules context (YulangClosure.OriginalSource.Source.app mark callee argument) =
    match mark.annotation with
    | none => YulangClosure.SourceAppDemandIncidenceR89.appCore mark.site context callee argument
    | some target =>
      YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.annotation mark.site context
        (YulangClosure.SourceAppDemandIncidenceR89.annotationPremises mark.site context target)
        (YulangClosure.OriginalSource.RuleForest.one
          (YulangClosure.SourceAppDemandIncidenceR89.appCore mark.site context callee argument))
'YulangClosure.SourceAppDemandIncidenceR89.app_rule' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
@YulangClosure.SourceAppDemandIncidenceR89.app_witness_scope_fields : ∀ {Value : Type}
  (environment : YulangClosure.OriginalSource.Environment Value) (site : YulangClosure.OriginalSource.Site)
  (witness : YulangClosure.OriginalSource.ScopedValue Value),
  have next := environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness;
  next.root = environment.root ∧
    next.anchors = environment.anchors ∧
      next.publications = environment.publications ∧
        next.origin = environment.origin ∧
          next.eventPath = environment.eventPath ∧
            next.names = environment.names ∧
              next.frames =
                  environment.frames ++
                    [{ binder := { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic },
                        value := witness, entryPath := environment.eventPath }] ∧
                next.replay = environment.replay ∧ next.initializers = environment.initializers
'YulangClosure.SourceAppDemandIncidenceR89.app_witness_scope_fields' depends on axioms: [propext]
@YulangClosure.SourceAppDemandIncidenceR89.app_core_iff : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (site : YulangClosure.OriginalSource.Site) (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.Judgment kernel environment
      (YulangClosure.SourceAppDemandIncidenceR89.appCore site context callee argument) ↔
    ∃ witness,
      kernel.admitted environment { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness ∧
        (∀ (premise : YulangClosure.OriginalSource.Premise),
            premise ∈ YulangClosure.SourceAppDemandIncidenceR89.appPremises site context callee argument →
              YulangClosure.OriginalSource.Local kernel
                (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
                premise) ∧
          YulangClosure.OriginalSource.SourceJudgment kernel
              (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
              context callee ∧
            YulangClosure.OriginalSource.SourceJudgment kernel
              (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
              context argument
'YulangClosure.SourceAppDemandIncidenceR89.app_core_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
@YulangClosure.SourceAppDemandIncidenceR89.app_derivation_iff : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (mark : YulangClosure.OriginalSource.Mark) (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.SourceJudgment kernel environment context
      (YulangClosure.OriginalSource.Source.app mark callee argument) ↔
    (match mark.annotation with
      | none => True
      | some target =>
        ∀ (premise : YulangClosure.OriginalSource.Premise),
          premise ∈ YulangClosure.SourceAppDemandIncidenceR89.annotationPremises mark.site context target →
            YulangClosure.OriginalSource.Local kernel environment premise) ∧
      ∃ witness,
        kernel.admitted environment { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
            witness ∧
          (∀ (premise : YulangClosure.OriginalSource.Premise),
              premise ∈ YulangClosure.SourceAppDemandIncidenceR89.appPremises mark.site context callee argument →
                YulangClosure.OriginalSource.Local kernel
                  (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                    witness)
                  premise) ∧
            YulangClosure.OriginalSource.SourceJudgment kernel
                (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                  witness)
                context callee ∧
              YulangClosure.OriginalSource.SourceJudgment kernel
                (environment.extend { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
                  witness)
                context argument
'YulangClosure.SourceAppDemandIncidenceR89.app_derivation_iff' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

```

### Complete stderr

```text

```

## Independent review of the R89 source result

Reviewer: `/root/r86_independent_review`, fresh read-only review.

Verdict: **PASS for the bounded source result; no A/B, counterexample or production closure.** The reviewer matched the 30,426-byte source handoff SHA-256 `74d5815c3d502ed2da2b1b50bf7edb6378f6d773fe2e6190efc6e2e335db5539` and all 34 amended manifest pins. The recipe→native demand→optional introduction→`ScopedDemand` chain and equal-birth SCC filtering are accurately described. `NO_SAFE_CODE_SLICE` is justified because the actual original whole registered interface, complete Gen-Call-0 tuple and single source telescope remain unsupplied. The report retains Ref/helper extraction and sealing lifecycle as open qualification premises, and does not claim stale-cache behavior or a source counterexample. No tests/build/Lean were run by the reviewer.

## R89 bounded outcome

Status: **CLOSED_BOUNDED_RESULT**. The source lane established actual native constructor and birth-qualification evidence, but no safe Rust code slice follows while original Call incidence is missing. The proof lane used both authorized Lean calls. Call 1 failed because candidate revision 1's `.map` application was parsed incorrectly. Revision 2 fixed that helper, but call 2 still failed at `app_rule`: the case split over `mark.annotation` did not reduce the annotation projection in `mark`, so `rfl` failed. This is the sole Lean error in call 2. The helper now elaborates, but the four-theorem candidate is not accepted as a whole: `app_rule` and `app_derivation_iff` report error-recovery `sorryAx`; `app_witness_scope_fields` reports `propext`; `app_core_iff` reports `propext, Classical.choice, Quot.sound`. The complete types, axiom reports and both complete stdout/stderr receipts are retained above. No R89 Lean call remains.

The exact next proof repair is to make the `app_rule` annotation split rewrite the projection on the original `mark` (for example, a named equation plus simplification), then re-review and reauthorize a new bounded call under a new sprint. The original four theorem statements, source/native incidence, A/B, Rust implementation and production remain open.
