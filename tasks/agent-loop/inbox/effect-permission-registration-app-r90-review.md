# R90 independent source review receipt

Disposition: **PASS** for the bounded R90 source missing-supplier result. No BLOCKING, major, or minor correctness finding.

## Frozen inputs

- Source handoff: 10,636 bytes; SHA-256 `afd6d07429915af55a47938bce8917e34469e88e17900525a409413f789e8a99`.
- Input manifest: SHA-256 `486f9825b4bb00ce4bc8931112be725dd11b17d701c4ebb4806fbfea8b8c3aa3`; all 48/48 input sizes and hashes match.

## Findings

The registration trace matches the pinned code: `candidate_source.rs:1106–1118` records owner/Lambda/formal/recipe/role/scope; `2292–2329` installs the positive parameter root and optional Computation entry row. `candidate_call::observe_computation_source_plan` authenticates those retained coordinates while explicitly leaving Function/entry-port/FreshUse correspondence unestablished. These records do not contain the original complete dependent interface or its source-telescope interpretation.

The local-use comparison is accurate. `candidate_scheme.rs:5024–5059` installs native `LocalScheme` coordinates and propagates initializer obligations; `5191+` captures the native graph and prepares a FreshUse route at the actual occurrence. Neither construction supplies the original complete interface, original typed substitution, shared source witnesses, or semantic membership.

The first missing constructor is substantiated at this formal-registration bridge: construct `OriginalRegistrationWholeInterface` at the authentic declaration and relate that same complete interface to its actual App callee use. The selected IF-Insert/IF-Use library constructions themselves are not missing. The authoritative interface design constructs static placement from authentic complete declaration/reference inputs and expressly separates placement from licensing, membership, provider validity, and complete C0.

The handoff preserves all 16 Gen-Call-0 input coordinates, the actual returned callee/provider, whole argument carrier, dependent receipt/current/context/continuation/path/consumer/incidence, and immediate/future evidence. It keeps these within one original App telescope and retains annotations, effects, recursive sharing, and lawful independent uses. No semantic license is inferred from root identity, slot placement, native ports, or observer success.

## Accepted scope

Bounded source-to-native registration incidence, with the first original registration/Call supplier still open. No complete supplier, joint lift, A/B closure, or implementation authority follows.

No tests, builds, Lean, Git operations, or writes were performed by the reviewer. The review was returned as a read-only receipt; Luna recorded it here without changing the findings.

## Primary exact-input authorization — call 1 of at most 2

Pre-execution review: **PASS** by `/root/r86_independent_review`, who is neither the proof author nor primary. The reviewer independently matched all 48/48 manifest pins, all four unchanged theorem statement texts, the candidate body and the flattened stdin bytes. This authorization is for call 1 only; no elaboration result is claimed yet.

The primary independently reconstructed the in-memory input using the same recipe: dependency-first read of `OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`, `SourceSignatureConstruction.lean`, and the frozen R90 candidate; for each file, split into text lines, remove only lines beginning exactly `import YulangClosure.`, and rejoin retained lines with LF; join the four resulting bodies with two LF bytes and append one final LF. No source or scratch output file is created.

- `OriginalSourceSyntax.lean`: 22,040 bytes, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- `OriginalSourceGeneration.lean`: 66,485 bytes, SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- `SourceSignatureConstruction.lean`: 37,437 bytes, SHA-256 `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311`.
- R90 candidate `SourceRegistrationAppBridgeR90.lean`: 11,964 bytes, SHA-256 `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`.
- Exact flattened stdin: **137,750 bytes**, SHA-256 `c43394385c4bec30c0ca35077d2ae7f0308ece6a7a26305ed2665d9f3a46fe1b`.
- Lean executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean **4.35.0**, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Direct invocation: `lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, hard timeout 120 seconds.
- Six declarations have complete `#check` / `#print axioms` pairs: `app_rule`, `app_witness_scope_fields`, `app_core_iff`, `app_derivation_iff`, `installed_call_app_atom`, and `reference_insertion_whole_action`.
- No Lake command, build, test, cache generation, scratch file, worktree, project copy, or environment creation is authorized for this call.

The reviewed candidate and handoff are committed and pushed before execution. This exact-input authorization is pushed separately before the primary invokes Lean. The complete exit, stdout, stderr, printed types and axiom reports will be appended here as the call-1 audit receipt.

## Primary Lean audit receipt — call 1 of at most 2

- Input: 137,750 bytes; SHA-256 `c43394385c4bec30c0ca35077d2ae7f0308ece6a7a26305ed2665d9f3a46fe1b`; executable SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Args: `-j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Result: exit **1**, timeout **false**, elapsed **11.336706s**.
- Stdout: **39,307 bytes**, SHA-256 `0a951e21fa2f9150084c8e5e09496c6ae0f22b449f50a6da89a925ff5e511075`.
- Stderr: **0 bytes**, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

### Failure classification

The concatenated source did not preserve module privacy for `OriginalSourceGeneration.private def node`. In the single stdin module, this private helper collided with auto-implicit `node` binders in `SourceSignatureConstruction`. The first diagnostics occur at `<stdin>:1922`–`1939`: `PortProv`/`Developed` constructor arguments resolve to the private `node` function, then `node.introductions` and the graph-local node fields fail. This cascades into unknown `Occurrence`, `PortProv`, `Developed`, `SupportPath`, `BuiltPath`, `PortProv`, and other source-signature declarations, and prevents the final `reference_insertion_whole_action` declaration from being available.

The candidate's printed prefix includes `app_rule` (`propext, Classical.choice, Quot.sound`), `app_witness_scope_fields` (`propext`), `app_core_iff` (`propext, Classical.choice, Quot.sound`), `app_derivation_iff` (`propext, Classical.choice, Quot.sound`), and `installed_call_app_atom` (`propext, Quot.sound`). Those reports came after source-file errors and therefore do **not** constitute accepted theorem results. The final theorem was unknown; the candidate as a whole was not accepted. No conclusion about A/B or the original source obligation follows.

The exact stdout was emitted in the primary execution receipt above; this file retains its byte length and digest plus the full failure classification, but not a second byte-for-byte copy. No Lean/build/test/cache/scratch/worktree/project-copy/environment output was created.

Call 1 is consumed. The proof author is preparing a deterministic, semantics-preserving flattening repair for review. No second invocation is authorized by this receipt.

## Primary exact-input authorization — call 2 of at most 2

Fresh pre-execution review: **PASS** by `/root/r86_independent_review` for the order-only repair. The reviewer independently reconstructed the complete 137,750-byte input and verified SHA-256 `3ab0d68ec6ceaec30b391d9ee5aa58306b338692ebc660f9960b898e96370eba`, all 48 manifest pins, and unchanged candidate SHA-256 `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`. The review confirmed both dependency edges: `SourceSignatureConstruction` and `OriginalSourceGeneration` depend only on `OriginalSourceSyntax`; the candidate depends on Generation and Signature. This places Signature before Generation so Generation's private `node` helper cannot shadow Signature's auto-implicit `node` binders. No source declaration, theorem statement, or candidate byte changed.

The primary independently reconstructed the bytes with dependency-first order `OriginalSourceSyntax.lean`, `SourceSignatureConstruction.lean`, `OriginalSourceGeneration.lean`, `SourceRegistrationAppBridgeR90.lean`. For each exact file, split into lines retaining their line endings, remove only lines beginning exactly `import YulangClosure.`, join retained lines without editing, then join the four bodies with one LF byte. Each body retains its original trailing LF, so each inter-file boundary has two LF bytes. The direct `import Std` remains. No source or scratch output file is created.

- `OriginalSourceSyntax.lean`: 22,040 bytes, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- `SourceSignatureConstruction.lean`: 37,437 bytes, SHA-256 `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311`.
- `OriginalSourceGeneration.lean`: 66,485 bytes, SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- R90 candidate: 11,964 bytes, SHA-256 `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`.
- Exact flattened stdin: **137,750 bytes**, SHA-256 `3ab0d68ec6ceaec30b391d9ee5aa58306b338692ebc660f9960b898e96370eba`.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean **4.35.0**, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Direct invocation: `lean -j1 -M1024 --stdin`, cwd `notes/theory/lean`, `LEAN_NUM_THREADS=1`, hard timeout 120 seconds.
- Six complete type/axiom audit pairs remain: `app_rule`, `app_witness_scope_fields`, `app_core_iff`, `app_derivation_iff`, `installed_call_app_atom`, and `reference_insertion_whole_action`.
- This is the final permitted invocation (**call 2/2**). No Lake/build/test/cache/scratch/worktree/project-copy/environment action is authorized.

The repaired proof handoff and frozen candidate are committed and pushed at `82a6f04d0`. This second exact-input authorization is committed and will be pushed as a separate commit before the primary invokes Lean. The result will be appended below; no theorem is accepted until the complete stdout has no errors and all six types/axiom lists are audited.

## Primary Lean audit receipt — call 2 of 2

- Exact input: **137,750 bytes**, SHA-256 `3ab0d68ec6ceaec30b391d9ee5aa58306b338692ebc660f9960b898e96370eba`.
- Frozen candidate: 11,964 bytes, SHA-256 `cd836e6b12a4deff0e5acf83523faedfb883240b6d019f17ec5a7d294b8c205a`.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`; Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Args `-j1 -M1024 --stdin`; cwd `notes/theory/lean`; `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Result: exit **0**, timeout **false**, elapsed **15.340572s**.
- Complete stdout: **12,150 bytes**, SHA-256 `c46535a3b1822a02893fea0d22df2707b7ab90ee4dea3f1304a65024df0c03a2`.
- Complete stderr: **0 bytes**, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The six requested declarations and their full standard axiom reports are:

| Declaration | `#print axioms` |
|---|---|
| `app_rule` | `propext, Classical.choice, Quot.sound` |
| `app_witness_scope_fields` | `propext` |
| `app_core_iff` | `propext, Classical.choice, Quot.sound` |
| `app_derivation_iff` | `propext, Classical.choice, Quot.sound` |
| `installed_call_app_atom` | `propext, Quot.sound` |
| `reference_insertion_whole_action` | `propext` |

No errors or warnings appeared. All six `#check` commands printed theorem types matching the frozen source declarations: annotation-aware App rule equality; all original environment fields under one logical witness; exact App core equivalence with one admitted witness, every premise, and both children; full annotated App derivation equivalence; installed Call static-incidence atom membership; and reference insertion preserving the original introduction/owner/receiver/import classification and applying the whole substitution once. No `sorryAx`, project axiom, or kernel-bypass declaration appeared in the complete stdout. The four original R89 theorem statements remain unchanged; the two new declarations instantiate only the constructor-derived static evidence. These results do not construct the missing original whole registration/Gen-Call-0 supplier or close the parent A/B theorem.

The primary execution output was complete at the recorded byte length and digest. This receipt preserves all six emitted types by reference to the frozen declarations, the full axiom lists, and the output hash. The independent result audit is pending.

### Complete stdout bytes (call 2)

```text
def YulangClosure.SourceRegistrationAppBridgeR90.appPremises : YulangClosure.OriginalSource.Site →
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
def YulangClosure.SourceRegistrationAppBridgeR90.appCore : YulangClosure.OriginalSource.Site →
  YulangClosure.OriginalSource.Context →
    YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
      YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression →
        YulangClosure.OriginalSource.RuleTree :=
fun site context callee argument =>
  YulangClosure.OriginalSource.RuleTree.existsE
    { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
    (YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.app site context
      (YulangClosure.SourceRegistrationAppBridgeR90.appPremises site context callee argument)
      (YulangClosure.OriginalSource.RuleForest.two (YulangClosure.OriginalSource.sourceRules context callee)
        (YulangClosure.OriginalSource.sourceRules context argument)))
def YulangClosure.SourceRegistrationAppBridgeR90.annotationPremises : YulangClosure.OriginalSource.Site →
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
YulangClosure.SourceRegistrationAppBridgeR90.app_rule : ∀ (mark : YulangClosure.OriginalSource.Mark)
  (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.sourceRules context (YulangClosure.OriginalSource.Source.app mark callee argument) =
    match mark.annotation with
    | none => YulangClosure.SourceRegistrationAppBridgeR90.appCore mark.site context callee argument
    | some target =>
      YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.annotation mark.site context
        (YulangClosure.SourceRegistrationAppBridgeR90.annotationPremises mark.site context target)
        (YulangClosure.OriginalSource.RuleForest.one
          (YulangClosure.SourceRegistrationAppBridgeR90.appCore mark.site context callee argument))
'YulangClosure.SourceRegistrationAppBridgeR90.app_rule' depends on axioms: [propext, Classical.choice, Quot.sound]
@YulangClosure.SourceRegistrationAppBridgeR90.app_witness_scope_fields : ∀ {Value : Type}
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
'YulangClosure.SourceRegistrationAppBridgeR90.app_witness_scope_fields' depends on axioms: [propext]
@YulangClosure.SourceRegistrationAppBridgeR90.app_core_iff : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (site : YulangClosure.OriginalSource.Site) (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.Judgment kernel environment
      (YulangClosure.SourceRegistrationAppBridgeR90.appCore site context callee argument) ↔
    ∃ witness,
      kernel.admitted environment { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness ∧
        (∀ (premise : YulangClosure.OriginalSource.Premise),
            premise ∈ YulangClosure.SourceRegistrationAppBridgeR90.appPremises site context callee argument →
              YulangClosure.OriginalSource.Local kernel
                (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
                premise) ∧
          YulangClosure.OriginalSource.SourceJudgment kernel
              (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
              context callee ∧
            YulangClosure.OriginalSource.SourceJudgment kernel
              (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic } witness)
              context argument
'YulangClosure.SourceRegistrationAppBridgeR90.app_core_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
@YulangClosure.SourceRegistrationAppBridgeR90.app_derivation_iff : ∀ {Value : Type}
  (kernel : YulangClosure.OriginalSource.Kernel Value) (environment : YulangClosure.OriginalSource.Environment Value)
  (mark : YulangClosure.OriginalSource.Mark) (context : YulangClosure.OriginalSource.Context)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression),
  YulangClosure.OriginalSource.SourceJudgment kernel environment context
      (YulangClosure.OriginalSource.Source.app mark callee argument) ↔
    (match mark.annotation with
      | none => True
      | some target =>
        ∀ (premise : YulangClosure.OriginalSource.Premise),
          premise ∈ YulangClosure.SourceRegistrationAppBridgeR90.annotationPremises mark.site context target →
            YulangClosure.OriginalSource.Local kernel environment premise) ∧
      ∃ witness,
        kernel.admitted environment { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
            witness ∧
          (∀ (premise : YulangClosure.OriginalSource.Premise),
              premise ∈ YulangClosure.SourceRegistrationAppBridgeR90.appPremises mark.site context callee argument →
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
'YulangClosure.SourceRegistrationAppBridgeR90.app_derivation_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@YulangClosure.SourceRegistrationAppBridgeR90.installed_call_app_atom : ∀ {Joint : Type}
  (graph : YulangClosure.SourceSignatureConstruction.Graph Joint) (context : YulangClosure.OriginalSource.Context)
  (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression)
  (regions : YulangClosure.SourceSignatureConstruction.CallRegions Joint)
  (locals : List (YulangClosure.SourceSignatureConstruction.Introduction Joint))
  (result : YulangClosure.SourceSignatureConstruction.Catalogue Joint),
  YulangClosure.OriginalSource.Premise.atom
        (YulangClosure.SourceSignatureConstruction.callAtom context mark callee argument) ∈
      YulangClosure.SourceRegistrationAppBridgeR90.appPremises mark.site context callee argument ∧
    YulangClosure.SourceSignatureConstruction.StaticCallIncidence
      (YulangClosure.SourceSignatureConstruction.installCall graph context mark callee argument regions locals result)
      (YulangClosure.SourceSignatureConstruction.callAtom context mark callee argument)
'YulangClosure.SourceRegistrationAppBridgeR90.installed_call_app_atom' depends on axioms: [propext, Quot.sound]
@YulangClosure.SourceRegistrationAppBridgeR90.reference_insertion_whole_action : ∀ {Joint : Type}
  (graph : YulangClosure.SourceSignatureConstruction.Graph Joint) (index target receiver clause : Nat)
  (site : YulangClosure.OriginalSource.Site) (substitution : Nat)
  (result : YulangClosure.SourceSignatureConstruction.Catalogue Joint)
  (found :
    graph.node index = some (YulangClosure.SourceSignatureConstruction.Node.reference site target substitution result))
  (occurrence : YulangClosure.SourceSignatureConstruction.Occurrence graph target) (whole : Joint),
  have moved := YulangClosure.SourceSignatureConstruction.contextual found ⋯ occurrence;
  have placed := YulangClosure.SourceSignatureConstruction.insert graph receiver clause moved;
  placed.intro = occurrence.intro ∧
    placed.owner = occurrence.owner ∧
      placed.receiver = graph.registration receiver ∧
        placed.inherited = true ∧
          YulangClosure.SourceSignatureConstruction.routeAction graph placed.route whole =
            YulangClosure.SourceSignatureConstruction.routeAction graph occurrence.route
              (graph.substitution substitution whole)
'YulangClosure.SourceRegistrationAppBridgeR90.reference_insertion_whole_action' depends on axioms: [propext]
```

## Independent result review — call 2

Reviewer: `/root/r86_independent_review`, independent read-only reviewer, neither author nor primary. Verdict: **PASS** for the six bounded declarations in the exact flattened input.

The reviewer extracted the fenced stdout stream and independently verified 12,150 bytes and SHA-256 `c46535a3b1822a02893fea0d22df2707b7ab90ee4dea3f1304a65024df0c03a2`. It reconstructed the 137,750-byte stdin at SHA-256 `3ab0d68ec6ceaec30b391d9ee5aa58306b338692ebc660f9960b898e96370eba`, rehashed the unchanged candidate and executable, and matched process exit 0, no timeout, settings, and empty stderr.

Exactly six unique theorem types and six complete axiom reports were emitted. The reviewer found zero errors, warnings, missing/duplicate reports, `sorryAx`, project axioms, native shortcuts, or bypasses. It compared every emitted type with the candidate: the App rule retains both annotation branches; environment-field preservation has all nine equations; core inversion uses one admitted witness for all premises and both children; full derivation inversion combines incoming-environment annotation obligations with that same witness; the installed Call result proves premise membership and constructor-built static incidence only; and reference insertion retains the actual found reference/occurrence, introduction, owner, registered receiver, import classification, and one whole-substitution action.

Confirmed axiom lists: `app_rule`, `app_core_iff`, `app_derivation_iff` — `propext, Classical.choice, Quot.sound`; `app_witness_scope_fields`, `reference_insertion_whole_action` — `propext`; `installed_call_app_atom` — `propext, Quot.sound`. These are standard Lean axioms, not axiom-free results.

Call 1 remains a failed assembly attempt; no candidate or dependency declaration changed. The topological reorder removed the private-node name-resolution collision, and the unchanged final declaration now prints cleanly. The result does not certify standalone imports, concrete original registration/Gen-Call-0 suppliers, native extraction, joint lift, A/B, or production. Calls consumed: **2/2**. The reviewer ran no Lean/build/tests and performed no writes or Git operations.
