# R88 proof handoff — exact App inversion and missing extrusion incidence

Assignment: `R88-PROOF`, handoff revision **1**, candidate revision **1**.  
Sprint: `SOURCE-SCOPED-JOINT-LIFT/20261031-R88`, contract revision 1, SHA-256 `e6adf9efbcea3d07aa3b419c52c5ec878d3852afa3231047cb1e7f2a0fa8304d`.  
Manifest: `source-scoped-joint-lift-20261031-r88-inputs.json`, SHA-256 `239497900445ae2b3b8e546f6f080db1bf1ec7dc52b9ee1b28bbede4f3c70353`.  
Admission baseline supplied by Luna: `8fd0da905449b5f4214f0ec5aa487075c03060a9`; contract/manifest source baseline remains `93fe63707d3a889f09284088413e2fc233aae468`.

Author/session: `/root/r88_proof`, current R88 leaf assignment from `/root`. Requested role: registered `lean_prover`; requested model/effort **UNKNOWN** in the received packet; observed runtime model/effort **UNKNOWN**. No descendants or contributing coauthors. No independent certification is claimed.

Outcome: **constructed-but-unchecked structural candidate; exact source/native obstruction**. This is the packet's obstruction outcome, not a source-scoped joint lift or source-qualified counterexample. Writes are stopped on the two leased paths.

## Parent and source correspondence

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, 7. It quantifies over every supported original source program, lawful finite Simple-sub history and actual retained extrusion occurrence, retaining all original typing/principal coverage, scopes, recursive monomorphic sharing, complete Call/effects, correlated evidence and lawful independent uses. The current correction is `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6: immutable source Value birth, SCC in each birth-induced graph, actual retained polar pairs. Its §6 expressly leaves the source-scoped joint lift open.

Source authority: selected `notes/design/2026-10-08-source-generalize-definition.md` §§2–3; selected construction `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1–3.4, 4, 5.1–5.2, 6–7. L1–L5 are original local premises, not established concrete instances. The original intrusion manuscript §3 does not import the paper's non-let principality sketch as the leveled/Call/effect theorem. No external paper result or research draft is used as a new semantic law.

Inspected exact source owners:

- `OriginalSource.Source.app`, `AtomKind`, `Atom`, `Endpoint`, `RuleTree`, and the complete raw syntax inventory in `OriginalSourceSyntax.lean`.
- `OriginalSource.sourceRules` App equation at lines 111–123; `Kernel`, `Local`, `Judgment` and `Environment.extend` in `OriginalSourceGeneration.lean`. The exact App is one admitted ViewLogic witness, all five ordinary atoms, the conditional singleton-formal atom, the returned-callee/descriptor Value check, callable-image/synthesis Computation check and both whole source children.
- `OriginalSourceInterpretation.Sorts`, `Fiber`, `Event`, `Inputs`, `SourceAssignment`, `literalKernel`, and `nameKernel`. Literal/Name interpretations do not provide the missing native App equation; arbitrary remaining `Kernel.atom` clauses cannot be treated as the concrete source law.
- `SourcePrincipalTransport.program_call_owners`, `h_call_complete_rule`, `recursive_call_complete_rule`, `recursive_field_retains_h_suffix`, `source_owners_after_all_frames`, `source_subjects_after_all_frames`, `h_return_supplies_current_receiver`. They preserve actual raw Apps and returned-callee owners, including the original Return/rebind suffix and monomorphic recursive Name. The module explicitly leaves the native ExtrudeFresh/source registry map open.
- `OriginalExtrusionWork.Operation`, `Parent`, `State.retain`, `functionKeys`, `initializeLocal`, `start`; `OriginalExtrusionFibers.metadata`, `transportKey`, `transport_key_exact`, `transferred_fiber_exact`. Native fields/pair retention and four-port polarity are present; no common source-telescope interpretation is supplied.
- `OriginalScopedClosure.Position`, `Occurrence.reference`, `allocate`, `Program.copy`, `Publication`, `prepare`, `openPublication`, `opened_readback`, `opened_restore_fields`, `opened_source_residual`. They retain source scope/reference/publication data and erase back to the original program; they do not establish a native coordinate interpretation or semantic fixed/template dependency classification.
- `SimpleSub.OriginalPrincipality.FiberConstant`, `joint_descent_iff_fiber_constant`, `joint_solution_coverage_iff`: the algebraic fiber criterion remains conditional. `OriginalSourceValueEntryAdmission.independent_receive_fields` and `receipt_decoder_uses_supplied_current` likewise supply no native actual-Receive admission law. R87 closes its finite readers only.

## Frozen artifact and intended declarations

Only artifact: `notes/theory/lean/YulangClosure/SourceScopedJointLiftR88.lean`, **9,755 bytes**, SHA-256 **`1421c7924fb93b957612b366942adefeaeca44a1b51daad9266d43016916facd`**. Its sole direct project import is `YulangClosure.OriginalSourceGeneration`; the project source dependency cone is that file plus `OriginalSourceSyntax.lean`, then pinned `Std`. No root import is edited.

All names below have prefix `YulangClosure.SourceScopedJointLiftR88`. The following are **intended source signatures, not printed checker output**. `appPremises` is the literal complete source premise list, `appCore` the original ViewLogic/App/children tree, and `annotationPremises` the original formation/boundary list; their definitions and every declaration type/axiom query are in the frozen file.

```lean
app_rule (mark : Mark) (context : Context)
    (callee argument : Source .expression) :
  sourceRules context (.app mark callee argument) =
    match mark.annotation with
    | none => appCore mark.site context callee argument
    | some target => .rule .annotation mark.site context
        (annotationPremises mark.site context target)
        (.one (appCore mark.site context callee argument))

app_witness_scope_fields {Value : Type} (environment : Environment Value)
    (site : Site) (witness : ScopedValue Value) :
  let next := environment.extend ⟨site, .viewLogic, 0⟩ witness
  next.root = environment.root ∧ next.anchors = environment.anchors ∧
  next.publications = environment.publications ∧ next.origin = environment.origin ∧
  next.eventPath = environment.eventPath ∧ next.names = environment.names ∧
  next.frames = environment.frames ++ [⟨⟨site, .viewLogic, 0⟩, witness, environment.eventPath⟩] ∧
  next.replay = environment.replay ∧ next.initializers = environment.initializers

app_core_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (site : Site) (context : Context)
    (callee argument : Source .expression) :
  Judgment kernel environment (appCore site context callee argument) ↔
    ∃ witness : ScopedValue Value,
      kernel.admitted environment ⟨site, .viewLogic, 0⟩ witness ∧
      (∀ premise ∈ appPremises site context callee argument,
        Local kernel (environment.extend ⟨site, .viewLogic, 0⟩ witness) premise) ∧
      SourceJudgment kernel (environment.extend ⟨site, .viewLogic, 0⟩ witness) context callee ∧
      SourceJudgment kernel (environment.extend ⟨site, .viewLogic, 0⟩ witness) context argument

app_derivation_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (mark : Mark) (context : Context)
    (callee argument : Source .expression) :
  SourceJudgment kernel environment context (.app mark callee argument) ↔
    (match mark.annotation with
     | none => True
     | some target => ∀ premise ∈ annotationPremises mark.site context target,
         Local kernel environment premise) ∧
    ∃ witness : ScopedValue Value,
      kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ witness ∧
      (∀ premise ∈ appPremises mark.site context callee argument,
        Local kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ witness) premise) ∧
      SourceJudgment kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ witness) context callee ∧
      SourceJudgment kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ witness) context argument
```

Represented: arbitrary original App operands/context/environment/payload, both annotation cases, both singleton-formal cases, every generated local clause, both checking modes, both source children at one witness and every Environment field. Nested syntax remains the original `Source`/`sourceRules`; there is no smaller accepted language. This is one induction case, not an induction over the whole source language.

Not established: any concrete full-App Kernel instance, actual source/native demand correspondence, immutable-birth qualification, selected pair interpretation, simultaneous substitution/fiber constancy, semantic effect transport, publication dependency classification, lawful-use allocation transport, whole-language soundness/principality/progress/termination or production. No source-reachable counterexample is asserted.

## First remaining premise and parent application

**R88-SOURCE-EXTRUSION-INCIDENCE-1 — owner: Luna's actual source/App-demand/extrusion construction lane.** At an actual retained, birth-qualified App/Call operation, supply the owning equation from that original App's `sourceCallIncidence` and complete Call tuple, at the one incoming source telescope, to `OriginalExtrusionWork.Operation.initial` and every retained `Parent.parent/copy` coordinate. It must identify the actual returned callee/provider and inert whole argument, original source Value origin/receiver, and all corresponding dependency terms/scopes. It must be produced by the actual construction/history, rather than selected from successful valuations, numeric levels, row SCCs or matching display types.

The first absent endpoint equation is the native demand's interpretation as the demand at `⟨callee.site, .returnedValue⟩` checked against `⟨App.site, .descriptor⟩` in that same App witness environment. Its Function decomposition must relate **both** native effect children (`FunctionTerms.argumentEffect`, `resultEffect`) as well as argument/result Value children to the complete original Call's argument, invocation/observation and current evidence. Lower/upper support, provider/capture identity, receipts, typed path, designated consumer, joint guards, attachment/witness and checked-observation fields remain coupled; numeric `Flow.demand` metadata preservation does not supply these equations.

This request does **not** require a separate source term/Desc for each native coordinate, alter qualification, or assume that selected parent/copy values already coincide. Endpoint terms at their actual legal telescopes suffice if the real owner supplies them. Publication/`ScopedClosure` and every lawful use must then interpret those same incidences and the same Shared maps. They cannot be inferred from copy erasure or the finite-reader PASS.

Parent application: at the original §5 completeness induction's App case, `app_derivation_iff` would extract the complete original source premise at exactly one original witness; `app_witness_scope_fields` would fix its outer/shared/event context. **The induction stops before defining the telescope-indexed simultaneous substitution**, because no pinned constructor identifies the actual selected native pair with scoped endpoint terms in that premise. There is therefore no source-derived fiber-constancy proof to apply to `SimpleSub.OriginalPrincipality.joint_solution_coverage_iff`. That lemma's fiber-constant existential stays open, with the original external conclusion, source domain and shared witnesses unchanged. No parent theorem is claimed proved or refuted.

## Commands, execution limits and cessation

Read-only manifest check: Python `hashlib.sha256`/byte-length comparison of all 25 manifest entries, **all matched**, command exit 0. Read-only `cat`, `sed`, `rg`, `sha256sum`, `wc -c` and UTC-clock calls inspected the sources above; shell calls completed without timeout. The artifact hash/size command exited 0. The broad text scan `rg 'sorry|admit|^axiom|skipKernel|native_decide'` matched only the ordinary word/identifier `admitted`; it is not a transitive axiom audit.

Toolchain files read: `leanprover/lean4:v4.35.0`; library `YulangClosure`; `moreLeanArgs = ["-j1", "-M1024"]`; manifest has no external packages. **Actual executable/version, kernel exits, printed theorem types and axiom results: NOT RUN / UNKNOWN.** No `elan`, Lean, Lake, build, test, installation or compiler invocation occurred. Calls used by this leaf: **0/2**. No failed Lean receipt exists and none is invented.

The skill's checker was inspected, not run: it would invoke Lake and create scratch audit files, contrary to the fixed R88 envelope. A later direct stdin check can flatten only the two pinned project dependencies plus this candidate and retain the existing four `#check`/`#print axioms` pairs; Luna must first authorize the exact executable/input hashes and own stdout/stderr/receipts. This is a handoff suggestion, not an execution authorization.

Resource observations: first recorded timestamp `2026-10-31 14:45:25.903 UTC`; candidate hash observation `14:51:39.376 UTC` (373.473 seconds between recorded observations). Launch-to-first-observation elapsed is not exposed here; Luna retains the launch clock and the unchanged 1,400-second lane bound. CPU time and peak RSS were not instrumented. No long-running process, descendants or unaccounted generated output exists.

Exact writes: this handoff and the single Lean candidate only. Scratch, `/tmp`, cache, worktree, project/environment copies and generated outputs: **none**. Other workers' paths, Rust, toolchain/manifests, root imports, shared records, tests, questions and Git were not mutated. **WRITES STOPPED** for revision 1 after this handoff; candidate bytes are frozen pending primary intake/review. A repair requires a new acknowledged revision and Luna's remaining execution budget. A/B, source/native correspondence, independent review and production remain OPEN.
