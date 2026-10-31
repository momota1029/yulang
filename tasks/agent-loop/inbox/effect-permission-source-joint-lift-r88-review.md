# R88 source-scoped joint-lift review and outcome

Sprint: `SOURCE-SCOPED-JOINT-LIFT/20261031-R88`
Contract SHA-256: `e6adf9efbcea3d07aa3b419c52c5ec878d3852afa3231047cb1e7f2a0fa8304d`
Manifest SHA-256: `239497900445ae2b3b8e546f6f080db1bf1ec7dc52b9ee1b28bbede4f3c70353`

## Independent review

Reviewer: `/root/r86_independent_review`, separate from both R88 authors. Review verdict: **PASS for the bounded R88 source-incidence obstruction outcome**. The reviewer checked all 26 manifest inputs and verified the candidate and both frozen handoffs by their pinned hashes. No blocking or major correctness finding was reported for the exact source-side obstruction.

The Lean candidate keeps the original App rule's single ViewLogic binder, complete local premises, both child derivations, optional written-annotation premises, and original environment/telescope fields. The named missing incidence is real within the pinned scope: native `ApplySourceInput.introduction` / `ScopedDemand` coordinates and `OriginalExtrusionWork.Operation` / `Parent` endpoints have no pinned interpretation into the original `sourceCallIncidence` and complete Call clause at that source telescope. The source mapper identifies the primary App/Call source-native bridge as owner and `candidate_context_seed` as the first inspected consumer. Native value/effect port metadata and receiver residual publication do not establish source scheme installation or lawful-use allocation.

The result is **not** a source-reachable counterexample, a proof that the bridge is impossible, a joint-lift theorem, or closure of the original A/B. Source result: `NO_SAFE_CODE_SLICE` for this packet. Rust semantics were not changed.

Minor handoff correction: the proof handoff says 25 manifest inputs in its command-accounting paragraph; the pinned manifest contains 26. The reviewer independently checked all 26. This count mismatch does not alter the source obstruction result.

## Primary Lean verification attempt

The contract allowed at most two direct Lean invocations, each with pinned Lean 4.35.0, `-j1 -M1024`, no Lake/build/tests, scratch, cache, or project-output writes. The primary used **2/2** invocations and will not exceed this packet's cap.

Preflight: Lean binary `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`, version `4.35.0`. The manifest-pinned `OriginalSourceSyntax.lean` and `OriginalSourceGeneration.lean` hashes matched. The frozen candidate SHA-256 was `1421c7924fb93b957612b366942adefeaeca44a1b51daad9266d43016916facd`. The single flattened stdin consisted of those source modules with their Yulang imports removed, followed by the candidate with its import removed; 98,194 bytes, SHA-256 `c06fe15684a757c81a5dc4bf03dd3eeba2a934980835a154377007820789baca`.

1. The first invocation attempt used repository-relative source paths while its working directory was `notes/theory/lean`. The flattening Python process failed before supplying input (`FileNotFoundError`); Lean received empty stdin. Pipeline exit: 1. This was a primary working-directory error, not proof evidence.
2. The second invocation ran the pinned executable with `--stdin -j1 -M1024` from the repository root, after recomputing and checking the exact flattened-input hash. Exit: **1**. Lean reported:
   - `appPremises`: invalid dotted identifier for `.roleAndInitialCallOrigin`; the expected type is ambiguous and Lean suggests `AtomKind.roleAndInitialCallOrigin`.
   - `app_rule`: `rfl` failed because `sourceRules`'s App result is not definitionally equal to the proposed `appCore`/annotation match.
   - Two unused-`simp`-argument warnings in `app_derivation_iff`.

The emitted type/axiom audit was:

| Declaration | Printed type status | `#print axioms` result |
|---|---|---|
| `app_rule` | Type printed; proof has the `rfl` error above | `propext, sorryAx, Classical.choice, Quot.sound` |
| `app_witness_scope_fields` | Type printed; accepted | `propext` |
| `app_core_iff` | Type printed under Lean error recovery; not accepted | `propext, sorryAx, Classical.choice, Quot.sound` |
| `app_derivation_iff` | Type printed under Lean error recovery; not accepted | `propext, sorryAx, Classical.choice, Quot.sound` |

The `sorryAx` results arise in an errored candidate and are not accepted proofs. Only `app_witness_scope_fields` has a clean printed axiom list, and it does not establish the joint lift. No theorem in this candidate closes the source/native bridge. No Lean build, Lake command, test, scratch file, cache, or project output was created.

## Disposition

Close R88 as a **bounded source-incidence obstruction** under contract outcome 3, with the Lean candidate recorded as constructed but checker-failing and unaccepted. Keep the original App/Call/effect correspondence, source/native joint lift, A/B, Rust implementation, and production OPEN. Next source work must pin and inspect the owner constructor producing `ApplySourceInput.introduction` and establish its source telescope/endpoint incidence before any Rust implementation slice is admitted.

Artifacts:

- Proof candidate SHA-256: `1421c7924fb93b957612b366942adefeaeca44a1b51daad9266d43016916facd`
- Proof handoff SHA-256: `f3018d03e04e4ac65e82e44329ee2a74d4e046a47f1e52726f3cc41cce6defe2`
- Source handoff SHA-256: `c2fbe9cc375beefae6cbdd78cb085ad87789c888107ac8884122a25d37d6e382`
- Independent reviewer: read-only; no Lean/build/test or filesystem writes.
- Authors: writes stopped; no Rust edits.


## Complete printed theorem types

The following are the four complete theorem signatures printed by Lean 4.35.0 on the flattened input. Names are written with the imported namespace expanded for readability; the exact printed forms are in the same order.

    app_rule :
      ∀ (mark : OriginalSource.Mark) (context : OriginalSource.Context)
        (callee argument : OriginalSource.Source OriginalSource.Category.expression),
        OriginalSource.sourceRules context
            (OriginalSource.Source.app mark callee argument) =
          match mark.annotation with
          | none => SourceScopedJointLiftR88.appCore mark.site context callee argument
          | some target =>
              OriginalSource.RuleTree.rule OriginalSource.Rule.annotation mark.site context
                (SourceScopedJointLiftR88.annotationPremises mark.site context target)
                (OriginalSource.RuleForest.one
                  (SourceScopedJointLiftR88.appCore mark.site context callee argument))

    app_witness_scope_fields :
      ∀ {Value : Type} (environment : OriginalSource.Environment Value)
        (site : OriginalSource.Site) (witness : OriginalSource.ScopedValue Value),
        let next :=
          environment.extend
            { site := site, kind := OriginalSource.BinderKind.viewLogic } witness
        next.root = environment.root ∧
        next.anchors = environment.anchors ∧
        next.publications = environment.publications ∧
        next.origin = environment.origin ∧
        next.eventPath = environment.eventPath ∧
        next.names = environment.names ∧
        next.frames =
          environment.frames ++
            [{ binder := { site := site, kind := OriginalSource.BinderKind.viewLogic },
               value := witness, entryPath := environment.eventPath }] ∧
        next.replay = environment.replay ∧
        next.initializers = environment.initializers

    app_core_iff :
      ∀ {Value : Type} (kernel : OriginalSource.Kernel Value)
        (environment : OriginalSource.Environment Value) (site : OriginalSource.Site)
        (context : OriginalSource.Context)
        (callee argument : OriginalSource.Source OriginalSource.Category.expression),
        OriginalSource.Judgment kernel environment
            (SourceScopedJointLiftR88.appCore site context callee argument) ↔
          ∃ witness,
            kernel.admitted environment
              { site := site, kind := OriginalSource.BinderKind.viewLogic } witness ∧
            (∀ (premise : OriginalSource.Premise),
              premise ∈ SourceScopedJointLiftR88.appPremises site context callee argument →
                OriginalSource.Local kernel
                  (environment.extend
                    { site := site, kind := OriginalSource.BinderKind.viewLogic } witness)
                  premise) ∧
            OriginalSource.SourceJudgment kernel
              (environment.extend
                { site := site, kind := OriginalSource.BinderKind.viewLogic } witness)
              context callee ∧
            OriginalSource.SourceJudgment kernel
              (environment.extend
                { site := site, kind := OriginalSource.BinderKind.viewLogic } witness)
              context argument

    app_derivation_iff :
      ∀ {Value : Type} (kernel : OriginalSource.Kernel Value)
        (environment : OriginalSource.Environment Value) (mark : OriginalSource.Mark)
        (context : OriginalSource.Context)
        (callee argument : OriginalSource.Source OriginalSource.Category.expression),
        OriginalSource.SourceJudgment kernel environment context
            (OriginalSource.Source.app mark callee argument) ↔
          (match mark.annotation with
           | none => True
           | some target =>
               ∀ (premise : OriginalSource.Premise),
                 premise ∈ SourceScopedJointLiftR88.annotationPremises
                   mark.site context target →
                   OriginalSource.Local kernel environment premise) ∧
          ∃ witness,
            kernel.admitted environment
              { site := mark.site, kind := OriginalSource.BinderKind.viewLogic } witness ∧
            (∀ (premise : OriginalSource.Premise),
              premise ∈ SourceScopedJointLiftR88.appPremises
                mark.site context callee argument →
                OriginalSource.Local kernel
                  (environment.extend
                    { site := mark.site, kind := OriginalSource.BinderKind.viewLogic } witness)
                  premise) ∧
            OriginalSource.SourceJudgment kernel
              (environment.extend
                { site := mark.site, kind := OriginalSource.BinderKind.viewLogic } witness)
              context callee ∧
            OriginalSource.SourceJudgment kernel
              (environment.extend
                { site := mark.site, kind := OriginalSource.BinderKind.viewLogic } witness)
              context argument

These signatures report the candidate declarations' elaborated theorem types under Lean error recovery. Their presence does not override the nonzero exit, failed app_rule, or sorryAx audit; no corresponding theorem-acceptance claim is made.
