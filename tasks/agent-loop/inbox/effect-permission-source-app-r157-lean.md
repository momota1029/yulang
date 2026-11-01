# R157 original App admission — leaf handoff revision 1

Status: **CONSTRUCTED / UNCHECKED / FROZEN / WRITES STOPPED**. Outcome: candidate construction plus exact source-owner obstruction. No parent theorem closure or source-qualified counterexample.

Assignment `/root/r157_lean_proof`; actual NEW_TASK from `/root` is the launch/activity receipt. This leaf is the sole author, with no descendants. Requested model/effort and effective observed model/effort: **UNKNOWN** (no runtime metadata was exposed). Role/configuration is not model activation evidence.

Exact leases and complete writes: `notes/theory/lean/YulangClosure/SourceAppAdmissionR157.lean` and this handoff. No scratch, runner file, generated Lean output, `/dev/shm` directory, cache, root import, compiler, test, configuration, dependency, scheduling or Git write occurred.

Contract: `tasks/agent-loop/sprints/effect-permission-effect-hygiene-20261102-r157.md`, SHA-256 `3de87e544b44a0ea346a7ba61b0c572e5f3b833768ebee87ecf97e23fc54ad6d`. Primary packet baseline: `17a4ee005`; contract baseline: `ead05a34e8aba32a1ca1d66e72109877d4b37e0e`. These are recorded separately, with no claim that they are equal. No Git command was used. The content hashes below identify the inspected inputs.

## Original sources and claim

Authority: `notes/design/2026-10-08-source-generalize-definition.md` §§2–3 selects `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1–3.3 and 5.2. Actual original App/Call retains the complete callee, inert whole argument, descriptor formation, source incidence, complete decorated Call certificate, callable image, and original finite checking. ViewLogic stays once per incoming description frame; Shared remains one original anchor; event witnesses stay under their actual event telescope.

Parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5: every supported source, lawful finite construction history and actual qualified extrusion must preserve original typing, required principal coverage, soundness, ordinary progress and termination with original scopes, complete Call/effects and one joint strategy. Qualification uses immutable Value birth levels and SCCs of each induced graph under `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Source Generalize local L1–L5 laws remain premises owned at their independent source interpretations.

Read current root/base operating instructions, goal-driven-sprints, current state, assignment protocol, Lean skill plus sources/execution references, fixed contract, project pins, relevant README sections, original source generation/interpretation/environment and R112/R114. The opening correction of `docs/yulang-source-type-safety-ja.tex` is explicitly a research/candidate manuscript; its source/core construction and lifetime correction are not semantic adoption. The 2026-10-26 source-generation construction §8 explicitly leaves original local semantic suppliers open. No research draft was treated as authority.

Exact source hashes:

| Source | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

## Constructed declarations and represented cases

Artifact: 12,595 bytes, 201 lines, SHA-256 `98cf8e4948ce1f9a72ebdcca7d5d2488b052df33c62947e067b10a616af5c00f`. Seven theorem declarations and two ordinary data definitions. **Printed types and every transitive axiom result: NOT RUN for all seven.** The exact source signatures follow; they are proposed types, not checker output.

`admitted_view_payload` uses unchanged `Admitted`/`LocalAdmissions`, classifies the candidate as `.logical .viewLogic data`, and reconstructs its exact parent path and occurrence. It retains arbitrary descriptor/interface writes and every independent proof field. `app_admission_exact` applies R112 and R114 at this same witness, returning admission, exact decode, chosen descriptor/interface maps, every original Local, descriptor formation, both finite Checking proofs, both operands, and the complete original continuation.

Both `mark.annotation` alternatives are covered by R112; the original annotation derivation remains in the input. Both `singletonFormalCall` branches occur in `appPremises` exactly as generated, including the conditional `roleAndInitialCallOrigin` atom. The arbitrary callee and argument may contain the complete original 13/11/3 source inventory. They are retained as original SourceJudgments, without claiming separate normalization of their internal constructors. Original kernel/checking admission is not replaced by a safety definition.

`clearWrites` is only a candidate payload operation. `clear_writes_contract_iff` proves its precise decoder condition: `put descriptor writes = original descriptor map` AND `put interface writes = original interface map`. The two final lemmas show any empty-write replacement loses an actually changed descriptor/interface at that endpoint, even with arbitrary other proof fields. They do not assert that an authenticated original source has changed or redundant writes.

```lean
theorem admitted_view_payload (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (site : Site) (candidate : ScopedValue (Payload s View))
    (accepted : Admitted inputs readout admissions environment ⟨site, .viewLogic, 0⟩ candidate) :
    ∃ occurrence data state,
      candidate = scopeCandidate environment occurrence (.logical .viewLogic data) ∧
      decode readout environment = some state ∧
      admissions.logical state ⟨site, .viewLogic, 0⟩ .viewLogic data
```

```lean
theorem app_continuation_exact (kernel : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression)
    (derivation : Judgment kernel environment
      (LogicalOccurrencesR104.appRule context mark callee argument)) :
    (∀ premise ∈ appPremises context mark callee argument, Local kernel environment premise) ∧
      SourceJudgment kernel environment context callee ∧
      SourceJudgment kernel environment context argument
```

```lean
theorem app_formation_and_checks (kernel : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression)
    (derivation : Judgment kernel environment
      (LogicalOccurrencesR104.appRule context mark callee argument)) :
    kernel.atom environment (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
      Checking kernel environment
        ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∧
      Checking kernel environment
        ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩
```

```lean
theorem app_admission_exact (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression)
    (source : SourceJudgment (admissionKernel inputs readout admissions original)
      environment context (.app mark callee argument)) :
    ∃ occurrence data state,
      decode readout environment = some state ∧
      admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
      let kernel := admissionKernel inputs readout admissions original
      let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
      let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
      kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
      decode readout after = some (state.logical data) ∧
      (state.logical data).assignment.descriptor = put state.assignment.descriptor data.descriptors ∧
      (state.logical data).interfaces = put state.interfaces data.interfaces ∧
      (∀ premise ∈ appPremises context mark callee argument, Local kernel after premise) ∧
      kernel.atom after (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
      Checking kernel after
        ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∧
      Checking kernel after
        ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ ∧
      SourceJudgment kernel after context callee ∧
      SourceJudgment kernel after context argument ∧
      Judgment kernel after (LogicalOccurrencesR104.appRule context mark callee argument)
```

```lean
theorem clear_writes_contract_iff (state : Decoded s View) (data : Logical s View) :
    ((state.logical (clearWrites data)).assignment.descriptor = (state.logical data).assignment.descriptor ∧
      (state.logical (clearWrites data)).interfaces = (state.logical data).interfaces) ↔
    (put state.assignment.descriptor data.descriptors = state.assignment.descriptor ∧
      put state.interfaces data.interfaces = state.interfaces)
```

```lean
theorem changed_descriptor_excludes_empty_replacement
    (state : Decoded s View) (data replacement : Logical s View) (point : Endpoint)
    (empty : replacement.descriptors = [])
    (changed : put state.assignment.descriptor data.descriptors point ≠ state.assignment.descriptor point) :
    (state.logical replacement).assignment.descriptor point ≠
      (state.logical data).assignment.descriptor point
```

```lean
theorem changed_interface_excludes_empty_replacement
    (state : Decoded s View) (data replacement : Logical s View) (point : Endpoint)
    (empty : replacement.interfaces = [])
    (changed : put state.interfaces data.interfaces point ≠ state.interfaces point) :
    (state.logical replacement).interfaces point ≠ (state.logical data).interfaces point
```

## Parent application and exact remaining source law

For `kernel := admissionKernel inputs readout admissions original` and an actual generated solution `solved : Satisfies kernel environment (Build context (.app mark callee argument))`, apply the existing unchanged source reconstruction and then this candidate:

```lean
app_admission_exact inputs readout admissions original environment context mark callee argument
  (OriginalSource.generated_constraints_imply_source_judgment kernel environment context
    (.app mark callee argument) solved)
```

This supplies the exact original admitted raw App witness and all its original obligations. It neither supplies `solved` from native success nor the intrusion-adjusted joint strategy. That application is a proposed term, not an executed Lean receipt.

First remaining goal, owner: **primary source/Checking semantics intake, specifically descriptorFormation and original admission**. Establish which descriptor/interface introduction the ORIGINAL App owns at its ViewLogic binder. There is no preceding Desc binder in `OriginalSource.sourceRules` for App. An empty-write target requires deriving the two redundancy equations from authentic source laws, or an independently justified representation retaining the actual selected descriptor/interface introduction. R114’s complete App interface discriminator shows unconditional redundancy fails for its explicit local model; that model is not a source-qualified counterexample.

Even decoded-state equality would still leave original admission and full-environment predicate transport open: `Kernel.atom`, `primitiveCheck`, `structuralShape`, `functionShape`, boundary/conversion and logical admission can inspect raw frames. No congruence law is established by their record types. A lawful replacement must construct admission plus every original Local and BOTH operand judgments under its actual extension. Supplying that conclusion as a hypothesis would restate the missing App law and is deliberately absent.

Lambda remains a separate obligation: exact Desc/ViewLogic before every admitted invocation, actual receipt, Value Return/rebind or retained Computation entry, same Shared anchor, body/pattern derivations, body-consumer atoms and finite computation Checking. Effect hygiene additionally needs concrete receipt/capture/body/shallow residual/latent/rigid-operation/raw-continuation interpretations tied to current authority/incidence. The existing OriginalEffectHygiene component supplies original publication/replay provenance and return/Name lifetime facts under its printed premises; it does not supply those missing local laws. Native success-to-solution, source/core correspondence, full A/B, whole effect hygiene, soundness, principality, termination and production remain OPEN.

Mutual TODO `R157-APP-FORMATION-OWNER-1`: source owner provides actual descriptorFormation/admission definition and a constructive introduction/transport law at the original App binder. Required output is a source-grounded admitted payload preserving the exact extracted continuation, both checks and both operands; falsifier is an authentic supported source derivation for which that proposed law fails. This TODO grants no write authority.

## Frozen module graph and named audit roots

Primary confirmed R156’s map was runtime-only and requested this read-only regeneration. Exactly 27 imported YulangClosure modules, 1,048,416 unique source bytes, and 61 authored theorem roots in the five requested root modules. The import traversal reads complete file bytes mechanically for hashes/imports/declaration census; this is not a claim that every proof body was manually reviewed. Focused manual reads covered the declarations cited above. Adding R157 extends this exact closure to 28 modules and 68 named roots; it does not change the R156 counts.

Topological order below is a valid serial order. Module names omit the common `YulangClosure.` prefix. Imports are exact direct source import lines (the same prefix omitted).

| # | Module | Bytes | SHA-256 | Direct imports |
| --- | --- | ---: | --- | --- |
| 1 | `OriginalSourceSyntax` | 22040 | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` | `Std` |
| 2 | `OriginalSourceGeneration` | 66485 | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` | `OriginalSourceSyntax` |
| 3 | `SourceLogicalOccurrencesR104` | 23908 | `0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39` | `OriginalSourceGeneration` |
| 4 | `NativeClosureEnvironment` | 12152 | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` | `Init` |
| 5 | `Contracts` | 7467 | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` | `Init` |
| 6 | `SourceIdentityWorld` | 25976 | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` | `NativeClosureEnvironment`, `Contracts` |
| 7 | `SourceFunctionMembership` | 7744 | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` | `SourceIdentityWorld` |
| 8 | `NativeDictionaryDenotation` | 33584 | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` | `Init` |
| 9 | `OriginalSourceInterpretation` | 56341 | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` | `OriginalSourceGeneration`, `SourceFunctionMembership`, `NativeDictionaryDenotation` |
| 10 | `OriginalSourceEnvironment` | 81021 | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` | `OriginalSourceInterpretation` |
| 11 | `SourceSignatureConstruction` | 37437 | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` | `OriginalSourceSyntax` |
| 12 | `OriginalSourceEvents` | 66574 | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` | `OriginalSourceEnvironment`, `SourceSignatureConstruction` |
| 13 | `SourceLogicalOwnerBridgeR105` | 19998 | `6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4` | `SourceLogicalOccurrencesR104`, `OriginalSourceEvents` |
| 14 | `OriginalRecursivePair` | 78256 | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` | `OriginalSourceInterpretation` |
| 15 | `OriginalWorldReadout` | 31012 | `edb82b9ecc62be486e057ee50152e30dad709f9a90196f78cab803838f08fb00` | `OriginalRecursivePair`, `OriginalSourceEnvironment` |
| 16 | `OriginalSourceChecking` | 103542 | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` | `OriginalSourceEnvironment` |
| 17 | `OriginalCheckingAdmission` | 52370 | `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7` | `OriginalSourceChecking` |
| 18 | `OriginalParameterWorld` | 33616 | `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802` | `OriginalWorldReadout`, `OriginalSourceEvents`, `OriginalCheckingAdmission` |
| 19 | `OriginalParameterSemantics` | 45481 | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` | `OriginalParameterWorld` |
| 20 | `OriginalFormalShared` | 58542 | `abb9d69546e284fcb5fe6be9bb3c18269227e91da94e09eebf1a62e0b56e67f7` | `OriginalParameterWorld`, `OriginalParameterSemantics` |
| 21 | `OriginalRetainedParameter` | 55668 | `ae8915cf002019541d0658895f0604e98700ac23f47aac479fc8382cf65ef799` | `OriginalParameterSemantics` |
| 22 | `OriginalFormalAdmission` | 34188 | `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c` | `OriginalFormalShared`, `OriginalRetainedParameter` |
| 23 | `OriginalSourceClosure` | 31884 | `e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a` | `OriginalFormalAdmission` |
| 24 | `SourceScopedAdmissionR112` | 13879 | `f43dd36aab4f3c25395ba87529bd037c21a77d50e48fda0d15c7a7a064d0b22f` | `OriginalSourceClosure`, `SourceLogicalOwnerBridgeR105` |
| 25 | `SourceAdmissionTransportR114` | 18462 | `7b3eb4a944999a6581b7bd85b2ba80e44ac69c592b43c42a6b4bb856dd55abac` | `SourceScopedAdmissionR112` |
| 26 | `PaperTypeSubstitution` | 10022 | `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861` |  |
| 27 | `OriginalEffectHygiene` | 20767 | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` | `OriginalSourceGeneration`, `SourceFunctionMembership`, `PaperTypeSubstitution` |

Named root inventory (all must be theorem constants and have complete printed type plus transitive axiom list; no root may be dropped after an error):

`YulangClosure.SourceLogicalOccurrencesR104` (10 roots):

```text
YulangClosure.OriginalSource.LogicalOccurrencesR104.inventory_iff_lookup
YulangClosure.OriginalSource.LogicalOccurrencesR104.encode_lookup
YulangClosure.OriginalSource.LogicalOccurrencesR104.observe_eq_follow
YulangClosure.OriginalSource.LogicalOccurrencesR104.source_membership_iff
YulangClosure.OriginalSource.LogicalOccurrencesR104.full_route_unique
YulangClosure.OriginalSource.LogicalOccurrencesR104.source_provenance
YulangClosure.OriginalSource.LogicalOccurrencesR104.app_exact
YulangClosure.OriginalSource.LogicalOccurrencesR104.lambda_body_exact
YulangClosure.OriginalSource.LogicalOccurrencesR104.app_inventory
YulangClosure.OriginalSource.LogicalOccurrencesR104.lambda_body_inventory
```

`YulangClosure.SourceLogicalOwnerBridgeR105` (15 roots):

```text
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.forest_head_route
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.forest_sibling_route
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.choice_right_route
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.advance_erases
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.follow_erases
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.advance_owner
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.follow_owner
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_route_exact
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_viewlogic_separate
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.app_bridge
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_route_exact
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.body_telescope_binders
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_owner
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.body_key_coordinates
YulangClosure.OriginalSource.LogicalOwnerBridgeR105.lambda_body_bridge
```

`YulangClosure.SourceScopedAdmissionR112` (11 roots):

```text
YulangClosure.SourceScopedAdmissionR112.app_witness
YulangClosure.SourceScopedAdmissionR112.lambda_telescope
YulangClosure.SourceScopedAdmissionR112.body_eventproof
YulangClosure.SourceScopedAdmissionR112.value_body_telescope
YulangClosure.SourceScopedAdmissionR112.computation_body_telescope
YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.admits_writes
YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.scoped_admits_writes
YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.shell_judgment
YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.changes_contract_fields
YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.proof_wrapper_rejects
YulangClosure.SourceScopedAdmissionR112.InterfaceCountermodel.no_event_packet_encoding
```

`YulangClosure.SourceAdmissionTransportR114` (10 roots):

```text
YulangClosure.SourceAdmissionTransportR114.app_continuation_iff
YulangClosure.SourceAdmissionTransportR114.app_actual_check
YulangClosure.SourceAdmissionTransportR114.checked_body_iff
YulangClosure.SourceAdmissionTransportR114.shared_body_iff
YulangClosure.SourceAdmissionTransportR114.lambda_core_iff
YulangClosure.SourceAdmissionTransportR114.entry_telescope_iff
YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.locals_of_ready
YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.raw_ready
YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.original_source_judgment
YulangClosure.SourceAdmissionTransportR114.ActualAppDiscriminator.no_normalized_continuation
```

`YulangClosure.OriginalEffectHygiene` (15 roots):

```text
YulangClosure.OriginalEffectHygiene.publication_candidate_provenance
YulangClosure.OriginalEffectHygiene.publication_lookup_provenance
YulangClosure.OriginalEffectHygiene.execution_lookup_provenance
YulangClosure.OriginalEffectHygiene.source_publication_constructs_replay
YulangClosure.OriginalEffectHygiene.replay_rejects_foreign_path
YulangClosure.OriginalEffectHygiene.description_extension_keeps_replay
YulangClosure.OriginalEffectHygiene.future_scope_has_no_replay_value
YulangClosure.OriginalEffectHygiene.published_replay_provenance
YulangClosure.OriginalEffectHygiene.published_execution_judgment
YulangClosure.OriginalEffectHygiene.generated_new_use_keeps_original_publication
YulangClosure.OriginalEffectHygiene.Native.owned_return_expires
YulangClosure.OriginalEffectHygiene.Native.name_preserves_historical_evidence
YulangClosure.OriginalEffectHygiene.Native.return_then_name_cannot_revive
YulangClosure.OriginalEffectHygiene.operation_substitution_keeps_declaration
YulangClosure.OriginalEffectHygiene.substitution_cannot_identify_distinct_operations
```

## Module-faithful future runner/review plan — NOT EXECUTED

Plan only: this handoff is not an executable runner or execution approval. Primary verification owner must instantiate the exact runner under a new exact lease, freeze/hash its bytes and this inventory, and obtain fresh independent review before one future batch. No existing R104/R106 review authorizes a retry. Use only the installed native distribution `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0`; installation/dependencies return to the primary if unavailable. No new environment, worktree or persistent cache.

1. Preflight outside Lean: verify all source/config/checker hashes, all direct import edges and full root list; reject missing/changed inputs, symlinks, duplicate modules/roots and unexpected non-YulangClosure project imports. Verify the native executable identities and already-installed toolchain using read-only paths/elan lookup, without an unresolved installing proxy. Under the same bounded owner, capture native `lake --version` and `lean --version`; both must identify Lean 4.35.0. No Lake build/env/default target is part of this runner. Existing executable actual versions were NOT RUN by this leaf.

2. Allocate exactly one unpredictable, mode-0700 directory via `mkdtemp(prefix="yulang-r157-module-audit-", dir="/dev/shm")`. Call its absolute canonical path ROOT. It must be absent before allocation and must not overlap any prior/quarantined path. Layout: ROOT/lib/YulangClosure, ROOT/audit, ROOT/log, ROOT/tmp. No source rewrite or flattening: compile original files directly with `--root=/home/momota1029/rust/yulang/notes/theory/lean`. Preserve module boundaries, private declarations, command scopes, source bytes and exact filenames. Read source and native installation; write only below ROOT. Set `PYTHONDONTWRITEBYTECODE=1`, `LEAN_NUM_THREADS=1`, `TMPDIR=ROOT/tmp`. Set LEAN_PATH to ROOT/lib followed by the native distribution’s lib/lean only; exclude project `.lake`, existing project `.olean`s and arbitrary inherited LEAN_PATH.

3. Proposed finite envelope for fresh review/admission: one serial batch, one active Lean process group, one CPU selected from the actual allowed affinity, 60 seconds per module, 45 seconds for the final named audit and 240 seconds aggregate (including version/preflight commands). Keep `-j1 -M1024`. External aggregate resident-memory guard: 1,342,177,280 bytes across all group members; ROOT cap 2,147,483,648 bytes counting both logical sizes and allocated blocks. Sample process-group RSS, elapsed time, root file types/paths/count/size at most every 50 ms, plus pre/post-command guards. Stop immediately on first guard failure, missing monitoring capability, module nonzero exit, timeout, signal, source hash drift or cleanup failure. These are proposed limits requiring fresh resource review, not measured runtime promises. No automatic retries or resource increase.

4. For each module in the exact table order, run the direct native Lean argv, with cwd at the original project root and one new process group:

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
  -j1 -M1024 --root=/home/momota1029/rust/yulang/notes/theory/lean
  -o ROOT/lib/YulangClosure/Module.olean
  /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/Module.lean
```

`Module` is replaced with the exact table module basename. R157 itself is an explicit optional 28th module, never inferred covered by the other five roots. Capture untruncated stdout/stderr, exact argv/cwd/env, exit/signal, wall time and sampled group RSS. Emit input/artifact SHA-256 inventories. A zero exit with absent/empty expected artifact is failure. Do not start the next module until all group members have ceased and outputs have passed inspection.

5. Transient `.olean.tmp.<pid>` handling: for the CURRENT module only, permit regular nonsymlink files matching the exact expected `.olean` path plus `.tmp.` and one or more decimal digits. Permit these solely while that module’s owned process group is active. The suffix may use a PID namespace; do not equate it to a host PID or classify the numeric name as a surviving process. Never broaden to arbitrary `*.tmp*`, other module paths, directories, symlinks or writes outside ROOT. All transient files count toward the 2-GiB cap. After process cessation require the final `.olean`, no transient leftovers and no unexpected output. A leftover or missing final artifact is a failed run, with its bytes/path/hash preserved in the failure receipt before cleanup. Do not delete a transient while its writer may still run. Pin handling of `.olean.server`, `.olean.private`, `.ir` and `.ir.sig` to actual source/module-mode inventory: these legacy sources have no leading `module` command, so this plan expects only `.olean`; any new output shape requires a new source-grounded review, not a silent allowlist expansion. Pinned `Lean/Environment.lean:1902` distinguishes legacy `saveModuleData` from module-mode multipart exports; pinned `Lean/Elab/Frontend.lean:384` writes the export only after no errors. The observed R106 `.olean.tmp.7` remains the concrete transient evidence.

6. After all modules pass, create ROOT/audit/R157NamedAudit.lean with the five actual imports (and R157 only if its explicit extension was admitted), `import Lean.Elab.Command`, `import Lean.Util.CollectAxioms`, `set_option pp.fullNames true`, and one ordered audit block per exact named root. Use the unchanged skill checker’s `audit_source`/`validate_audit` logic: require `.thmInfo`, emit BEGIN/END markers, `#check @Fully.Qualified.name`, `#print axioms Fully.Qualified.name`, and `Lean.collectAxioms` rejecting every dependency beyond `propext`, `Classical.choice`, `Quot.sound`. Reject absent/truncated/reordered/duplicate markers or types/axiom results. Do not treat a Prop definition or assumed LocalLaws as a delivered theorem. The 61-root inventory includes all 15 OriginalEffectHygiene roots, which have no embedded queries; they must be added explicitly. Audit the seven R157 roots too if its extension is admitted. Every actual list, including empty lists or `sorryAx`, must be retained verbatim.

7. Run that audit directly with the same native Lean, `-j1 -M1024 --root=ROOT/audit ROOT/audit/R157NamedAudit.lean` and isolated LEAN_PATH; no output `-o` is necessary. The bundled checker cannot be executed unchanged within this packet: its `main` always runs `lake --no-cache build` and creates another temporary directory. Reusing its audit generation/validation in a separately reviewed direct runner preserves its theorem-kind/axiom checks; bypassing them is not allowed. Checker hash is pinned below. This is why no checker receipt is claimed here.

8. Stop/cleanup: on any failure terminate the entire known process group, wait/reap it, then independently check remaining group membership. Do not infer cessation merely from wrapper exit, a `.tmp` suffix or an absent leader. Preserve untruncated failure/log/resource/artifact evidence by emitting it to the primary-owned command receipt before deletion. Delete only this uniquely owned ROOT after all its writers have demonstrably ceased; verify ROOT absent. If cessation/cleanup cannot be established, quarantine ROOT and STOP with exact process identities and path, rather than claiming cleanup. Source hashes must remain unchanged before/after. Success only establishes named kernel acceptance under printed premises, pending independent source review; it grants no parent or production authority.

## Preserved failures and actual commands/evidence

R106 outcome `tasks/agent-loop/history/effect-permission-source-admission-20261101-r106-outcome.md`, SHA-256 `0f0ad632aba0b5e6f735c2eda7c9233d670589bd425ab0a7c183470150e779e9`: call 1 OriginalSourceSyntax, exit -9 after 5.918905 s, sampled group peak 819,956 KiB, empty stdout/stderr, UNEXPECTED_OUTPUT `YulangClosure/OriginalSourceSyntax.olean.tmp.7`, member [[7,0]], unconfirmed cessation/cleanup at that run. Later absence is separate, cause unknown. This was a runner policy failure; no R105 theorem was reached and no retry was authorized. R104 flattened syntax success and R105 flattened `Contracts.Step` scope leakage are historical, distinct from module-faithful validation. No failure receipt was overwritten.

Actual commands in this leaf: read-only `cat`, `sed`, `rg`, `pwd`, Python standard-library source/hash/import/declaration inspection, `clock` lookup, and `apply_patch` to the two leased outputs. Successful source reads/inspections/writes exited 0. A locator `cat .../LogicalOccurrencesR104.lean` exited 1 (actual file is SourceLogicalOccurrencesR104.lean); a broad locator glob exited 2 for absent optional paths; two guessed installed C++ source paths were absent (subsequent pipe still exited 0). These were source-locator failures, with no Lean goal/diagnostic. Native frontend/environment Lean sources were found/read. No Lean/Lake/elan/checker invocation, build, test, Cargo, subprocess proof check or generated artifact occurred. Actual executable versions/exits, kernel goals and all axiom results: NOT RUN.

Pin/config/checker hashes:

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `notes/theory/lean/lean-toolchain` | 25 | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | 311 | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | 145 | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` | 10178 | `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` |

Project pin: `leanprover/lean4:v4.35.0`, library `YulangClosure`, `-j1 -M1024`, no external packages. No global-default, manifest/lockfile or dependency change. Source-only inspection found no forbidden proof command in the new theorem bodies; this is not a transitive axiom audit.

Resource use: one leaf; no descendants, Lean processes, build processes, persistent cache or scratch root. Fixed leaf wall budget 1200 seconds; elapsed CPU/RSS of the agent itself is not exposed, so no numerical consumption receipt is invented. Import/hash census mechanically read 1,048,416 unique dependency bytes; five root modules contain 61 authored theorem declarations. R157 writes 12,595 source bytes and this handoff; all other reads were focused source/governing-reference reads or mechanical inventory. The source-only packet finishes before the finite bound. No independent reviewer was appointed by this leaf and no self-certification is asserted.

Worker STOP: all writes stopped after this revision. No unresolved descendants or owned generated outputs. Pending primary review/integration; any repair needs an explicit resumed packet for these frozen bytes.
