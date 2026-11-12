# Cycle128 verification

Local focused verification only. Full repository build/audit is hosted CI, not a local claim.

## Exact focused targets
```sh
cd lean
timeout 180s lake build Yulang.GeneralDictionaryPayloadReconstruction Yulang.GeneralDictionaryRecipeFidelity Yulang.GeneralDictionaryPayloadPreparation Yulang.GeneralDictionaryPayloadReconstructionOrder Yulang.GeneralDictionaryPayloadReconstructionExamples Yulang.GeneralDictionaryPayloadPreparationExamples Yulang.GeneralDictionaryNominalEquations Yulang.GeneralDictionaryNominalExamples Yulang.GeneralDictionaryNominalRecording Yulang.GeneralDictionaryNominalSourceEvidence Yulang.GeneralDictionaryNominalSourceExamples Yulang.GeneralDictionaryNominalStateEvidence Yulang.GeneralDictionaryNominalStateExamples Yulang.GeneralDictionaryNominalCandidateReadback Yulang.GeneralDictionaryNominalCandidateReadbackExamples Yulang.GeneralDictionaryNominalCandidateEvidence Yulang.GeneralDictionaryNominalCandidateEvidenceExamples
```

## Final outputs

### final-build
Command: `focused targets above`
Exit: 0
```text
✔ [603/603] Built Yulang.GeneralDictionaryNominalCandidateEvidenceExamples (3.4s)
Build completed successfully (603 jobs).
```

### final-audit
Command: `cd lean && timeout 90s lake env lean --trust=0 ../cache/yulang128/FinalAudit.lean`
Exit: 0
```text
'Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_exists_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstruct_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecipeFidelity.localize_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecipeFidelity.headless_prepare_tree' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecipeFidelity.source_prepare_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecipeFidelity.recipe_tree' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecipeFidelity.recipe_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecipeFidelity.prepare_recipe_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparation.prepare_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparation.prepare_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparation.prepare_uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparation.prepare_payload_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.leaf_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.extra_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.wrong_role_key_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.absent_key_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.source_identities_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstructionExamples.source_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparationExamples.raw_tree_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparationExamples.raw_uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparationExamples.raw_source_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparationExamples.raw_payload_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparationExamples.raw_preparation_with_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparationExamples.absent_output_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.liftRow_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.recorded_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.append_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.atoms_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.batch_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalEquations.batch_member_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalExamples.base_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalExamples.root_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalExamples.child_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalExamples.joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalExamples.tree_joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalExamples.nominal_not_embedded_int' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalRecording.liftAtom_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.liftAtoms_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.recorded_base_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.record_preserves' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.record_pending' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.record_order_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.realizes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.singleton_value' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.head_realization' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.output_realization' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.source_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.transaction_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSourceEvidence.prepare_uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSourceExamples.raw_nominal_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSourceExamples.raw_nominal_payload_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalStateEvidence.prepare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalStateEvidence.prepare_payload_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalStateExamples.full_base_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalStateExamples.full_record_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalStateExamples.full_nominal_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalStateExamples.full_root_pending' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalStateExamples.recorded_root_pending' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.declaration_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.bindings_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.survivor_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.evidence_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.payload_candidate_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.payload_candidate_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.root_plan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.leaf_plan' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_plan_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_child_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadbackExamples.source_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_candidate_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidence.prepare_uniform_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.terminal_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.located' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.report' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.candidate_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.preparation_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.preparation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.tree_items' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.recorded_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidenceExamples.joint_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### final-runtime
Command: `cd lean && timeout 90s lake env lean --trust=0 ../cache/yulang128/Runtime.lean`
Exit: 0
```text
some (2, 2)
true
some (1, 2)
some (7, 1)
```

### definition-audit
Command: `cd lean && timeout 90s lake env lean --trust=0 ../cache/yulang128/DefinitionAudit.lean`
Exit: 0
```text
'Yulang.GeneralDictionaryPayloadReconstruction.reconstruct' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPayloadReconstruction.reconstructChildren' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPayloadPreparation.prepare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNominalRecording.record' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.frames' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateEvidence.prepare' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### final-gate
Command: `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`
Exit: 0
```text
verify-lean: . @ e08bc7ade (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

## Exact runtime program
```lean
import Yulang.GeneralDictionaryNominalCandidateEvidenceExamples
import Yulang.GeneralDictionaryPayloadPreparationExamples
import Yulang.GeneralDictionaryNominalCandidateReadbackExamples
open Yulang
#eval (GeneralDictionaryPayloadReconstruction.reconstruct
  GeneralDictionaryHeadlessFixture.registry GeneralDictionaryHeadlessFixture.registry_checked
  (fun _ => GeneralDictionaryHeadlessFixture.frame)
  GeneralDictionaryPayloadReconstructionExamples.payload GeneralDictionaryHeadlessFixture.root).map
  (fun tree => (tree.key, (GeneralSourceDictionaries.observations tree).length))
#eval (GeneralDictionaryPayloadReconstruction.reconstruct
  GeneralDictionaryHeadlessFixture.registry GeneralDictionaryHeadlessFixture.registry_checked
  (fun _ => GeneralDictionaryHeadlessFixture.frame)
  (.node 2 []) GeneralDictionaryHeadlessFixture.root).isNone
#eval (GeneralDictionaryNominalCandidateReadback.reconstruct
  GeneralNominalExamples.registry GeneralNominalExamples.registry_checked (GeneralNominalExamples.context true)
  GeneralDictionaryNominalCandidateReadbackExamples.payload GeneralNominalExamples.displayRoot).map
  (fun tree => (tree.key, (GeneralSourceDictionaries.observations tree).length))

#eval (GeneralDictionaryNominalCandidateEvidence.prepare
  GeneralDictionaryNominalCandidateEvidenceExamples.registry
  GeneralDictionaryNominalCandidateEvidenceExamples.registry_checked
  (GeneralNominalExamples.context true)
  GeneralDictionaryNominalCandidateEvidenceExamples.payload
  GeneralDictionaryNominalCandidateEvidenceExamples.root).map
    (fun tree => (tree.dictionary.key, (GeneralSourceDictionaries.observations tree.dictionary).length))
```

## Signature inventory
Command: `cd lean && timeout 90s lake env lean --trust=0 ../cache/yulang128/Signatures.lean`.
Exit: 0. All 98 names and complete `#check @` types are reproduced in [the theorem inventory](dots-cycle-128-theorems.md).

## All attempt exit codes
Earlier failed elaborations are not counted as successful verification. The final runs above supersede them.
```text
candidate-dependency-build.exit: 0
candidate-readback-build.exit: 0
checkpoint-audit.exit: 0
checkpoint-gate.exit: 0
definition-audit.exit: 0
fidelity-build.exit: 1
fidelity-build2.exit: 0
final-audit.exit: 0
final-build.exit: 0
final-gate.exit: 0
final-runtime.exit: 0
final-signatures.exit: 0
full-nominal-build.exit: 1
full-nominal-build2.exit: 0
nominal-audit.exit: 0
nominal-build.exit: 0
nominal-fixture-dependency.exit: 0
nominal-recording-build.exit: 0
payload-build.exit: 1
payload-build2.exit: 1
payload-build3.exit: 1
payload-build4.exit: 1
payload-build5.exit: 0
reconstruction-build.exit: 1
reconstruction-build2.exit: 1
runtime.exit: 0
second-audit.exit: 0
second-build.exit: 0
second-gate.exit: 0
second-signatures.exit: 0
signatures.exit: 0
third-audit.exit: 0
third-build.exit: 0
third-signatures.exit: 0
```

Earlier development failures: recursive reconstruction equations needed explicit reduction; recipe-localization equality needed full-tree induction; nominal examples needed dependent-index elimination and correctly formed state-model fields. Each was fixed before final focused verification. The first final build invocation used the repository root instead of lean/ and returned a configuration-path error; the actual focused command above ran in lean/ and succeeded. No proof obligation was suppressed.

Publication verification initially parsed the tab-separated local tree incorrectly. No content write resulted from that comparison error; corrected whitespace parsing verified all 2485 entries. A hosted-log parser initially retained timestamp prefixes on wrapped axiom lines. It was corrected by stripping timestamp prefixes before comparing names, then all 9117 entries were checked.

## Source publication readback
```json
{"commit":"07cfd9def3a1eb5baf7b21fb600659b4d98d21d2","tree":"f4c14547520c0c3098cbf0bbb056a5a05c1c1749","remoteCount":2485,"localCount":2485,"truncated":false,"mismatches":0}
```

## Hosted verification
Core run43124544032 and proof run43124545197 both success for exact source SHA.
```json
{"commit":"07cfd9def3a1eb5baf7b21fb600659b4d98d21d2","job":130873179892,"run":43124545197,"checkout":true,"build":["Build completed successfully (1440 jobs)."],"auditBlocks":9117,"dependent":8890,"axiomFree":227,"theorems":98,"missing":[],"forbidden":[]}
```

The first source checkpoint verified2474 files and hosted1429jobs/9053 audit entries (34 new theorem names). The second verified2482 files and hosted1437jobs/9096 audit entries (77 new names). Final source verifies2485 files and hosted1440jobs/9117 audit entries (98 new names). Every publication used work/dots-main and nonforce expected-head updates.

## Remaining limitations
General B4Bridges V3 remains12/12 unfilled. Candidate evidence and successful partial preparation remain independent premises. No general Step, stable forest, arbitrary model existence, candidate completeness, or full boundary is claimed. Existing root-output and coverage guards remain unchanged.

## Registration and inventory crosscheck

All17 modules were compared with actual public theorem declarations, Audit registrations, umbrella imports and the exact-type inventory. Indented mutual theorems are included.

```json
{"modules": 17, "public_theorems": 98, "unique_names": 98, "Audit_registration": 98, "inventory_entries": 98, "umbrella_imports": 17}
```

Existing Lean modifications are restricted to appended registrations/documentation in Audit.lean, Yulang.lean and README.md. All17 implementation modules are new.
