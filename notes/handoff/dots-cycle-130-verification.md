# Cycle130: 検証・公開の証跡

基準integration: `9230c133c9627cab9504fa6c26a644c9fd9f6ad1`。最終source: `4c84d2fcb0b8fc71cfe625178a4ba3562a126998`。

## 最終ローカル検証

Lean 4.35.0、commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc。既存 .lake を再利用した。全体build/Audit/AxiomGateはlocal実行しない。以下のscoped検証はMetadata強化後のsourceと同一内容。

実行script（保持される実行sessionで起動、各コマンド180秒上限）:

```bash
#!/bin/bash
export PATH=/workspace/scratch/1d0b4aaa3394/labo-cycle128/toolchain/bin:$PATH
cd /workspace/scratch/1d0b4aaa3394/yulang/lean
names=$(sed 's/^/Yulang./' ../cache/yulang130/modules.txt | tr '\n' ' ')
timeout 180s lake build --wfail $names > ../cache/yulang130/report-build.log 2>&1; echo $? > ../cache/yulang130/report-build.exit
timeout 180s env LEAN_PATH=.lake/build/lib/lean lean --trust=0 ../cache/yulang130/FinalAudit.lean > ../cache/yulang130/report-audit.log 2>&1; echo $? > ../cache/yulang130/report-audit.exit
timeout 180s env LEAN_PATH=.lake/build/lib/lean lean --trust=0 ../cache/yulang130/Runtime.lean > ../cache/yulang130/report-runtime.log 2>&1; echo $? > ../cache/yulang130/report-runtime.exit
```

### report-build

コマンド: `cd lean && timeout 180s lake build --wfail <下記10module>`

```text
Build completed successfully (620 jobs).
```
終了コード: `0`。

対象10modules:

```text
GeneralDictionaryRecursiveEvidence
GeneralDictionaryRecursiveEvidenceFacts
GeneralDictionaryRecursiveEvidenceReadback
GeneralDictionaryRecursiveObstruction
GeneralDictionaryRecursiveObstructionEvidence
GeneralDictionaryRecursiveOrder
GeneralDictionaryRecursivePreparation
GeneralDictionaryRecursiveReadback
GeneralDictionaryRecursiveRecordingExamples
GeneralDictionaryRecursiveSemanticOrder
```

### report-audit

コマンド: `cd lean && timeout 180s env LEAN_PATH=.lake/build/lib/lean lean --trust=0 ../cache/yulang130/FinalAudit.lean`

```text
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_iff_payload' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.instance_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_exists' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_node' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_of_branch' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_elim' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_leaf_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.boundary_node_of_branch' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.boundary_evidenceNode_independent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.branch_models_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.capture_occurs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.generated_scalar_equation' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.generated_output_binder_equation' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.instance_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.instance_children_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.indexed_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.reconstruct_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_readback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveEvidence.evidence_fixed_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.query_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.report_calculated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.schema_calculated' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.good_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.metadata' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.not_pending' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.not_rootK2' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.not_candidateK2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.not_inspection_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.bad_original_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.bad_private_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.bad_output_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.bad_not_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.original_model_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.output_provenance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.classified_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode_of_output_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.no_dictionarySound_of_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.branch_iff_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.instance_output_sound' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.bad_not_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.evidence_output_sound' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.evidence_iff_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.bad_not_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.good_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.classified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveObstruction.concrete_evidence_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveOrder.bindings_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveOrder.frame_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveOrder.frames_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveOrder.reconstruct_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveOrder.prepare_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursivePreparation.prepare_candidate_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursivePreparation.prepare_source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursivePreparation.prepare_uniform_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.bindings_found' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.survivor_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.evidence_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.reconstruct_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.output_atoms_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.good_recorded_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.bad_not_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_strict_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.candidate_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.reconstruct_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.compound_head_deferred' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_iff_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_uniform_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveSemanticOrder.generated_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveSemanticOrder.branch_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveSemanticOrder.indexed_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecursiveSemanticOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
```
終了コード: `0`。

scoped audit入力:

```lean
import Yulang.GeneralDictionaryRecursiveEvidence
import Yulang.GeneralDictionaryRecursiveEvidenceFacts
import Yulang.GeneralDictionaryRecursiveEvidenceReadback
import Yulang.GeneralDictionaryRecursiveObstruction
import Yulang.GeneralDictionaryRecursiveObstructionEvidence
import Yulang.GeneralDictionaryRecursiveOrder
import Yulang.GeneralDictionaryRecursivePreparation
import Yulang.GeneralDictionaryRecursiveReadback
import Yulang.GeneralDictionaryRecursiveRecordingExamples
import Yulang.GeneralDictionaryRecursiveSemanticOrder
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_iff_payload
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.instance_models
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_exists
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_node
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_of_branch
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_node_elim
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_leaf_iff
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.boundary_node_of_branch
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.boundary_evidenceNode_independent
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.branch_models_iff
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.capture_occurs
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_capture
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.projected_value_fits_child
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.generated_scalar_equation
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.generated_output_binder_equation
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.instance_plan
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.instance_children_functional
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.indexed_plan
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.reconstruct_evidence
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_readback
#print axioms Yulang.GeneralDictionaryRecursiveEvidence.evidence_fixed_readback
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.registry_checked
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.query_exact
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.report_calculated
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.schema_calculated
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.good_branch
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.metadata
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.linked
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.not_pending
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.prepared
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.survivor
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.not_rootK2
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.not_candidateK2
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.not_inspection_pending
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.safe
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.unique
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.selected
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.bad_original_model
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.bad_private_projection
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.bad_output_equation
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.bad_not_branch
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.original_model_gap
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.output_provenance
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.classified_any
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode_of_output_sound
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.no_dictionarySound_of_unchanged
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.branch_iff_output
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.instance_output_sound
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.bad_not_instance
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.evidence_output_sound
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.evidence_iff_output
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.bad_not_evidence
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.good_evidence
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.classified
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.no_evidenceNode
#print axioms Yulang.GeneralDictionaryRecursiveObstruction.concrete_evidence_gap
#print axioms Yulang.GeneralDictionaryRecursiveOrder.report_reorders
#print axioms Yulang.GeneralDictionaryRecursiveOrder.bindings_reorders
#print axioms Yulang.GeneralDictionaryRecursiveOrder.frame_reorders
#print axioms Yulang.GeneralDictionaryRecursiveOrder.frames_reorders
#print axioms Yulang.GeneralDictionaryRecursiveOrder.reconstruct_reorders
#print axioms Yulang.GeneralDictionaryRecursiveOrder.prepare_reorders
#print axioms Yulang.GeneralDictionaryRecursivePreparation.prepare_candidate_evidence
#print axioms Yulang.GeneralDictionaryRecursivePreparation.prepare_source_evidence
#print axioms Yulang.GeneralDictionaryRecursivePreparation.prepare_uniform_joint
#print axioms Yulang.GeneralDictionaryRecursiveReadback.bindings_found
#print axioms Yulang.GeneralDictionaryRecursiveReadback.survivor_plan
#print axioms Yulang.GeneralDictionaryRecursiveReadback.evidence_plan
#print axioms Yulang.GeneralDictionaryRecursiveReadback.reconstruct_candidate
#print axioms Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_readback
#print axioms Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_unique
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.output_atoms_exact
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_exact
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.good_recorded_model
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.bad_not_recorded
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_strict_nonempty
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.candidate_tree
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.reconstruct_exact
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.compound_head_deferred
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_models_iff_evidence
#print axioms Yulang.GeneralDictionaryRecursiveRecordingExamples.recorded_uniform_evidence
#print axioms Yulang.GeneralDictionaryRecursiveSemanticOrder.generated_reorders
#print axioms Yulang.GeneralDictionaryRecursiveSemanticOrder.branch_reorders
#print axioms Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders_forward
#print axioms Yulang.GeneralDictionaryRecursiveSemanticOrder.instance_reorders
#print axioms Yulang.GeneralDictionaryRecursiveSemanticOrder.indexed_reorders
#print axioms Yulang.GeneralDictionaryRecursiveSemanticOrder.evidence_reorders
```

### report-runtime

コマンド: `cd lean && timeout 180s env LEAN_PATH=.lake/build/lib/lean lean --trust=0 ../cache/yulang130/Runtime.lean`

```text
some (300, 40, 0)
false
2
```
終了コード: `0`。

runtime入力:

```lean
import Yulang.GeneralDictionaryRecursiveRecordingExamples
open Yulang
open GeneralDictionaryRecursiveObstruction
#eval (GeneralDictionaryRecursiveReadback.reconstruct registry registry_checked context (.node 40 []) root).map
  (fun tree => match tree with | .node occurrence key children => (occurrence.identity, key, children.length))
#eval (GeneralDictionaryRecursivePreparation.prepare registry registry_checked context (.node 40 []) root).isSome
#eval GeneralDictionaryRecursiveRecordingExamples.outputAtoms.length
```

### report-gate

コマンド: `bash tools/verify-lean.sh . 9230c133c9627cab9504fa6c26a644c9fd9f6ad1 --no-build`

```text
verify-lean: . @ 66da84fe0 (base 9230c133c9627cab9504fa6c26a644c9fd9f6ad1)
ok: no removed lines in lean/ since 9230c133c9627cab9504fa6c26a644c9fd9f6ad1
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```
終了コード: `0`。

`git diff --check`もexit0、出力なし。最終89定理の全signatureは[別紙](dots-cycle-130-theorems.md)へ全文転載した。`metadata-signatures.exit`は0。新公理なし。

## Hosted CI（local結果とは別）

最終sourceの [Lean inference kernel](https://github.com/momota1029/yulang/actions/runs/43138729619) と [Core CI](https://github.com/momota1029/yulang/actions/runs/43138729661) はともにcompleted/success。proof job130920244184の取得ログにfull build1489jobs、audit9523entriesを確認。全89新定理を照合し欠落0。全audit entriesを再解析しpropext/Classical.choice/Quot.sound以外0。source/value/regular/semantic record exampleのstepもsuccess。

```text
ℹ [1224/1489] Replayed Yulang.SpecConformanceIndex
✔ [1481/1489] Built Yulang.GeneralDictionaryRecursiveOrder (933ms)
✔ [1482/1489] Built Yulang.GeneralDictionaryRecursiveEvidence (1.1s)
✔ [1483/1489] Built Yulang.GeneralDictionaryRecursiveObstructionEvidence (950ms)
✔ [1484/1489] Built Yulang.GeneralDictionaryRecursiveEvidenceFacts (1.2s)
✔ [1485/1489] Built Yulang.GeneralDictionaryRecursiveEvidenceReadback (1.3s)
✔ [1486/1489] Built Yulang.GeneralDictionaryRecursiveRecordingExamples (956ms)
✔ [1487/1489] Built Yulang.GeneralDictionaryRecursiveSemanticOrder (962ms)
✔ [1488/1489] Built Yulang (1.0s)
Build completed successfully (1489 jobs).
```

途中checkpoint0fb161de5adc6813865ed10bfa86e41e5c7992a8もCore43136327660、Lean43136327650がsuccess、full1481jobs。途中70a009ec0e46d14312ee758440e108f06e01a97cはCore43137540794、Lean43137540841がsuccess、full1484jobs、9484audit entries。初回集計9205はdepends-on行だけの数だった。no-axiom行238を加えた全件数は9443。これらは最終Metadata guard強化前であり、最終成果として4c84d2fcを用いる。

## 公開とtree照合

GitHub appでwork/dots-mainのみに公開。blob/tree/commitを作りexpected_sha付きnon-force ref更新。各source checkpointでrecursive treeを取得し、local git ls-tree -rの全tracked path/mode/type/blobを照合。truncated=false、欠落/余剰/不一致0。

| 公開commit | tree | tracked files |
| --- | --- | --- |
| 0fb161de5adc6813865ed10bfa86e41e5c7992a8 | 7880983ca21d30c538a3dcb8f2d453d2fcffcc67 | 2535 |
| 70a009ec0e46d14312ee758440e108f06e01a97c | b797094a07aff724db715f0bb0d31168851cd512 | 2539 |
| 4c84d2fcb0b8fc71cfe625178a4ba3562a126998 | e1b5b75ae0bff4a9932e459fa881106a59bed3eb | 2544 |

報告3filesを追加した最終tree/commitと照合件数はcompleted heartbeatに記録する。報告中に自身のcommit hashは循環参照になるため埋めない。

## 途中の失敗・修正と再検証

初回PATHにlakeがなく127、toolchain PATH指定で解消。長い処理はtimeout付きbackground実行。以下には途中の失敗も全文残す。途中コマンド表記は対象と引数の正規化で、最終scriptは上の全文が実行形。124はtimeoutでありPASSではない。readback aliasのrewriteを修正、semantic orderのroles implicitと依存rewriteを修正し、最終全対象620jobsとaudit89件を再実行済み。workerが親のcache更新中に一時的な依存olean未取得になった件も再実行で解消。

### upstream-build

コマンド: `cd lean && lake build --wfail Yulang.GeneralNominalRecursiveCandidates Yulang.GeneralNominalLocalBoundary`

```text
✔ [562/586] Built Yulang.CommonNominalFullFiniteMaskOrder (4.8s)
✔ [563/586] Built Yulang.CommonNominalFullLayerCongruence (887ms)
✔ [564/586] Built Yulang.CommonRecursiveNominalIntervals (6.2s)
✔ [565/586] Built Yulang.CommonNominalFullGuardedClosure (1.2s)
✔ [566/586] Built Yulang.GeneralNominalK2Coverage (7.1s)
✔ [567/586] Built Yulang.GeneralNominalRegressions (7.4s)
✔ [568/586] Built Yulang.GeneralNominalIntervalLaws (2.6s)
✔ [569/586] Built Yulang.GeneralNominalLocalBoundary (2.0s)
✔ [570/586] Built Yulang.GeneralNominalProjections (1.6s)
✔ [571/586] Built Yulang.GeneralNominalMixedRecurrence (1.7s)
✔ [572/586] Built Yulang.GeneralNominalProjectionPropagation (1.7s)
✔ [573/586] Built Yulang.GeneralNominalIntervalExamples (1.9s)
✔ [574/586] Built Yulang.GeneralNominalEmissionOrigins (2.0s)
✔ [575/586] Built Yulang.GeneralNominalCaptureMerges (2.3s)
✔ [576/586] Built Yulang.GeneralNominalRecursiveInspection (7.8s)
✔ [577/586] Built Yulang.GeneralNominalStructuralProjectionLaws (2.2s)
✔ [578/586] Built Yulang.GeneralNominalMaterialization (2.8s)
✔ [579/586] Built Yulang.GeneralNominalRecursiveCandidates (2.1s)
✔ [580/586] Built Yulang.GeneralNominalRecursiveBoundary (1.7s)
✔ [581/586] Built Yulang.GeneralNominalUnaryCaptureFacts (1.8s)
✔ [582/586] Built Yulang.GeneralNominalMixedExamples (1.9s)
✔ [583/586] Built Yulang.GeneralNominalRecursiveExamples (2.3s)
✔ [584/586] Built Yulang.GeneralNominalRecursiveRegressions (2.6s)
✔ [585/586] Built Yulang.GeneralNominalMixedCandidateExample (2.7s)
✔ [586/586] Built Yulang.GeneralNominalNonpointInspectionExamples (3.2s)
Build completed successfully (586 jobs).
```
終了コード: `0`。

### readback-build

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursiveReadback`

```text
✖ [571/571] Building Yulang.GeneralDictionaryRecursiveReadback (1.3s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/labo-cycle128/toolchain/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryRecursiveReadback.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryRecursiveReadback.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryRecursiveReadback.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryRecursiveReadback.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryRecursiveReadback.setup.json --json
error: Yulang/GeneralDictionaryRecursiveReadback.lean:45:16: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  GeneralDictionaryNominalCandidateReadback.declaration registry root key
in the target expression
  (match declaration registry root key, GeneralNominalRecursiveCandidates.arguments context root with
    | some selected, some bounds =>
      GeneralNominalRecursiveInspection.bindings context.state
        (GeneralNominalRecursiveCandidates.report context selected bounds)
    | x, x_1 => []) =
    GeneralNominalRecursiveInspection.bindings context.state
      (GeneralNominalRecursiveCandidates.report context selected bounds)

registry : Registry
checked : Checked registry
context : Context
root : Occurrence registry.roles
key : Nat
selected : Declaration
visible : selected ∈ registry.declarations
identity : selected.id = key
role : selected.role = root.demand.role
bounds : List (GeneralNominalInspection.Bounds context.state)
located : GeneralNominalRecursiveCandidates.arguments context root = some bounds
⊢ (match declaration registry root key, GeneralNominalRecursiveCandidates.arguments context root with
    | some selected, some bounds =>
      GeneralNominalRecursiveInspection.bindings context.state
        (GeneralNominalRecursiveCandidates.report context selected bounds)
    | x, x_1 => []) =
    GeneralNominalRecursiveInspection.bindings context.state
      (GeneralNominalRecursiveCandidates.report context selected bounds)
Some required targets logged failures:
- Yulang.GeneralDictionaryRecursiveReadback
error: build failed
```
終了コード: `1`。

### readback-build2

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursiveReadback`

```text
✔ [571/571] Built Yulang.GeneralDictionaryRecursiveReadback (2.1s)
Build completed successfully (571 jobs).
```
終了コード: `0`。

### preparation-direct

コマンド: `cd lean && timeout 45s lean --trust=0 Yulang/GeneralDictionaryRecursivePreparation.lean`

```text
(stdout/stderrなし)
```
終了コード: `124`。

### preparation-build

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursivePreparation`

```text
✔ [593/593] Built Yulang.GeneralDictionaryRecursivePreparation (87s)
Build completed successfully (593 jobs).
```
終了コード: `0`。

### checkpoint-audit

コマンド: `cd lean && timeout 120s lake env lean --trust=0 ../cache/yulang130/CheckpointAudit.lean`

```text
(stdout/stderrなし)
```
終了コード: `124`。

### checkpoint-audit-direct

コマンド: `cd lean && timeout 300s env LEAN_PATH=.lake/build/lib/lean lean --trust=0 ../cache/yulang130/CheckpointAudit.lean`

```text
'Yulang.GeneralDictionaryRecursiveReadback.bindings_found' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.survivor_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.evidence_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.reconstruct_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursiveReadback.payload_candidate_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursivePreparation.prepare_candidate_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursivePreparation.prepare_source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecursivePreparation.prepare_uniform_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
終了コード: `0`。

### evidence-obstruction-build

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursiveEvidence Yulang.GeneralDictionaryRecursiveObstruction Yulang.GeneralDictionaryRecursiveEvidenceReadback`

```text
✔ [583/584] Built Yulang.GeneralDictionaryRecursiveEvidence (186s)
✔ [584/584] Built Yulang.GeneralDictionaryRecursiveObstruction (187s)
Build completed successfully (584 jobs).
```
終了コード: `0`。

### recording-build

コマンド: `cd lean && timeout 240s lake build --wfail Yulang.GeneralDictionaryRecursiveRecordingExamples`

```text
(stdout/stderrなし)
```
終了コード: `124`。

### recording-direct

コマンド: `cd lean && env LEAN_PATH=.lake/build/lib/lean lean --trust=0 Yulang/GeneralDictionaryRecursiveRecordingExamples.lean`

```text
(stdout/stderrなし)
```
終了コード: `0`。

### order-build

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursiveOrder`

```text
✔ [597/597] Built Yulang.GeneralDictionaryRecursiveOrder (103s)
Build completed successfully (597 jobs).
```
終了コード: `0`。

### final-components-build

コマンド: `cd lean && lake build --wfail <EvidenceFacts/ObstructionEvidence/RecordingExamples/SemanticOrder>`

```text
✔ [616/619] Built Yulang.GeneralDictionaryRecursiveEvidenceFacts (2.5s)
✔ [617/619] Built Yulang.GeneralDictionaryRecursiveObstructionEvidence (2.5s)
✔ [618/619] Built Yulang.GeneralDictionaryRecursiveRecordingExamples (1.3s)
✖ [619/619] Building Yulang.GeneralDictionaryRecursiveSemanticOrder (1.4s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/labo-cycle128/toolchain/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryRecursiveSemanticOrder.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryRecursiveSemanticOrder.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryRecursiveSemanticOrder.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryRecursiveSemanticOrder.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryRecursiveSemanticOrder.setup.json --json
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:35:15: don't know how to synthesize implicit argument `α`
  @Eq ((clause : Clause) → GeneralDeclarationDemands.Allocation ?m.20 clause)
    (GeneralNominalAllocation.allocation context.state
      { constructors := constructors, roles := roles, declarations := first } root.identity a.id)
    (GeneralNominalAllocation.allocation context.state
      { constructors := constructors, roles := roles, declarations := last } root.identity b.id)
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
context : Context
root : Occurrence roles
a b : Declaration
order : DeclarationReorders a b
ac : DeclarationChecked constructors roles a
bc : DeclarationChecked constructors roles b
bounds : List (GeneralNominalInspection.Bounds context.state)
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
cap :
  GeneralNominalAllocation.capture context.state { constructors := constructors, roles := roles, declarations := first }
      root.identity a.id (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds)) =
    GeneralNominalAllocation.capture context.state
      { constructors := constructors, roles := roles, declarations := last } root.identity b.id
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
⊢ Type
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:36:6: don't know how to synthesize implicit argument `roles`
  @GeneralNominalAllocation.allocation ?m.20 context.state
    { constructors := constructors, roles := roles, declarations := last } root.identity b.id
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
context : Context
root : Occurrence roles
a b : Declaration
order : DeclarationReorders a b
ac : DeclarationChecked constructors roles a
bc : DeclarationChecked constructors roles b
bounds : List (GeneralNominalInspection.Bounds context.state)
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
cap :
  GeneralNominalAllocation.capture context.state { constructors := constructors, roles := roles, declarations := first }
      root.identity a.id (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds)) =
    GeneralNominalAllocation.capture context.state
      { constructors := constructors, roles := roles, declarations := last } root.identity b.id
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
⊢ Roles.RoleDecls
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:35:15: don't know how to synthesize implicit argument `roles`
  @GeneralNominalAllocation.allocation ?m.20 context.state
    { constructors := constructors, roles := roles, declarations := first } root.identity a.id
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
context : Context
root : Occurrence roles
a b : Declaration
order : DeclarationReorders a b
ac : DeclarationChecked constructors roles a
bc : DeclarationChecked constructors roles b
bounds : List (GeneralNominalInspection.Bounds context.state)
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
cap :
  GeneralNominalAllocation.capture context.state { constructors := constructors, roles := roles, declarations := first }
      root.identity a.id (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds)) =
    GeneralNominalAllocation.capture context.state
      { constructors := constructors, roles := roles, declarations := last } root.identity b.id
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
⊢ Roles.RoleDecls
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:26:104: unsolved goals
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
context : Context
root : Occurrence roles
a b : Declaration
order : DeclarationReorders a b
ac : DeclarationChecked constructors roles a
bc : DeclarationChecked constructors roles b
bounds : List (GeneralNominalInspection.Bounds context.state)
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
cap :
  GeneralNominalAllocation.capture context.state { constructors := constructors, roles := roles, declarations := first }
      root.identity a.id (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds)) =
    GeneralNominalAllocation.capture context.state
      { constructors := constructors, roles := roles, declarations := last } root.identity b.id
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
⊢ GeneralNominalMaterialization.generated context.state context.interpretation
      (GeneralNominalMaterialization.rootRequests a root ++
        List.flatMap GeneralNominalMaterialization.emissionRequests
          (GeneralCanonicalChildOrder.canonicalEmit root.identity a ac
            (GeneralNominalAllocation.capture context.state
              { constructors := constructors, roles := roles, declarations := first } root.identity a.id
              (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds)))
            (GeneralNominalAllocation.allocation context.state
              { constructors := constructors, roles := roles, declarations := first } root.identity a.id))) =
    GeneralNominalMaterialization.generated context.state context.interpretation
      (GeneralNominalMaterialization.rootRequests b root ++
        List.flatMap GeneralNominalMaterialization.emissionRequests
          (GeneralCanonicalChildOrder.canonicalEmit root.identity b bc
            (GeneralNominalAllocation.capture context.state
              { constructors := constructors, roles := roles, declarations := last } root.identity b.id
              (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
            (GeneralNominalAllocation.allocation context.state
              { constructors := constructors, roles := roles, declarations := last } root.identity b.id)))
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:57:6: Tactic `rewrite` failed: motive is not type correct:
  fun _a =>
    GeneralNominalState.Models context.state model ∧
        GeneralNominalAllocation.Compatible
            (bindings context.state (GeneralNominalRecursiveCandidates.report context _a bounds)) model ∧
          PresenceNormalForm.All CommonNominalFullCarrier.model model
              (GeneralNominalAllocation.merges context.state
                { constructors := constructors, roles := roles, declarations := first } root.identity a
                (bindings context.state (GeneralNominalRecursiveCandidates.report context _a bounds))) ∧
            PresenceNormalForm.All CommonNominalFullCarrier.model model
                (GeneralNominalRecursiveInspection.selfChecks context.state
                  (GeneralNominalRecursiveCandidates.report context _a bounds)) ∧
              GeneralNominalRecursiveInspection.ProjectionModels context.state
                  (GeneralNominalRecursiveCandidates.report context _a bounds) model ∧
                GeneralNominalMaterialization.Models context.state a
                  (GeneralNominalAllocation.capture context.state
                    { constructors := constructors, roles := roles, declarations := first } root.identity a.id
                    (bindings context.state (GeneralNominalRecursiveCandidates.report context _a bounds)))
                  (GeneralNominalRecursiveCandidates.report context _a bounds)
                  (GeneralNominalRecursiveCandidates.generated
                    { constructors := constructors, roles := roles, declarations := last } context root _a bc bounds)
                  model ↔
      GeneralNominalState.Models context.state model ∧
        GeneralNominalAllocation.Compatible
            (bindings context.state (GeneralNominalRecursiveCandidates.report context _a bounds)) model ∧
          PresenceNormalForm.All CommonNominalFullCarrier.model model
              (GeneralNominalAllocation.merges context.state
                { constructors := constructors, roles := roles, declarations := last } root.identity _a
                (bindings context.state (GeneralNominalRecursiveCandidates.report context _a bounds))) ∧
            PresenceNormalForm.All CommonNominalFullCarrier.model model
                (GeneralNominalRecursiveInspection.selfChecks context.state
                  (GeneralNominalRecursiveCandidates.report context _a bounds)) ∧
              GeneralNominalRecursiveInspection.ProjectionModels context.state
                  (GeneralNominalRecursiveCandidates.report context _a bounds) model ∧
                GeneralNominalMaterialization.Models context.state _a
                  (GeneralNominalAllocation.capture context.state
                    { constructors := constructors, roles := roles, declarations := last } root.identity _a.id
                    (bindings context.state (GeneralNominalRecursiveCandidates.report context _a bounds)))
                  (GeneralNominalRecursiveCandidates.report context _a bounds)
                  (GeneralNominalRecursiveCandidates.generated
                    { constructors := constructors, roles := roles, declarations := last } context root _a bc bounds)
                  model
Error: Application type mismatch: The argument
  bc
has type
  DeclarationChecked constructors roles b
but is expected to have type
  DeclarationChecked { constructors := constructors, roles := roles, declarations := last }.constructors roles _a
in the application
  GeneralNominalRecursiveCandidates.generated { constructors := constructors, roles := roles, declarations := last }
    context root _a bc

Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that 'congrArg' implies that 'm a = m b', which can be used with lemmas such as 'Eq.mpr' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.

Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).

constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
context : Context
root : Occurrence roles
a b : Declaration
order : DeclarationReorders a b
ac : DeclarationChecked constructors roles a
bc : DeclarationChecked constructors roles b
bounds : List (GeneralNominalInspection.Bounds context.state)
model : GeneralNominalCommonBridge.Assignment
⊢ GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible
          (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
            (GeneralNominalAllocation.merges context.state
              { constructors := constructors, roles := roles, declarations := first } root.identity a
              (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))) ∧
          PresenceNormalForm.All CommonNominalFullCarrier.model model
              (GeneralNominalRecursiveInspection.selfChecks context.state
                (GeneralNominalRecursiveCandidates.report context b bounds)) ∧
            GeneralNominalRecursiveInspection.ProjectionModels context.state
                (GeneralNominalRecursiveCandidates.report context b bounds) model ∧
              GeneralNominalMaterialization.Models context.state a
                (GeneralNominalAllocation.capture context.state
                  { constructors := constructors, roles := roles, declarations := first } root.identity a.id
                  (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
                (GeneralNominalRecursiveCandidates.report context b bounds)
                (GeneralNominalRecursiveCandidates.generated
                  { constructors := constructors, roles := roles, declarations := last } context root b bc bounds)
                model ↔
    GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible
          (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
            (GeneralNominalAllocation.merges context.state
              { constructors := constructors, roles := roles, declarations := last } root.identity b
              (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))) ∧
          PresenceNormalForm.All CommonNominalFullCarrier.model model
              (GeneralNominalRecursiveInspection.selfChecks context.state
                (GeneralNominalRecursiveCandidates.report context b bounds)) ∧
            GeneralNominalRecursiveInspection.ProjectionModels context.state
                (GeneralNominalRecursiveCandidates.report context b bounds) model ∧
              GeneralNominalMaterialization.Models context.state b
                (GeneralNominalAllocation.capture context.state
                  { constructors := constructors, roles := roles, declarations := last } root.identity b.id
                  (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
                (GeneralNominalRecursiveCandidates.report context b bounds)
                (GeneralNominalRecursiveCandidates.generated
                  { constructors := constructors, roles := roles, declarations := last } context root b bc bounds)
                model
Some required targets logged failures:
- Yulang.GeneralDictionaryRecursiveSemanticOrder
error: build failed
```
終了コード: `1`。

### semantic-order-build2

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursiveSemanticOrder`

```text
✖ [602/602] Building Yulang.GeneralDictionaryRecursiveSemanticOrder (2.2s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/labo-cycle128/toolchain/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryRecursiveSemanticOrder.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryRecursiveSemanticOrder.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryRecursiveSemanticOrder.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryRecursiveSemanticOrder.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryRecursiveSemanticOrder.setup.json --json
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:52:79: unsolved goals
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
context : Context
root : Occurrence roles
a b : Declaration
order : DeclarationReorders a b
ac : DeclarationChecked constructors roles a
bc : DeclarationChecked constructors roles b
bounds : List (GeneralNominalInspection.Bounds context.state)
model : GeneralNominalCommonBridge.Assignment
⊢ (GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible
          (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
            (List.flatMap
              (fun name =>
                match
                  GeneralNominalAllocation.occurrences
                    (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) name with
                | [head] => []
                | bounds_1 =>
                  GeneralNominalAllocation.equations
                      (match
                          GeneralNominalAllocation.occurrences
                            (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
                            name with
                        | [bounds] => bounds
                        | x =>
                          (GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 0 name 0),
                            GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 1 name 0))).fst
                      (GeneralNominalAllocation.lower bounds_1) ++
                    GeneralNominalAllocation.equations
                      (match
                          GeneralNominalAllocation.occurrences
                            (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
                            name with
                        | [bounds] => bounds
                        | x =>
                          (GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 0 name 0),
                            GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 1 name 0))).snd
                      (GeneralNominalAllocation.upper bounds_1))
              (GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs b.head))) ∧
          PresenceNormalForm.All CommonNominalFullCarrier.model model
              (GeneralNominalRecursiveInspection.selfChecks context.state
                (GeneralNominalRecursiveCandidates.report context b bounds)) ∧
            GeneralNominalRecursiveInspection.ProjectionModels context.state
                (GeneralNominalRecursiveCandidates.report context b bounds) model ∧
              (∀ (test : GeneralNominalRecursiveInspection.Origin × GeneralNominalRecursiveInspection.Test),
                  test ∈
                      (GeneralNominalRecursiveCandidates.generated
                          { constructors := constructors, roles := roles, declarations := last } context root b bc
                          bounds).tests →
                    (∃ actual, GeneralNominalRecursiveInspection.Observes model test.fst actual) ∧
                      ∀ (actual : CommonNominalFullCarrier.Ty),
                        GeneralNominalRecursiveInspection.Observes model test.fst actual → test.snd.Holds actual) ∧
                (∀ (entry : GeneralNominalMaterialization.Use),
                    entry ∈
                        (GeneralNominalRecursiveCandidates.generated
                            { constructors := constructors, roles := roles, declarations := last } context root b bc
                            bounds).variables →
                      (∃ actual, GeneralNominalRecursiveInspection.Observes model entry.origin actual) ∧
                        ∀ (actual : CommonNominalFullCarrier.Ty),
                          GeneralNominalRecursiveInspection.Observes model entry.origin actual →
                            if entry.name ∈ List.map OutputBinder.name b.outputBinders then
                              CommonNominalFullCarrier.Equivalent actual
                                (model
                                    (GeneralNominalIdentities.source context.state.seed
                                      (GeneralNominalAllocation.origin root.identity b.id 2 entry.name 0))).fst
                            else
                              match entry.mode with
                              | GeneralNominalMaterialization.Mode.lower =>
                                CommonNominalFullCarrier.Equivalent actual
                                  (model
                                      (match
                                          GeneralNominalAllocation.occurrences
                                            (bindings context.state
                                              (GeneralNominalRecursiveCandidates.report context b bounds))
                                            entry.name with
                                        | [bounds] => bounds
                                        | x =>
                                          (GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 0 entry.name 0),
                                            GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 1 entry.name
                                                0))).fst).fst
                              | GeneralNominalMaterialization.Mode.upper =>
                                CommonNominalFullCarrier.Equivalent actual
                                  (model
                                      (match
                                          GeneralNominalAllocation.occurrences
                                            (bindings context.state
                                              (GeneralNominalRecursiveCandidates.report context b bounds))
                                            entry.name with
                                        | [bounds] => bounds
                                        | x =>
                                          (GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 0 entry.name 0),
                                            GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 1 entry.name
                                                0))).snd).fst
                              | GeneralNominalMaterialization.Mode.actual =>
                                GeneralNominalCaptureMerges.Fits model
                                  (match
                                    GeneralNominalAllocation.occurrences
                                      (bindings context.state
                                        (GeneralNominalRecursiveCandidates.report context b bounds))
                                      entry.name with
                                  | [bounds] => bounds
                                  | x =>
                                    (GeneralNominalIdentities.source context.state.seed
                                        (GeneralNominalAllocation.origin root.identity b.id 0 entry.name 0),
                                      GeneralNominalIdentities.source context.state.seed
                                        (GeneralNominalAllocation.origin root.identity b.id 1 entry.name 0)))
                                  actual) ∧
                  (∀ (first : GeneralNominalMaterialization.Use),
                      first ∈
                          (GeneralNominalRecursiveCandidates.generated
                              { constructors := constructors, roles := roles, declarations := last } context root b bc
                              bounds).variables →
                        ∀ (last_1 : GeneralNominalMaterialization.Use),
                          last_1 ∈
                              (GeneralNominalRecursiveCandidates.generated
                                  { constructors := constructors, roles := roles, declarations := last } context root b
                                  bc bounds).variables →
                            first.name = last_1.name →
                              first.mode = GeneralNominalMaterialization.Mode.actual →
                                last_1.mode = GeneralNominalMaterialization.Mode.actual →
                                  ∀ (a b : CommonNominalFullCarrier.Ty),
                                    GeneralNominalRecursiveInspection.Observes model first.origin a →
                                      GeneralNominalRecursiveInspection.Observes model last_1.origin b →
                                        CommonNominalFullCarrier.Equivalent a b) ∧
                    ∀ (entry : GeneralNominalMaterialization.Use),
                      entry ∈
                          (GeneralNominalRecursiveCandidates.generated
                              { constructors := constructors, roles := roles, declarations := last } context root b bc
                              bounds).variables →
                        ∀ (captured : GeneralNominalRecursiveInspection.Capture context.state),
                          captured ∈ (GeneralNominalRecursiveCandidates.report context b bounds).captures →
                            entry.name = captured.name →
                              entry.mode = GeneralNominalMaterialization.Mode.actual →
                                ∀ (origin : GeneralNominalRecursiveInspection.Origin),
                                  captured.origin = some origin →
                                    ∀ (a b : CommonNominalFullCarrier.Ty),
                                      GeneralNominalRecursiveInspection.Observes model entry.origin a →
                                        GeneralNominalRecursiveInspection.Observes model origin b →
                                          CommonNominalFullCarrier.Equivalent a b) ↔
    GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible
          (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
            (List.flatMap
              (fun name =>
                match
                  GeneralNominalAllocation.occurrences
                    (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)) name with
                | [head] => []
                | bounds_1 =>
                  GeneralNominalAllocation.equations
                      (match
                          GeneralNominalAllocation.occurrences
                            (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
                            name with
                        | [bounds] => bounds
                        | x =>
                          (GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 0 name 0),
                            GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 1 name 0))).fst
                      (GeneralNominalAllocation.lower bounds_1) ++
                    GeneralNominalAllocation.equations
                      (match
                          GeneralNominalAllocation.occurrences
                            (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
                            name with
                        | [bounds] => bounds
                        | x =>
                          (GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 0 name 0),
                            GeneralNominalIdentities.source context.state.seed
                              (GeneralNominalAllocation.origin root.identity b.id 1 name 0))).snd
                      (GeneralNominalAllocation.upper bounds_1))
              (GeneralDeclarationPatterns.variablesArgs (GeneralDeclarationPatterns.normalizeArgs b.head))) ∧
          PresenceNormalForm.All CommonNominalFullCarrier.model model
              (GeneralNominalRecursiveInspection.selfChecks context.state
                (GeneralNominalRecursiveCandidates.report context b bounds)) ∧
            GeneralNominalRecursiveInspection.ProjectionModels context.state
                (GeneralNominalRecursiveCandidates.report context b bounds) model ∧
              (∀ (test : GeneralNominalRecursiveInspection.Origin × GeneralNominalRecursiveInspection.Test),
                  test ∈
                      (GeneralNominalRecursiveCandidates.generated
                          { constructors := constructors, roles := roles, declarations := last } context root b bc
                          bounds).tests →
                    (∃ actual, GeneralNominalRecursiveInspection.Observes model test.fst actual) ∧
                      ∀ (actual : CommonNominalFullCarrier.Ty),
                        GeneralNominalRecursiveInspection.Observes model test.fst actual → test.snd.Holds actual) ∧
                (∀ (entry : GeneralNominalMaterialization.Use),
                    entry ∈
                        (GeneralNominalRecursiveCandidates.generated
                            { constructors := constructors, roles := roles, declarations := last } context root b bc
                            bounds).variables →
                      (∃ actual, GeneralNominalRecursiveInspection.Observes model entry.origin actual) ∧
                        ∀ (actual : CommonNominalFullCarrier.Ty),
                          GeneralNominalRecursiveInspection.Observes model entry.origin actual →
                            if entry.name ∈ List.map OutputBinder.name b.outputBinders then
                              CommonNominalFullCarrier.Equivalent actual
                                (model
                                    (GeneralNominalIdentities.source context.state.seed
                                      (GeneralNominalAllocation.origin root.identity b.id 2 entry.name 0))).fst
                            else
                              match entry.mode with
                              | GeneralNominalMaterialization.Mode.lower =>
                                CommonNominalFullCarrier.Equivalent actual
                                  (model
                                      (match
                                          GeneralNominalAllocation.occurrences
                                            (bindings context.state
                                              (GeneralNominalRecursiveCandidates.report context b bounds))
                                            entry.name with
                                        | [bounds] => bounds
                                        | x =>
                                          (GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 0 entry.name 0),
                                            GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 1 entry.name
                                                0))).fst).fst
                              | GeneralNominalMaterialization.Mode.upper =>
                                CommonNominalFullCarrier.Equivalent actual
                                  (model
                                      (match
                                          GeneralNominalAllocation.occurrences
                                            (bindings context.state
                                              (GeneralNominalRecursiveCandidates.report context b bounds))
                                            entry.name with
                                        | [bounds] => bounds
                                        | x =>
                                          (GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 0 entry.name 0),
                                            GeneralNominalIdentities.source context.state.seed
                                              (GeneralNominalAllocation.origin root.identity b.id 1 entry.name
                                                0))).snd).fst
                              | GeneralNominalMaterialization.Mode.actual =>
                                GeneralNominalCaptureMerges.Fits model
                                  (match
                                    GeneralNominalAllocation.occurrences
                                      (bindings context.state
                                        (GeneralNominalRecursiveCandidates.report context b bounds))
                                      entry.name with
                                  | [bounds] => bounds
                                  | x =>
                                    (GeneralNominalIdentities.source context.state.seed
                                        (GeneralNominalAllocation.origin root.identity b.id 0 entry.name 0),
                                      GeneralNominalIdentities.source context.state.seed
                                        (GeneralNominalAllocation.origin root.identity b.id 1 entry.name 0)))
                                  actual) ∧
                  (∀ (first : GeneralNominalMaterialization.Use),
                      first ∈
                          (GeneralNominalRecursiveCandidates.generated
                              { constructors := constructors, roles := roles, declarations := last } context root b bc
                              bounds).variables →
                        ∀ (last_1 : GeneralNominalMaterialization.Use),
                          last_1 ∈
                              (GeneralNominalRecursiveCandidates.generated
                                  { constructors := constructors, roles := roles, declarations := last } context root b
                                  bc bounds).variables →
                            first.name = last_1.name →
                              first.mode = GeneralNominalMaterialization.Mode.actual →
                                last_1.mode = GeneralNominalMaterialization.Mode.actual →
                                  ∀ (a b : CommonNominalFullCarrier.Ty),
                                    GeneralNominalRecursiveInspection.Observes model first.origin a →
                                      GeneralNominalRecursiveInspection.Observes model last_1.origin b →
                                        CommonNominalFullCarrier.Equivalent a b) ∧
                    ∀ (entry : GeneralNominalMaterialization.Use),
                      entry ∈
                          (GeneralNominalRecursiveCandidates.generated
                              { constructors := constructors, roles := roles, declarations := last } context root b bc
                              bounds).variables →
                        ∀ (captured : GeneralNominalRecursiveInspection.Capture context.state),
                          captured ∈ (GeneralNominalRecursiveCandidates.report context b bounds).captures →
                            entry.name = captured.name →
                              entry.mode = GeneralNominalMaterialization.Mode.actual →
                                ∀ (origin : GeneralNominalRecursiveInspection.Origin),
                                  captured.origin = some origin →
                                    ∀ (a b : CommonNominalFullCarrier.Ty),
                                      GeneralNominalRecursiveInspection.Observes model entry.origin a →
                                        GeneralNominalRecursiveInspection.Observes model origin b →
                                          CommonNominalFullCarrier.Equivalent a b
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:88:96: don't know how to synthesize implicit argument `a`
  @rfl (GeneralDictionaryEmissionPlans.Frame ?m.164)
    (GeneralNominalAllocation.frame context.state
      { constructors := constructors, roles := roles, declarations := first } root.identity
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
_one : Checked { constructors := constructors, roles := roles, declarations := first }
two : Checked { constructors := constructors, roles := roles, declarations := last }
order :
  Reorders { constructors := constructors, roles := roles, declarations := first }
    { constructors := constructors, roles := roles, declarations := last }
context : Context
model : GeneralNominalCommonBridge.Assignment
root : Occurrence roles
key : Nat
children : List (Occurrence roles)
a : Declaration
present : a ∈ { constructors := constructors, roles := roles, declarations := first }.declarations
ac : DeclarationChecked { constructors := constructors, roles := roles, declarations := first }.constructors roles a
identity : a.id = key
role : a.role = root.demand.role
bounds : List (GeneralNominalInspection.Bounds context.state)
located : GeneralNominalRecursiveCandidates.arguments context root = some bounds
finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalRecursiveCandidates.report context a bounds)
ready : RequestReady { constructors := constructors, roles := roles, declarations := first } context root a ac bounds
emitted :
  children =
    GeneralNominalAllocation.children context.state
      { constructors := constructors, roles := roles, declarations := first } root a ac
      (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds))
branch :
  BranchModels { constructors := constructors, roles := roles, declarations := first } context root a ac bounds model
b : Declaration
visible : b ∈ { constructors := constructors, roles := roles, declarations := last }.declarations
pair : DeclarationReorders a b
bc :
  DeclarationChecked { constructors := constructors, roles := roles, declarations := last }.constructors
    { constructors := constructors, roles := roles, declarations := last }.roles b
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
⊢ GeneralDictionaryEmissionPlans.Frame ?m.164
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:88:96: don't know how to synthesize implicit argument `α`
  @rfl (GeneralDictionaryEmissionPlans.Frame ?m.164)
    (GeneralNominalAllocation.frame context.state
      { constructors := constructors, roles := roles, declarations := first } root.identity
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
_one : Checked { constructors := constructors, roles := roles, declarations := first }
two : Checked { constructors := constructors, roles := roles, declarations := last }
order :
  Reorders { constructors := constructors, roles := roles, declarations := first }
    { constructors := constructors, roles := roles, declarations := last }
context : Context
model : GeneralNominalCommonBridge.Assignment
root : Occurrence roles
key : Nat
children : List (Occurrence roles)
a : Declaration
present : a ∈ { constructors := constructors, roles := roles, declarations := first }.declarations
ac : DeclarationChecked { constructors := constructors, roles := roles, declarations := first }.constructors roles a
identity : a.id = key
role : a.role = root.demand.role
bounds : List (GeneralNominalInspection.Bounds context.state)
located : GeneralNominalRecursiveCandidates.arguments context root = some bounds
finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalRecursiveCandidates.report context a bounds)
ready : RequestReady { constructors := constructors, roles := roles, declarations := first } context root a ac bounds
emitted :
  children =
    GeneralNominalAllocation.children context.state
      { constructors := constructors, roles := roles, declarations := first } root a ac
      (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds))
branch :
  BranchModels { constructors := constructors, roles := roles, declarations := first } context root a ac bounds model
b : Declaration
visible : b ∈ { constructors := constructors, roles := roles, declarations := last }.declarations
pair : DeclarationReorders a b
bc :
  DeclarationChecked { constructors := constructors, roles := roles, declarations := last }.constructors
    { constructors := constructors, roles := roles, declarations := last }.roles b
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
⊢ Type
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:85:18: don't know how to synthesize implicit argument `α`
  @Eq (GeneralDictionaryEmissionPlans.Frame ?m.164)
    (GeneralNominalAllocation.frame context.state
      { constructors := constructors, roles := roles, declarations := first } root.identity
      (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
    (GeneralNominalAllocation.frame context.state { constructors := constructors, roles := roles, declarations := last }
      root.identity (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds)))
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
_one : Checked { constructors := constructors, roles := roles, declarations := first }
two : Checked { constructors := constructors, roles := roles, declarations := last }
order :
  Reorders { constructors := constructors, roles := roles, declarations := first }
    { constructors := constructors, roles := roles, declarations := last }
context : Context
model : GeneralNominalCommonBridge.Assignment
root : Occurrence roles
key : Nat
children : List (Occurrence roles)
a : Declaration
present : a ∈ { constructors := constructors, roles := roles, declarations := first }.declarations
ac : DeclarationChecked { constructors := constructors, roles := roles, declarations := first }.constructors roles a
identity : a.id = key
role : a.role = root.demand.role
bounds : List (GeneralNominalInspection.Bounds context.state)
located : GeneralNominalRecursiveCandidates.arguments context root = some bounds
finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalRecursiveCandidates.report context a bounds)
ready : RequestReady { constructors := constructors, roles := roles, declarations := first } context root a ac bounds
emitted :
  children =
    GeneralNominalAllocation.children context.state
      { constructors := constructors, roles := roles, declarations := first } root a ac
      (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds))
branch :
  BranchModels { constructors := constructors, roles := roles, declarations := first } context root a ac bounds model
b : Declaration
visible : b ∈ { constructors := constructors, roles := roles, declarations := last }.declarations
pair : DeclarationReorders a b
bc :
  DeclarationChecked { constructors := constructors, roles := roles, declarations := last }.constructors
    { constructors := constructors, roles := roles, declarations := last }.roles b
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
⊢ Type
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:87:6: don't know how to synthesize implicit argument `roles`
  @GeneralNominalAllocation.frame ?m.164 context.state
    { constructors := constructors, roles := roles, declarations := last } root.identity
    (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
_one : Checked { constructors := constructors, roles := roles, declarations := first }
two : Checked { constructors := constructors, roles := roles, declarations := last }
order :
  Reorders { constructors := constructors, roles := roles, declarations := first }
    { constructors := constructors, roles := roles, declarations := last }
context : Context
model : GeneralNominalCommonBridge.Assignment
root : Occurrence roles
key : Nat
children : List (Occurrence roles)
a : Declaration
present : a ∈ { constructors := constructors, roles := roles, declarations := first }.declarations
ac : DeclarationChecked { constructors := constructors, roles := roles, declarations := first }.constructors roles a
identity : a.id = key
role : a.role = root.demand.role
bounds : List (GeneralNominalInspection.Bounds context.state)
located : GeneralNominalRecursiveCandidates.arguments context root = some bounds
finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalRecursiveCandidates.report context a bounds)
ready : RequestReady { constructors := constructors, roles := roles, declarations := first } context root a ac bounds
emitted :
  children =
    GeneralNominalAllocation.children context.state
      { constructors := constructors, roles := roles, declarations := first } root a ac
      (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds))
branch :
  BranchModels { constructors := constructors, roles := roles, declarations := first } context root a ac bounds model
b : Declaration
visible : b ∈ { constructors := constructors, roles := roles, declarations := last }.declarations
pair : DeclarationReorders a b
bc :
  DeclarationChecked { constructors := constructors, roles := roles, declarations := last }.constructors
    { constructors := constructors, roles := roles, declarations := last }.roles b
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
⊢ Roles.RoleDecls
error: Yulang/GeneralDictionaryRecursiveSemanticOrder.lean:85:18: don't know how to synthesize implicit argument `roles`
  @GeneralNominalAllocation.frame ?m.164 context.state
    { constructors := constructors, roles := roles, declarations := first } root.identity
    (bindings context.state (GeneralNominalRecursiveCandidates.report context b bounds))
context:
constructors : GeneralDeclarationPatterns.Constructors
roles : Roles.RoleDecls
first last : List Declaration
_one : Checked { constructors := constructors, roles := roles, declarations := first }
two : Checked { constructors := constructors, roles := roles, declarations := last }
order :
  Reorders { constructors := constructors, roles := roles, declarations := first }
    { constructors := constructors, roles := roles, declarations := last }
context : Context
model : GeneralNominalCommonBridge.Assignment
root : Occurrence roles
key : Nat
children : List (Occurrence roles)
a : Declaration
present : a ∈ { constructors := constructors, roles := roles, declarations := first }.declarations
ac : DeclarationChecked { constructors := constructors, roles := roles, declarations := first }.constructors roles a
identity : a.id = key
role : a.role = root.demand.role
bounds : List (GeneralNominalInspection.Bounds context.state)
located : GeneralNominalRecursiveCandidates.arguments context root = some bounds
finished : GeneralNominalRecursiveInspection.Finished (GeneralNominalRecursiveCandidates.report context a bounds)
ready : RequestReady { constructors := constructors, roles := roles, declarations := first } context root a ac bounds
emitted :
  children =
    GeneralNominalAllocation.children context.state
      { constructors := constructors, roles := roles, declarations := first } root a ac
      (bindings context.state (GeneralNominalRecursiveCandidates.report context a bounds))
branch :
  BranchModels { constructors := constructors, roles := roles, declarations := first } context root a ac bounds model
b : Declaration
visible : b ∈ { constructors := constructors, roles := roles, declarations := last }.declarations
pair : DeclarationReorders a b
bc :
  DeclarationChecked { constructors := constructors, roles := roles, declarations := last }.constructors
    { constructors := constructors, roles := roles, declarations := last }.roles b
rep :
  GeneralNominalRecursiveCandidates.report context a bounds = GeneralNominalRecursiveCandidates.report context b bounds
⊢ Roles.RoleDecls
Some required targets logged failures:
- Yulang.GeneralDictionaryRecursiveSemanticOrder
error: build failed
```
終了コード: `1`。

### semantic-order-build3

コマンド: `cd lean && lake build --wfail Yulang.GeneralDictionaryRecursiveSemanticOrder`

```text
✔ [602/602] Built Yulang.GeneralDictionaryRecursiveSemanticOrder (2.6s)
Build completed successfully (602 jobs).
```
終了コード: `0`。

### metadata-final-build

コマンド: `cd lean && lake build --wfail <全10module>`

```text
✔ [615/620] Built Yulang.GeneralDictionaryRecursiveEvidence (2.9s)
✔ [616/620] Built Yulang.GeneralDictionaryRecursiveEvidenceFacts (1.2s)
✔ [617/620] Built Yulang.GeneralDictionaryRecursiveObstructionEvidence (1.7s)
✔ [618/620] Built Yulang.GeneralDictionaryRecursiveEvidenceReadback (1.8s)
✔ [619/620] Built Yulang.GeneralDictionaryRecursiveSemanticOrder (1.3s)
✔ [620/620] Built Yulang.GeneralDictionaryRecursiveRecordingExamples (1.8s)
Build completed successfully (620 jobs).
```
終了コード: `0`。

## 末尾のfresh fetch、STOP、時間上限

### end-fetch

コマンド: `git fetch origin integration/m1-final work/dots-main work/dots-audit --depth=30`

```text
From https://github.com/momota1029/yulang
 * branch                integration/m1-final -> FETCH_HEAD
 * branch                work/dots-main       -> FETCH_HEAD
 * branch                work/dots-audit      -> FETCH_HEAD
   9230c133c..3fcd14ec6  integration/m1-final -> origin/integration/m1-final
```
終了コード: `0`。

末尾のfresh fetchでintegrationが3fcd14ec614aaf04af1e0bb7fffec30fefcf59bdへ進んでいた。inboxはACTIVE、I-22を確認。新しいAstra Step/Stable/Generated等とK2 spec変更が含まれる。最終source検証後なので未検証の取り込みをせず、次cycleへ明示的に引き継ぐ。今回のtable/証明/CIは9230c133c基準であり、新integrationについての合格を主張しない。

55分総上限は実行時間最低値を求める旧文書より優先。開始基準01:27:19Z、worker割当は01:31台、開始heartbeat公開は約01:33台で「直後」の要件に遅れた。10/20/30分付近と41.74分で時間基準heartbeat公開。40分心拍は02:09:03Zで約1分44秒遅れた。遅れを定刻成功とは記録しない。最終completed heartbeatで所要時間とwriter releaseを確定する。

disk空き37GiB、使用量枠不明。既存cache全体のコピー/削除なし。焦点検証用の個別olean利用は行った。前cycleのcrashなし、source喪失なし、writer競合なし。

