# Cycle129: verification and publication evidence

## Scope and clock

開始: 2026-11-12T00:25:23Z。55分の総上限: 2026-11-12T01:20:23Z。最終終了時刻/elapsedはcompleted heartbeatに記録。
新規18 modules/125 public theorems。一般B4Bridges V3は12/12未充填。既存実装は変更せず、Yulang/Audit/READMEのみ追記。spec/plan/lake config変更なし。
一般Step/I-20、Astra担当項目1/2/3、候補Survivor、source allocatorを完成したとは主張しない。全体lake build/Audit/AxiomGateはlocalでは実行していない。以下のhosted結果とlocal focused結果を区別する。

## Final local verification commands

使用toolchain: Lean4.35.0。既存`.lake`を再利用。各実行に120〜180秒timeoutを付け、バックグラウンドでログとexitを記録。
```sh
cd lean
timeout 180s lake build Yulang.GeneralDictionaryNominalCandidateOrder Yulang.GeneralDictionaryNominalSlotTransport Yulang.GeneralDictionaryTypeCoverage Yulang.GeneralDictionaryTypeCoverageExamples Yulang.GeneralDictionaryNominalCandidateOrderExamples Yulang.GeneralDictionaryNominalBatchTransport Yulang.GeneralDictionaryNominalBatchTransportExamples Yulang.GeneralDictionaryNominalSemanticOrder Yulang.GeneralDictionaryNominalSlotTransportExamples Yulang.GeneralDictionarySlotLocalizationTransport Yulang.GeneralDictionarySlotMaterializationTransport Yulang.GeneralDictionarySlotPreparationTransport Yulang.GeneralDictionarySlotEvidenceTransport Yulang.GeneralDictionarySlotPreparationTransportExamples Yulang.GeneralDictionarySlotFreshnessTransport Yulang.GeneralDictionarySlotFreshnessTransportExamples Yulang.GeneralDictionarySlotViewBoundaryExamples Yulang.GeneralDictionaryFreshSlotPreparationExamples --wfail
timeout 120s lake env lean --trust=0 ../cache/yulang129/FinalAudit.lean
timeout 120s lake env lean --trust=0 ../cache/yulang129/Signatures.lean
timeout 120s lake env lean --trust=0 ../cache/yulang129/Runtime.lean
timeout 120s lake env lean --trust=0 ../cache/yulang129/RuntimeFresh.lean
cd ..
tools/verify-lean.sh . origin/integration/m1-final --no-build
git diff --check
```

FinalAudit.leanは下記18 modulesをimportし、inventoryに載る125定理すべてへ`#print axioms`を実行する。Signatures.leanは同じ125名に`#check @名前`を実行する。全出力の正確な型はtheorems報告に収録。全125名の監査行を照合した。許された公理はpropext/Classical.choice/Quot.soundのみで、それ以外は0。

### final-build

exit code: 0

```text
Build completed successfully (609 jobs).
```

### final-audit

exit code: 0

```text
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.lifted_arrow_separate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.old_item_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_not_collapsed' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.all_assignment_recording_exact' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.realizes_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_instance_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_evidence_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.every_assignment_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.old_coordinates_preserved' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.strict_extension_localizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_bounds_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.sourceSlot_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.locateTerm_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.binder_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.variable_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.headless_locate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.available' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_denotesAt' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_denotes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.materializes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.variable_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.plan_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.headless_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_dictionary' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.headless_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_localize_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.payload_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepared_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.recorded_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepare_uniform_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.preparation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_preparation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.exact_shared_dictionary' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.nonempty_obligations' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.recorded_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_recorded_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.shared_source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.strict_preparation_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.sources_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.sources_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.allocation_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.generated_member_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.fresh_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.unowned_generated_absent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_coordinates_bounded' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.new_coordinates_justified' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_sources_preserved' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_fresh_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_unowned_absent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotViewBoundaryExamples.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotViewBoundaryExamples.known_before' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotViewBoundaryExamples.not_known_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotViewBoundaryExamples.not_pending_before' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotViewBoundaryExamples.pending_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotViewBoundaryExamples.nonvacuous_view_boundary' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFreshSlotPreparationExamples.preparation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFreshSlotPreparationExamples.before_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFreshSlotPreparationExamples.new_reserved_slot' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFreshSlotPreparationExamples.recorded_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFreshSlotPreparationExamples.fresh_source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFreshSlotPreparationExamples.still_pending' depends on axioms: [propext, Quot.sound]
```

### final-gate-corrected

exit code: 0

```text
verify-lean: . @ 6be6722f5 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

### runtime

exit code: 0

```text
some (300, 1, 2)
some (300, 1, 2)
false
true
```

### runtime-fresh

exit code: 0

```text
false
some (301, 1, 2)
```

### Exact signature checks

exit code: 0. 125/125名、全型の省略なし出力は[dots-cycle-129-theorems.md](dots-cycle-129-theorems.md)。

### Runtime probe sources

`Runtime.lean`

```lean
import Yulang.GeneralDictionarySlotPreparationTransportExamples
import Yulang.GeneralDictionaryNominalCandidateOrderExamples
open Yulang
#eval (GeneralDictionaryPayloadPreparation.prepare
  GeneralDictionaryHeadlessFixture.registry GeneralDictionaryHeadlessFixture.registry_checked
  GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base
  GeneralDictionarySlotPreparationTransportExamples.frames
  GeneralDictionarySlotPreparationTransportExamples.payload
  GeneralDictionarySlotPreparationTransportExamples.root).map fun tree =>
    (tree.root.identity, tree.items.length, tree.root.demand.outputs.length)
#eval (GeneralDictionaryPayloadPreparation.prepare
  GeneralDictionaryHeadlessFixture.registry GeneralDictionaryHeadlessFixture.registry_checked
  GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base
  GeneralDictionarySlotPreparationTransportExamples.frames
  GeneralDictionarySlotPreparationTransportExamples.payload
  GeneralDictionarySlotPreparationTransportExamples.root).map fun tree =>
    (tree.root.identity, tree.items.length, tree.root.demand.outputs.length)
#eval (GeneralDictionaryHeadlessLocations.locate GeneralDictionaryTypeCoverageExamples.before.base
  GeneralDictionaryTypeCoverageExamples.demand).isSome
#eval (GeneralDictionaryHeadlessLocations.locate GeneralDictionaryTypeCoverageExamples.afterBase
  GeneralDictionaryTypeCoverageExamples.demand).isSome
```

`RuntimeFresh.lean`

```lean
import Yulang.GeneralDictionaryFreshSlotPreparationExamples
open Yulang
#eval (GeneralDictionaryPayloadPreparation.prepare
  GeneralDictionaryHeadlessFixture.registry GeneralDictionaryHeadlessFixture.registry_checked
  GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base
  GeneralDictionaryFreshSlotPreparationExamples.frames
  GeneralDictionaryFreshSlotPreparationExamples.payload
  GeneralDictionaryFreshSlotPreparationExamples.root).isSome
#eval (GeneralDictionaryPayloadPreparation.prepare
  GeneralDictionaryHeadlessFixture.registry GeneralDictionaryHeadlessFixture.registry_checked
  GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base
  GeneralDictionaryFreshSlotPreparationExamples.frames
  GeneralDictionaryFreshSlotPreparationExamples.payload
  GeneralDictionaryFreshSlotPreparationExamples.root).map fun tree =>
    (tree.root.identity, tree.items.length, tree.root.demand.outputs.length)
```

## Public checkpoints and full-tree verification

GitHub APIによる非force・expected-head付き更新のみ。対象枝は全て`work/dots-main`。blob SHAとlocal git blobを比較し、作成tree SHAがlocal treeと一致してからrefを進めた。公開後はrecursive treeの全blobをlocal `git ls-tree -r`と比較し、path/mode/type/SHAの一致を確認。いずれもtruncated=false、差分0。

### checkpoint-evidence

source: `3422acd820109ff6f676e72d611d197581ace327`
tree: `477e57d4f62cfe539355cd614efa564f0601fdea`
local: `e5e22c92b904d83b00f1497881301db004ced5f1`
全tracked files: 2503; verified=True。

Hosted結果:
- Core CI: success https://github.com/momota1029/yulang/actions/runs/43128441737
- Lean inference kernel: success https://github.com/momota1029/yulang/actions/runs/43128441740
full build: Build completed successfully (1453 jobs).
audit entries: 9244; 新定理名: 51; 許可外公理: 0。

### second-evidence

source: `0031756d286a732970df0ba0cca8f4002f490c09`
tree: `dfd0559d17f2f00c3c2b17da0b5df01516dd8d72`
local: `ebea643d6e304e6666b71af21881955b1bf30c4d`
全tracked files: 2510; verified=True。

Hosted結果:
- Core CI: success https://github.com/momota1029/yulang/actions/runs/43130189110
- Lean inference kernel: success https://github.com/momota1029/yulang/actions/runs/43130189099
full build: Build completed successfully (1460 jobs).
audit entries: 9287; 新定理名: 94; 許可外公理: 0。

### final-publication

source: `3bba9c845697a0a8a41d03ff62f880a8b8a7aef3`
tree: `c427f61635232a73b8ad83524294f377600722ea`
local: `6be6722f5d467d3fc84f1e03cce7f20408c6d2f6`
全tracked files: 2515; verified=True。

### Final source hosted CI

- Lean inference kernel: success https://github.com/momota1029/yulang/actions/runs/43132021275
- Core CI: success https://github.com/momota1029/yulang/actions/runs/43132021470
ログ内checkout SHA一致: True
Build completed successfully (1465 jobs).
全audit entries: 9318。新規125/125名を確認、missing=[]、許可外公理=[]。

## Intermediate checks and corrected failures

以下は途中のstdout/stderr全文と記録済みexit。開発途中の失敗を隠さず残す。旧logが単一commandの終了値でない場合、最終の独立exit付き実行を判定に用いる。
初期transport・batch fixtureのelaboration失敗は修正済み。中間型helperの`pp.width`は未対応optionでexit1となったため除去し、最終全125型をexit0で取得。fresh-slotのnone証明はrflから実source不在の証明へ修正し、不要simp引数と不要simpaも修正した。final-gate初回はrepo/base引数不足によるusage exit1で、正しい全引数による再実行はPASS。これら失敗は成功件数に含めない。

### batch-examples

exit code: 1

```text
✔ [562/563] Built Yulang.GeneralDictionaryNominalSlotTransportExamples (19s)
✖ [563/563] Building Yulang.GeneralDictionaryNominalBatchTransportExamples (1.7s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryNominalBatchTransportExamples.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryNominalBatchTransportExamples.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryNominalBatchTransportExamples.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryNominalBatchTransportExamples.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryNominalBatchTransportExamples.setup.json --json
error: Yulang/GeneralDictionaryNominalBatchTransportExamples.lean:69:0: Not a definitional equality: the conclusion should be an equality, but is
  (items mixedTransport batch).length = 2 ∧
    List.map (fun item => item.demand.outputs.length) (items mixedTransport batch) = [2, 2]
error: Yulang/GeneralDictionaryNominalBatchTransportExamples.lean:71:92: Type mismatch
  rfl
has type
  ?m.29 = ?m.29
but is expected to have type
  (items mixedTransport batch).length = 2 ∧
    List.map (fun item => item.demand.outputs.length) (items mixedTransport batch) = [2, 2]
Some required targets logged failures:
- Yulang.GeneralDictionaryNominalBatchTransportExamples
error: build failed
```

### batch-transport

exit code: 0

```text
✔ [548/548] Built Yulang.GeneralDictionaryNominalBatchTransport (1.8s)
Build completed successfully (548 jobs).
```

### checkpoint-audit

exit code: 0

```text
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
```

### checkpoint-audit2

exit code: 0

```text
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved' depends on axioms: [propext, Quot.sound]
```

### checkpoint-build-audit

exit code: 0

```text
✔ [585/586] Built Yulang.GeneralDictionaryTypeCoverage (1.5s)
✔ [586/586] Built Yulang.GeneralDictionaryTypeCoverageExamples (1.3s)
Build completed successfully (586 jobs).
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
```

### checkpoint-final

exit code: 0

```text
✔ [594/594] Built Yulang.GeneralDictionaryNominalCandidateOrderExamples (1.3s)
Build completed successfully (594 jobs).
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### checkpoint-gate

exit code: 0

```text
verify-lean: . @ e5e22c92b (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

### evidence-transport

exit code: 0

```text
✔ [575/576] Built Yulang.GeneralDictionarySlotPreparationTransport (104s)
✔ [576/576] Built Yulang.GeneralDictionarySlotEvidenceTransport (71s)
Build completed successfully (576 jobs).
```

### final-gate

exit code: 1

```text
tools/verify-lean.sh: line 31: 2: usage: verify-lean.sh <repo-dir> <base-rev> [--no-build]
```

### fresh-slot-example-corrected

exit code: 1

```text
✖ [583/583] Building Yulang.GeneralDictionaryFreshSlotPreparationExamples (21s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryFreshSlotPreparationExamples.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryFreshSlotPreparationExamples.setup.json --json
error: Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean:120:121: unsolved goals
absent : GeneralDictionaryHeadlessLocations.locate mixedBefore.base demand = none
reconstructed :
  GeneralDictionaryPayloadReconstruction.reconstruct registry registry_checked frames payload root = some sourceTree
⊢ (do
          let inputs ← none
          let localized ←
            List.mapM (GeneralDictionarySourceRecipe.localize GeneralDictionaryTypeCoverageExamples.afterBase) []
          pure (GeneralDictionaryHeadlessPreparation.Recipe.node root 3 inputs localized)).bind
      (GeneralDictionaryHeadlessPreparation.prepare registry registry_checked frames) =
    none
warning: Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean:136:4: This simp argument is unused:
  Option.bind_none

Hint: Omit it from the simp argument list.
  [apply] simp only [GeneralDictionaryPayloadPreparation.prepare, reconstructed, Option.bind_some, sourceTree,
    GeneralDictionaryRecipeFidelity.recipe, List.map_nil, GeneralDictionarySourceRecipe.prepare,
    GeneralDictionarySourceRecipe.localize, absent]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Some required targets logged failures:
- Yulang.GeneralDictionaryFreshSlotPreparationExamples
error: build failed
```

### fresh-slot-example-final

exit code: 0

```text
✔ [583/583] Built Yulang.GeneralDictionaryFreshSlotPreparationExamples (2.9s)
Build completed successfully (583 jobs).
```

### fresh-slot-example

exit code: 1

```text
✔ [597/598] Built Yulang.GeneralDictionarySlotViewBoundaryExamples (12s)
✖ [598/598] Building Yulang.GeneralDictionaryFreshSlotPreparationExamples (12s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryFreshSlotPreparationExamples.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryFreshSlotPreparationExamples.setup.json --json
error: Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean:121:2: Tactic `rfl` failed: The left-hand side
  GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedBefore.base frames payload root
is not definitionally equal to the right-hand side
  none

⊢ GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedBefore.base frames payload root = none
warning: Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean:127:19: This simp argument is unused:
  mixedBefore

Hint: Omit it from the simp argument list.
  [apply] simp

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean:168:4: `simp` already closes the goal

Hint: Use `simp` instead of `simpa`:
  [apply] simp at known

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Some required targets logged failures:
- Yulang.GeneralDictionaryFreshSlotPreparationExamples
error: build failed
```

### nominal-order

exit code: 0

```text
✔ [584/584] Built Yulang.GeneralDictionaryNominalSemanticOrder (10s)
Build completed successfully (584 jobs).
```

### preparation-example-build

exit code: 0

```text
✔ [581/581] Built Yulang.GeneralDictionarySlotPreparationTransportExamples (20s)
Build completed successfully (581 jobs).
```

### registration-check

exit code: 0

```text
GeneralDictionaryNominalCandidateOrder: 8
GeneralDictionaryNominalSlotTransport: 10
GeneralDictionaryTypeCoverage: 6
GeneralDictionaryTypeCoverageExamples: 7
GeneralDictionaryNominalCandidateOrderExamples: 14
GeneralDictionaryNominalBatchTransport: 6
GeneralDictionaryNominalBatchTransportExamples: 5
GeneralDictionaryNominalSemanticOrder: 6
GeneralDictionaryNominalSlotTransportExamples: 8
GeneralDictionarySlotLocalizationTransport: 8
GeneralDictionarySlotMaterializationTransport: 6
GeneralDictionarySlotPreparationTransport: 6
GeneralDictionarySlotEvidenceTransport: 4
GeneralDictionarySlotPreparationTransportExamples: 8
GeneralDictionarySlotFreshnessTransport: 6
GeneralDictionarySlotFreshnessTransportExamples: 5
GeneralDictionarySlotViewBoundaryExamples: 6
GeneralDictionaryFreshSlotPreparationExamples: 6
All18imports/125audit registrations/125inventory blocks: exact, no duplicates.
```

### second-audit-corrected

exit code: 0

```text
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.lifted_arrow_separate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.old_item_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_not_collapsed' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.all_assignment_recording_exact' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.realizes_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_instance_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_evidence_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.every_assignment_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.old_coordinates_preserved' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.strict_extension_localizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_bounds_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.sourceSlot_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.locateTerm_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.binder_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.variable_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.headless_locate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.available' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_denotesAt' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_denotes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.materializes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.variable_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.plan_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.headless_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_dictionary' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.headless_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_localize_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.payload_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepared_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.recorded_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepare_uniform_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### second-build

exit code: 0

```text
✔ [600/600] Built Yulang.GeneralDictionarySlotMaterializationTransport (4.7s)
Build completed successfully (600 jobs).
```

### second-final

exit code: 1

```text
Build completed successfully (602 jobs).
../cache/yulang129/SecondAudit.lean:14:0: error: Unknown option `pp.width`
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.lifted_arrow_separate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.old_item_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_not_collapsed' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.all_assignment_recording_exact' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.realizes_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_instance_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_evidence_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.every_assignment_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.old_coordinates_preserved' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.strict_extension_localizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_bounds_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.sourceSlot_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.locateTerm_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.binder_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.variable_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.headless_locate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.available' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_denotesAt' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_denotes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.materializes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.variable_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.plan_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.headless_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_dictionary' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.headless_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_localize_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.payload_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepared_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.recorded_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepare_uniform_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### second-gate

exit code: 0

```text
verify-lean: . @ ebea643d6 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

### third-audit

exit code: 0

```text
'Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind' does not depend on any axioms
'Yulang.GeneralDictionaryNominalSlotTransport.embed_injective' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.term_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.base_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransport.source_identity' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.available_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.after_located' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes' depends on axioms: [propext]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes' does not depend on any axioms
'Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.located_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.lifted_arrow_separate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.old_item_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_not_collapsed' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalBatchTransportExamples.all_assignment_recording_exact' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.realizes_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_instance_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSemanticOrder.computed_evidence_reorders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.every_assignment_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.old_coordinates_preserved' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.strict_extension_localizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_bounds_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.sourceSlot_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.locateTerm_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.binder_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.variable_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.headless_locate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.available' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_denotesAt' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotLocalizationTransport.head_compile_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_denotes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.head_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.materializes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.variable_build_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.plan_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotMaterializationTransport.headless_lookup_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.prepared_dictionary' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.headless_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_localize_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.source_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransport.payload_prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepared_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.recorded_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotEvidenceTransport.prepare_uniform_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.preparation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_preparation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.exact_shared_dictionary' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.nonempty_obligations' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.recorded_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_recorded_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.shared_source_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotPreparationTransportExamples.strict_preparation_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.sources_preserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.sources_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.allocation_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.generated_member_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.fresh_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransport.unowned_generated_absent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_coordinates_bounded' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.new_coordinates_justified' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_sources_preserved' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_fresh_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_unowned_absent' depends on axioms: [propext, Quot.sound]
```

### third-build

exit code: 0

```text
✔ [585/586] Built Yulang.GeneralDictionarySlotFreshnessTransport (12s)
✔ [586/586] Built Yulang.GeneralDictionarySlotFreshnessTransportExamples (1.4s)
Build completed successfully (586 jobs).
```

### transport-build

exit code: 1

```text
✖ [442/442] Building Yulang.GeneralDictionaryNominalSlotTransport (1.3s)
trace: .> LEAN_PATH=/workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean /workspace/scratch/1d0b4aaa3394/cache/toolchain116/lean-4.35.0-linux/bin/lean --trust=0 /workspace/scratch/1d0b4aaa3394/yulang/lean/Yulang/GeneralDictionaryNominalSlotTransport.lean -o /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryNominalSlotTransport.olean -i /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/lib/lean/Yulang/GeneralDictionaryNominalSlotTransport.ilean -c /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryNominalSlotTransport.c --setup /workspace/scratch/1d0b4aaa3394/yulang/lean/.lake/build/ir/Yulang/GeneralDictionaryNominalSlotTransport.setup.json --json
error: Yulang/GeneralDictionaryNominalSlotTransport.lean:87:95: Invalid field `mp`: The environment does not contain `Function.mp`, so it is not possible to project the field `mp` from an expression
  ih
of type
  ∀ (values : List CommonNominalFullCarrier.Argument),
    FitsAll after.base model (List.map (parameter transport.embed) rest) values ↔ FitsAll before.base model rest values
error: Yulang/GeneralDictionaryNominalSlotTransport.lean:90:96: Invalid field `mpr`: The environment does not contain `Function.mpr`, so it is not possible to project the field `mpr` from an expression
  ih
of type
  ∀ (values : List CommonNominalFullCarrier.Argument),
    FitsAll after.base model (List.map (parameter transport.embed) rest) values ↔ FitsAll before.base model rest values
error: Yulang/GeneralDictionaryNominalSlotTransport.lean:123:72: Application type mismatch: The argument
  recorded
has type
  (after.base.heads (transport.embed old)).equation = some (TyTerm.rename transport.embed original)
but is expected to have type
  (before.base.heads old).equation = some original
in the application
  heads old original recorded
error: Yulang/GeneralDictionaryNominalSlotTransport.lean:127:56: Application type mismatch: The argument
  member
has type
  (transport.embed old.fst, transport.embed old.snd) ∈
    List.map (fun pair => (transport.embed pair.fst, transport.embed pair.snd)) before.base.intervals
but is expected to have type
  old ∈ before.base.intervals
in the application
  intervals old member
error: Yulang/GeneralDictionaryNominalSlotTransport.lean:143:86: Application type mismatch: The argument
  recorded
has type
  after.nominals (transport.embed old) = some (descriptor transport.embed original)
but is expected to have type
  before.nominals old = some original
in the application
  valid old original recorded
error: Yulang/GeneralDictionaryNominalSlotTransport.lean:150:9: Application type mismatch: The argument
  before.base.source_injective
has type
  Function.Injective before.base.source
but is expected to have type
  before.base.source first = before.base.source last → first = last
in the application
  Iff.intro before.base.source_injective
Some required targets logged failures:
- Yulang.GeneralDictionaryNominalSlotTransport
error: build failed
```

### transport-build2

exit code: 0

```text
✔ [583/584] Built Yulang.GeneralDictionaryNominalCandidateOrder (1.2s)
✔ [584/584] Built Yulang.GeneralDictionaryNominalSlotTransport (1.4s)
Build completed successfully (584 jobs).
```

### transport-second

exit code: 0

```text
✔ [563/564] Built Yulang.GeneralDictionaryNominalBatchTransportExamples (2.3s)
✔ [564/564] Built Yulang.GeneralDictionarySlotLocalizationTransport (2.3s)
Build completed successfully (564 jobs).
```

## Heartbeat and recovery notes

前cycle128はcompleted/releasedで正常終了。公開済み最後の追記を新integrationへの復元時に保持。writerの重複なし。heartbeatは初回・約10/20/30/40分と終了時に公開し、50分到達時にもrunning更新を行う。
初回heartbeatの手入力updated=00:27:30/elapsed=2.1は実時刻の予測値だった。実公開commitの時刻は00:26:05Z（開始42秒後）と読み戻して確認した。以後のheartbeatはdatetimeの実測値を使用。初回メタデータを正確な実測値だとは扱わない。
local integration merge時、一つのtool応答が拒否を示したが作業結果を確認するとmergeは完了していた。状態照合でuncertain outcomeを解消し、同操作を再実行しなかった。公開について未解決の拒否/承認待ちはない。

## Remaining obligations and resources

新target snapshot、typed source IDの正当な起源/権限、normalized view対応、実child Context/capture生成は依然入力/未完成。CoordinatesBoundはFresh保存に必要な追加前提であり勝手なsource追加の許可ではない。新ID88の具体回帰もRootPendingを保ち、candidate completionと区別する。
一般B4は12/12未充填。SourceBoundary全13項目はmain報告に記載。新しい言語意味論の選択なし、質問ノート0件。Yulang2は既存ROLE-MORE-001–008を確認、新しい実機試験なし。
開始・終盤の空きディスクは37GiB。既存cacheのコピー/削除なし。使用量上限は不明。

## Exact new module inventory

- `lean/Yulang/GeneralDictionaryNominalCandidateOrder.lean`
- `lean/Yulang/GeneralDictionaryNominalSlotTransport.lean`
- `lean/Yulang/GeneralDictionaryTypeCoverage.lean`
- `lean/Yulang/GeneralDictionaryTypeCoverageExamples.lean`
- `lean/Yulang/GeneralDictionaryNominalCandidateOrderExamples.lean`
- `lean/Yulang/GeneralDictionaryNominalBatchTransport.lean`
- `lean/Yulang/GeneralDictionaryNominalBatchTransportExamples.lean`
- `lean/Yulang/GeneralDictionaryNominalSemanticOrder.lean`
- `lean/Yulang/GeneralDictionaryNominalSlotTransportExamples.lean`
- `lean/Yulang/GeneralDictionarySlotLocalizationTransport.lean`
- `lean/Yulang/GeneralDictionarySlotMaterializationTransport.lean`
- `lean/Yulang/GeneralDictionarySlotPreparationTransport.lean`
- `lean/Yulang/GeneralDictionarySlotEvidenceTransport.lean`
- `lean/Yulang/GeneralDictionarySlotPreparationTransportExamples.lean`
- `lean/Yulang/GeneralDictionarySlotFreshnessTransport.lean`
- `lean/Yulang/GeneralDictionarySlotFreshnessTransportExamples.lean`
- `lean/Yulang/GeneralDictionarySlotViewBoundaryExamples.lean`
- `lean/Yulang/GeneralDictionaryFreshSlotPreparationExamples.lean`

全定理名/型/範囲は[dots-cycle-129-theorems.md](dots-cycle-129-theorems.md)。最終report公開後にも全tracked tree照合を実施し、completed heartbeatへreport commit/treeとファイル数を記録する。

## Closeout readback and late upstream

Report checkpoint4ec3a668294c7bf1ead4e3b265e82de118f9db5e/tree88ec107cac79d2eaae55ba0064118409000139e2は全2518tracked filesを再照合、差分0/truncated=false。3報告それぞれも公開raw内容をlocal全文と比較し、一致した。明示refspec付きfetch後の公開report treeとのgit diffもexit0。最終sourceからLean subtreeに変更なし（git diff --quiet exit0）。

終盤の再fetchでintegrationがa5e2eecf619b7237fb545faea6fa7e5a52cb0ce9へ進み、inbox I-21の担当更新を確認した。今回のゲート/ビルド/CIは開始時a97bf63の基準に対する記録。新Astra14modulesと117audit追記は今回の検証に含めない。次cycleは新integrationを統合し、recursive Survivorに対するEvidence/evidenceNodeを最優先する。変更は本closeout追記のみ、Leanは凍結のまま。
