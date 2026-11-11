# Cycle127 verification and publication record

**一般B4 V3は12/12未充填。local全体build/Audit/AxiomGateは実行していない。**

## 最終sourceと件数

- source: [ebea49a586d96b795f8194cb9f3c5811bc0c616c](https://github.com/momota1029/yulang/commit/ebea49a586d96b795f8194cb9f3c5811bc0c616c)。
- tree: `70d662d46f87ccbac11c7f5381518f0ccdc63c35`。integration baseは`ac106dc2d40da22a38d9908b5d1940d21cd2d7e0`。
- source公開後2456 tracked filesをrecursive API treeとlocal `git ls-tree -r HEAD`で全件比較。path/mode/type/blob SHA一致、truncated=false。
- 15新Lean module、100公開定理。全100件の`#check @`を取得し、日本語主張・効く側とともに[定理別報告](dots-cycle-127-theorems.md)へ収録。
- 既存source変更はAudit/Yulang/README追記のみ。spec/plan/lakeは未変更。以前のcycle126報告追記も消さずに保持。

## 実行コマンドと結果

作業directoryはyulang、Lean用PATHはcache/toolchain116/lean-4.35.0-linux/bin。Lean 4.35.0。
既存lakefileのmoreLeanArgs=["--trust=0"]を変更していない。

1. `git fetch origin integration/m1-final`を開始時と22:45に実施、standing orders/inbox、前回公開報告、APIの前heartbeat completedを読取。23:06にもinbox同hash/ACTIVEを確認。
2. 途中checkpoint: 対象9moduleの`lake build --wfail`、`lake env lean --trust=0 ../cache/yulang127/CheckpointAudit.lean`、diff-only gate。553jobs・67定理audit、exit0。
3. 最終対象: `cd lean && timeout 240s lake build --wfail $(cat ../cache/yulang127/checkpoint-modules.txt)`。15moduleの依存を含む566jobs、exit0。
4. scoped audit: `cd lean && timeout 90s lake env lean --trust=0 ../cache/yulang127/CheckpointAudit.lean`は無出力timeout124。`timeout 180s`で一度再試行しexit0。全100件の出力、欠落0、許可外公理0。
5. `cd lean && timeout 90s lake env lean --trust=0 ../cache/yulang127/FinalSignatures.lean`はexit0、`set_option pp.universes true`と`#check @`で100/100件取得。全文は定理別報告に収録。
6. runtime evalと6実行定義のruntime axiom printは各`timeout 90s lake env lean --trust=0`で無出力timeout124。未検証として記録し、成功を主張しない。各対応回帰定理のbuild/audit成功とは区別する。任意evalの追加再試行はしなかった。
7. 最終読取レビューでsource-only2moduleの冒頭コメントだけを明確化。binderValuesはprepare runtimeでなくassignmentごとのsoundness証明で構成する。変更後`timeout 150s lake build Yulang.GeneralDictionarySourceRecipe Yulang.GeneralDictionarySourceRecipeExamples`は555jobs exit0。定義・定理文・証明は前述100auditから不変。
8. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`と`git diff --check origin/integration/m1-final`はexit0。全出力を下へ添付。

対象modules:

```text
Yulang.GeneralDictionaryHeadlessCandidateBoundary Yulang.GeneralDictionaryHeadlessExactness Yulang.GeneralDictionaryHeadlessExamples Yulang.GeneralDictionaryHeadlessFixture Yulang.GeneralDictionaryHeadlessLocations Yulang.GeneralDictionaryHeadlessOrder Yulang.GeneralDictionaryHeadlessPendingBoundary Yulang.GeneralDictionaryHeadlessPlans Yulang.GeneralDictionaryHeadlessPreparation Yulang.GeneralDictionaryHeadlessRealization Yulang.GeneralDictionaryHeadlessSemanticOrder Yulang.GeneralDictionaryHeadlessSourceEvidence Yulang.GeneralDictionaryHeadlessSourceExamples Yulang.GeneralDictionarySourceRecipe Yulang.GeneralDictionarySourceRecipeExamples
```

## 最終focused build出力全文

```text
✔ [566/566] Built Yulang.GeneralDictionaryHeadlessCandidateBoundary (67s)
Build completed successfully (566 jobs).
exit 0
```

## コメント明確化後の再build出力全文

```text
✔ [554/555] Built Yulang.GeneralDictionarySourceRecipe (11s)
✔ [555/555] Built Yulang.GeneralDictionarySourceRecipeExamples (30s)
Build completed successfully (555 jobs).
exit 0
```

## 全100件のscoped axiom出力全文

許可公理はpropext、Classical.choice、Quot.soundのみ。無公理の項目は無公理。

```text
'Yulang.GeneralDictionaryHeadlessCandidateBoundary.survivor_outputs_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessCandidateBoundary.output_demand_outside_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessCandidateBoundary.prepared_output_tree_outside_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExactness.prepare_materializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExactness.materializes_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExactness.prepare_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExactness.materializes_functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExactness.prepare_none_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.root_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.child_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.leaf_prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.tree_prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.prepared_uniform_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.prepared_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.wrong_role_key_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.absent_key_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.nominal_root_still_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.unequal_capture_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.absent_second_source_defers' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.changed_child_identity_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessExamples.source_localization' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.binderWrap_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.leaf_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.root_actual_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.child_actual_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.root_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.child_holds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.tree_items' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.tree_joint_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.retained_outputs' depends on axioms: [propext]
'Yulang.GeneralDictionaryHeadlessFixture.root_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.child_build' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.root_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.child_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.root_head_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.child_head_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.root_head_builds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.child_head_builds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.tree_built' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.uniform_completion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessFixture.all_model_root_child_input' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.inputs_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.inputs_available' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.locate_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.locate_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.locate_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.linked_available' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessLocations.locate_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessOrder.prepare_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessOrder.dictionary_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessOrder.record_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessOrder.prepared_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessOrder.dictionary_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPendingBoundary.root_still_pending' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPendingBoundary.preparation_with_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_build_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.head_compile_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.head_build_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_reorders_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPlans.lookup_none_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPreparation.prepare_node_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPreparation.prepare_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPreparation.prepare_built' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessPreparation.prepare_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHeadlessRealization.normalized_var_occurs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessRealization.supported_input' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessRealization.realizes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessRealization.lookup_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessSemanticOrder.realizes_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessSemanticOrder.instance_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessSemanticOrder.instance_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessSemanticOrder.evidence_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceEvidence.source_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceEvidence.prepare_uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceExamples.tree_uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceExamples.tree_source_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_capture_realizes' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_source_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceExamples.source_instance_while_lookup_defers' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryHeadlessSourceExamples.unequal_leaf_preparation_defers' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySourceRecipe.localize_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipe.prepare_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipe.prepare_uniform_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipe.prepare_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.leaf_localizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.tree_localizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.tree_prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.tree_uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.tree_source_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.absent_output_location_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.absent_output_localization_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.absent_output_preparation_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceRecipeExamples.omitted_child_defers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```

## Diff-only gateの出力全文

```text
verify-lean: . @ e618d78a5 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

`git diff --check origin/integration/m1-final`: 出力なし、exit0。

## 第一checkpointの公開とhosted検証

- source `883de7b1673172a7d1a0c413572e1b957bec14a6`、tree `6c18e8ecef1b3e4e84df099c5b9447e48e3bd6ec`、全2445ファイル一致。
- [core success](https://github.com/momota1029/yulang/actions/runs/43114337401/job/130838287899)、[proof success](https://github.com/momota1029/yulang/actions/runs/43114337062/job/130838285886)。
- exact checkout SHA一致、full1404jobs、full Audit8617出力、追加67/67名前一致、許可外公理0。
- これはhosted CIの確認であり、local全体検証の実行や監督役の独立AxiomGate確認とは別。

## 修正前エラー・制限

証明の未解決goal・不要simp引数のlinter warningを修正してから上記成功を得た。
初回lake PATH不足は正しいPATHを設定して復旧。GitHub CLIは未認証のため接続済みアプリを使った。
一部focused処理が無出力timeout124。原因は未確定で、成功と数えない。
開始時空き38GiB、23:06時点37GiB。cache複製・削除なし、使用量上限は不明。

各bounded checkの記録（中間失敗を含む）:

| log | exit |
| --- | --- |
| all-build | 124 |
| all-build2 | 1 |
| candidate-boundary-build | 124 |
| checkpoint-checks | 1 |
| checkpoint-gate | 0 |
| comment-build | 0 |
| exactness-build | 1 |
| exactness-build2 | 1 |
| exactness-build3 | 1 |
| exactness-build4 | 0 |
| exactness-build5 | 124 |
| final-audit | 124 |
| final-build | 0 |
| final-diff | 0 |
| final-gate | 0 |
| final-signatures | 0 |
| pending-build | 124 |
| preparation-build | 1 |
| probe | 124 |
| retry-audit | 0 |
| runtime-audit | 124 |
| runtime | 124 |
| second-build | 0 |
| second-gate | 0 |
| serial-build | 1 |
| serial-checks2 | 0 |

## 新規定理とaudit登録の整合

100件のpublic theorem名を新15moduleから抽出。Audit登録不足0、aggregate import不足0、
定理報告100項目、signature placeholder0を照合した。
完全な名前と型は定理別報告、実際のaxiom出力は上記にある。

## 最終hosted CIとreport readback

最終sourceのhosted結果は下記追記に確定。report readbackはcompleted heartbeatへ記録する。

## 定理型の分割検査

最終読取レビューで型分割器が型中の別定理参照を誤って境界にしていたことを発見。
公開前に修正し、行頭の完全な宣言headerだけで100件に分割した。
100 codeblockを再連結するとraw #checkログ全文66661 bytesとbyte-for-byte一致する。
source/proofを変更せず、切断された型や孤立した@を残していない。

## 最終sourceのhosted結果（23:11UTC確認）

- [core success](https://github.com/momota1029/yulang/actions/runs/43117436529/job/130848934786)
- [proof success](https://github.com/momota1029/yulang/actions/runs/43117436547/job/130848934857)

両jobのcheckout logにexact source SHA ebea49a586d96b795f8194cb9f3c5811bc0c616cを確認。
full buildは1415jobs成功、full Auditの8935項目を抽出し、今回100/100定理が存在、
許可外公理0を確認した。source treeは2456 tracked files全件一致。
これはhostedでの検証結果であり、dotがlocal full build/Audit/AxiomGateを実行した意味ではない。

最終3報告のtree readbackとwriter解放時刻は、公開後のcompleted heartbeatに記録する。
source以後の差分はこの3報告とheartbeatのみとし、Lean sourceの追加変更はしない。

## 報告整合の再確認

公開前に100型ブロックの完全性を独立読取で再確認した。以前切れていた3例も完全で、
全100ブロックを連結するとraw #checkログとbyte-for-byte一致する。残る具体的な報告誤りなし。
report編集後のdiff-only gateとgit diff --checkもexit0、sourceからの変更は3報告とheartbeatのみ。

```text
verify-lean: . @ a6f70a4e4 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

## 公開後の完全readback（23:16UTC）

report commit ca1013ded899e622bf84e19a49f028a85f15dc5a、tree
ce51b8219ca041c336108c818a3afc91f06732f4の2459 tracked filesを全件照合。
path/mode/type/blob SHAが完全一致、truncated=false。再取得した定理報告のblobは
e0da442dc7a9b0ff331b5a11eff1ded9ec0c7e37で本文も完全一致、100個の完全type blockあり。
公開後の最終diff-only gate（local ac676c90d）とgit diff --checkはともにexit0。
この追記後の最終treeとcompleted heartbeatも、解放前に確認する。
