# dots cycle171 — recursive named-spine certificate and conservative discovery

開始2026-11-13 18:24:41 UTC。55分の保守的期限19:19:41 UTCを優先した。
初回integration afbd591366、前回公開f96fb52505から開始。初回心拍5ebcb1df83、最初のsource checkpoint babc030cd54e4e705a7fa9ddc1168f549c349f46をwork/dots-mainに公開した。

## 成果と範囲

19新規モジュール。すべて補助／健全性補助で、一般の完全性・主型性の完成ではない。
- NamedSpine.Shapeを局所Nodeと再帰Treeの追加constructorに接続。前回のnominal-input/named-output実例の局所証明書の穴を埋めた。任意Reachable/StableからCoverageを発見する一般定理ではない。
- 固定journalのrankからchosen-child accessibilityを導き、fuel付きassemblerの成功、全現在モデルで同じ辞書、node数上界を証明。Coverageは外部義務のまま。言語実行の一般停止性や実行時間上界ではない。
- ordinary traceでTree、Coverage、buildの結果を保存。実selectednessと現在モデル一つがある場合、異なる局所証明書の選択でも結果は一致する。任意descriptor refreshへは拡張していない。
- actual Finished inspectionから閉じたscalar/nominal queryの有限観察を回収。point条件を実際に観察したslotへ局所化。nominal入力のdescriptor・引数boundsを実inspectionから回収する橋も追加。
- 保守的な実行可能checkerは有限carrierから正確なoutput identityを検索し、閉じたquery/point条件を検査する。成功ならNodeと同一terminal Evidenceを構成。falseは未証明であり、言語上のrejectではない。aliases、nonpoint、reserved-only identityの一般完全性は未証明。
- 前回の実named-spine fixtureはchecker true、reserved-output fixtureはfalse。source集合への所属から物理slotの存在を仮定していない。再帰strictnessのgraftは構造的条件付き結果で、新しいReachable非terminal実行例とは呼ばない。

## 復旧と検証

18:57 UTCに実行担当の消失から復旧。retained source・ログ・公開branchを読み、active Lean/lake writerがないことを確認してから続行した。初回12 modules/8 auditsのimmutable source replayはPASS、旧gate215宣言。初回focused lake build799jobs PASSのログを保持。
後半19 modulesを新しいlibraryで依存順にlean --trust=0再構築し、14監査を実行。19 modules・14 auditsすべてPASS、最終gate415宣言PASS。検証ログをnotes/verification/cycle171へ保存した。全体lake buildとverify-lean.shは常設指示の環境制限により実行していない。
既公開gateのwantedを書き換えかけたが、公開前に元版へ戻し、新規Cycle171FinalGateへ分離。既公開Leanは追記のみ。Yulang.leanへの全新規module importを確認する。
18:58の再取得でintegration e83e521dd9e629c91d00d3529032576d5b43fe59を確認、inbox ACTIVE/I27まで。初回afbd591の統合は維持し、遅れて到着したupstream sourceは今回の検証範囲へ混ぜていない。次回に統合する。心拍は18:33以後復旧まで途絶えた。予定どおり連続更新したとは報告しない。

## 13境界とV5

| 境界 | 状態 |
|---|---|
| Checked | 一般nominal定義を維持、新nominal実例で成立 |
| Models | 一般定義を維持、全現在モデルと実例の明示モデルを区別 |
| Step | Shared/ActualInspection定義を変更せず。ordinaryは実関係の制限 |
| Stable | 一般定義を維持。新spine初期実例の実Shared Stableを追加検証 |
| Generated | 一般定義を維持。生成から局所coverageの一般導出は未完 |
| RootPending | 一般定義あり、変更なし |
| RootK2 | 一般定義あり、変更なし |
| CandidateK2 | 一般定義あり、変更なし |
| InspectionPending | 一般nominal定義あり、全Shared境界の統合は未完 |
| Survivor | 一般定義あり、変更なし |
| Evidence | 構造的局所構築、計算assembler、named spine解釈を追加 |
| Reorders | 一般定義あり、変更なし |
| DictionaryEquivalent | 一般定義あり、変更なし |


V5未証明8/14のまま。一般evidenceNode、生成/到達からのCoverage、任意refresh保存は閉じていない。CoverageをV5の追加仮定にして達成扱いにしない。

## Yulang2との照合

この復旧区間では新しいYulang2実機実行なし。前回のx-oracleのX1/X2比較を素材として扱うが、今回のchecker・辞書との一般同値は未証明。言語仕様やAstraの既存定義を変更しない。

## 次の義務

1. Reachable/Stableから今回の局所Coverageを一般に導出する。
2. 実snapshotの観察とrelocationを任意descriptor refreshで保存する。
3. conservative checkerの成功範囲を正確に切り分け、aliases/nonpoint/reserved outputをfalseからrejectへ読み替えない。

## 公開定理台帳

各定理の完全な型は対応Auditの#checkにある。名前にactual/exampleがあるものは固定実例。その他もsource docstringの前提を維持する。
- `GeneralDictionary171AssemblyPersistence`（補助／健全性補助）: `collect_congr`, `assemble_congr`, `extension_assemble`, `ordinary_assemble`, `collect_unique`, `successful_fuel_unique`, `extension_build`, `ordinary_build`
- `GeneralDictionary171AssemblySize`（補助／健全性補助）: `node_degree`, `collect_bound`, `successful_bound`, `build_bound`
- `GeneralDictionary171BoundedAssembly`（補助／健全性補助）: `enough_fuel`, `successful_tree`, `build_succeeds`, `build_dictionary`, `zero_fuel`
- `GeneralDictionary171CheckedSpine`（補助／健全性補助）: `discover_success_iff`, `uniform_evidence`
- `GeneralDictionary171CheckedSpineExample`（補助／健全性補助）: `checked_true`, `discovered`, `checked_uniform_dictionary`, `reserved_check_false`, `linked_without_physical_target`
- `GeneralDictionary171InputDiscovery`（補助／健全性補助）: `type_arguments_exact`, `inspected_leaf`, `input_exists`
- `GeneralDictionary171InspectionObservation`（補助／健全性補助）: `inspected_tree`, `observed_requests`, `variables_finished`, `no_variables_tree`
- `GeneralDictionary171LocalInspectionObservation`（補助／健全性補助）: `inspected_tree`, `observed_requests`, `of_global`
- `GeneralDictionary171NamedSpinePersistence`（補助／健全性補助）: `requests_eq`, `shape_slot`, `shape_query`, `extension`, `ordinary_steps`, `current_evidence`
- `GeneralDictionary171RecursiveStrictness`（補助／健全性補助）: `old_tree_node`, `old_tree_decompose`, `old_tree_selected_children`, `child_gap_propagates`, `recorded_parent_strict`, `actual_no_old_tree`
- `GeneralDictionary171RequestChecker`（補助／健全性補助）: `closedQuery_sound`, `closedQueries_sound`, `pointArguments_sound`, `pointReport_sound`, `finishedReport_sound`, `checkAt_sound`, `checkRequest_sound`, `checkRequests_sound`
- `GeneralDictionary171SelectedAssembly`（補助／健全性補助）: `node_instance`, `node_selected`, `assemble_independent`, `build_independent`
- `GeneralDictionary171SpineAccessible`（補助／健全性補助）: `child_rank`, `coverage_accessible`, `covered_tree`, `covered_dictionary`
- `GeneralDictionary171SpineCoverage`（補助／健全性補助）: `node_tree`, `accessible_tree`, `wellFounded_tree`, `uniform_dictionary`
- `GeneralDictionary171SpineDiscovery`（補助／健全性補助）: `branch_models`, `uniform_evidence`
- `GeneralDictionary171SpineDiscoveryExample`（補助／健全性補助）: `point_descriptors`, `closed_request`, `finished_request`, `tested_requests`, `discovered_evidence`, `inspected_strict_node`
- `GeneralDictionary171SpineExample`（補助／健全性補助）: `actual_tree`, `actual_accessible`, `actual_uniform_dictionary`, `actual_no_old_coverage`, `stable_strict_coverage`
- `GeneralDictionary171SpinePersistence`（補助／健全性補助）: `tree_extension`, `tree_ordinary_steps`, `node_transport`, `node_children`, `node_key`, `child_iff`, `ordinary_children`, `ordinary_dictionary`, `ordinary_uniform_payload`
- `GeneralDictionary171SpineTree`（補助／健全性補助）: `current_evidence`
