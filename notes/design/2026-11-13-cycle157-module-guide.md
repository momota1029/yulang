# cycle157 module guide: Evidence / I-25

この地図の対象は今回の22モジュールだけ。既存モジュール全体の分類ではない。
すべて新規ファイルで、既存の言語規則・分類器・実ステップの定義は変更しない。

## 読む順序と量化範囲

### A. 過去の記録から現在の request を取り出す

- PersistentCatalog: 任意のroles、registry、root、任意の実Value Stepおよび有限Stepsについて、過去の変数なしpacketのrequest catalogが後の状態に包含される。初期に記録されたpacketのrequestを任意の後続状態へ運べる。意味論上の終端性は要らない。
- RequestCatalog: 任意の有限journalについて、packet全体ではなく個々のrequestの生成schemaの変数リストが空であるものを抽出する。catalog所属と既存RecordedBatchModels.Coveredは同値。whole-packet safeCatalogを包含する。実到達状態での意味論への接続には既存の到達履歴を使う。
- RequestCatalogCompute: 同じ有限リストをBoolのisEmptyで抽出し、上のcatalogとの等式を示す。計算対象は構文的履歴coverageだけで、Modelsや全Evidenceの判定器ではない。
- RequestCatalogEvidence: 任意の実到達状態、任意有限個のscalar点head引数、現在のShapeと対象requestのcatalog所属から現在のInstanceを導く。有限再帰辞書の健全性は選択経路ごとのShape/coverageを明示的に要求する。
- VariableClauseCatalog: 任意の記録済みpacketで、whereの入力が変数だけなら、materializationのrequestリストは観測状態・capture bindingの置換で変わらない。記録schemaに変数がない場合、現在のcoverageを導出し、scalar Shapeおよび現在選択に接続する。子の割当てまで不変とは言わない。

具体的回帰:
- MixedCatalogExample: 同じpacket内の閉じたrequestと変数を含むrequestを分離し、旧catalogは空、新catalogは閉じたrequestを保持する。
- MixedCatalogInhabited: このpacketの制約には正のモデルがある。
- MixedCatalogReachable: このpacketを空journalの実InitialSourceから実Value installで記録する。生のjournalを仮定しただけの例ではない。
- ComputedCatalogExample: 実fixtureの計算catalogが閉じたrequest一個と等しい。
- VariableClauseCatalogExample: 既存の予約出力fixtureを用い、carrierが2から3になった後でも記録requestのcoverageと現在Evidenceを得る。

### B. 生成された子の区間を形成する

- GeneratedOrigins: 任意の実到達状態とGenerated occurrenceについて、元rootか、実journal内のpacketが発行した子であることを得る。
- CapturedChildIntervals: 任意のchecked packet、各where入力が正規化後に変数である構文条件、任意のpacketモデルについて、任意の発行子・任意の引数のlowerはupper以下。捕捉が空ならbottom/topを用いる。繰返し捕捉は実際のcross制約とmerge等式を使い、独立のframeや端点順序を仮定しない。
- GeneratedIntervals: 任意の実到達状態、journal全体の上記構文条件、任意のGenerated occurrence、任意の現在モデルから、全引数の端点順序を導く。rootの場合と記録子の場合を区別する。
- ProvenanceGeneratedIntervals: 現在scalar interval Shape、実request provenance、現在selectionと上の生成区間条件をInstanceへ接続する。
- VariableRegistryIntervals: registryの全宣言のwhere入力が変数へ正規化されるなら、実履歴からjournal条件が従う。headと名前付き出力はこの述語では制限しない。
- GeneratedIntervalCoverage: 任意の実到達状態とその有限selected辞書について、上のregistry条件と選択経路の各節点のGenerated/現在scalar interval Shape/catalog所属からEvidenceを得る。端点順序やInstanceを前提にしない。ただし選択経路が自動的にGeneratedであることや、そのcoverage自体は未証明。
- GeneratedIntervalExample: 実installで生じる非rootの子について、その生成・現在の区間・正のモデルを検証する。

このVariableRegistryは証明した断片の条件であり、compound where入力を言語から拒否する規則ではない。

### C. 変数を含む名前付きschemaを現在へ移す

- CapturedSchemaTransport: 任意の古い/新しいcarrier・capture/reportについて、schemaが実際に読むsource identityの一致と、現在の関連するorigin/name読みが過去にもあることを有限Footprintとして要求し、名前付きschemaのModelsを移す。有限変数リストだけを調べ、全解釈の同一性は要らない。
- BindingSchemaReplay: 任意の実到達状態とその記録packetについて、現在computed source-ID bindingsがpacket.bindingsと等しく、関連Originsが保持されれば、現在のgenerated named schema全体のModelsが従う。実履歴からseed保存を得て、現在requestとcapture allocationを再構成する。
- RecordedScalarIntervalEvidence: 任意の実到達状態に記録されたpacket、VariableRegistry、現在scalar interval Shape、computed bindings一致から現在BranchModelsを示し、選択されたInstanceへ接続する。schema全体の変数なし条件と手動Supportedは要らない。ただしscalar Shapeは捕捉なしなので、一致条件はpacket.bindingsが空である場合に限る。下記nominal捕捉例をそのままこの完全Instanceの定理へ入れることはできない。
- MixedCapturedReplay: 実install後の変更されたcontextで、現在の捕捉とrequestを具体的に再計算し、変数付きschemaのreplayを正のモデル付きで確認する。
- MixedCarrierRefresh: 同じmixed fixtureで、未知の出力sourceをintとして公開する実Value refreshを構成する。carrier2→3、実到達性、正のモデル、capture binding/source origin保持、現在の変数付きschema全体のreplayを示す。Stableや全BranchModelsを示したものではない。

## 今回で閉じないもの

V5の未証明フィールドは8/14のまま:
progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder,
evidenceNode, generatedChildren。

特定の実fixtureが存在すること、任意の有限証明対象に対する条件付き健全性、
および任意の実履歴に対する構文的保存補題を区別する。
一般のStableから現在capture一致や全選択節点のcoverageを導く橋は残る。
新しい意味論上の決定を採用していない。

## 公開定理名の索引

22モジュール、140公開定理。上記の各群の量化範囲・前提と合わせて読む。
正確な型と各補助補題の前提は同名Leanファイルを参照。

### GeneralDictionaryBindingSchemaReplay
`packet_seed`, `capture_seed`, `requests_seed`, `replay`

### GeneralDictionaryCapturedChildIntervals
`occurrences_member`, `capture_order`, `packet_capture_order`, `clause_input_order`, `variable_name`, `clause_input_declared`, `child_origin`, `child_intervals`

### GeneralDictionaryCapturedSchemaTransport
`variable_meaning`, `replay`, `footprint_refl`, `recorded_replay`

### GeneralDictionaryComputedCatalogExample
`packet_computed`, `installed_computed`

### GeneralDictionaryGeneratedIntervalCoverage
`selected_instance`, `dictionary_evidence`, `dictionaries_evidence`, `root_dictionary_evidence`, `completed_tree_evidence`

### GeneralDictionaryGeneratedIntervalExample
`capture_bindings`, `variable_inputs`, `registry_fragment`, `journal`, `reachable`, `nonroot`, `every_generated_interval`, `positive_model`, `actual_nonroot_intervals`

### GeneralDictionaryGeneratedIntervals
`recorded_child`, `generated_intervals`, `located_intervals`

### GeneralDictionaryGeneratedOrigins
`generated`, `monotone`, `administrative`, `installed`, `step`, `reachable`, `reachable_generated`

### GeneralDictionaryMixedCapturedReplay
`report_current`, `report_old`, `footprint`, `replay_current`, `requests_exact`, `current_schema`, `bindings_exact`, `computed_reinspection`, `context_changed`, `nonvacuous`

### GeneralDictionaryMixedCarrierRefresh
`target_fresh`, `output_int`, `snapshot_models`, `target_reserved`, `output_member`, `output_not_known`, `output_known`, `refresh_step`, `refreshed_models`, `refreshed_reachable`, `refreshed_inhabited`, `report_current`, `bindings_exact`, `origins`, `packet_recorded`, `replay`, `carrier_changed`, `nonvacuous_replay`

### GeneralDictionaryMixedCatalogExample
`checked`, `emissions`, `closed`, `mixed`, `old_catalog_empty`, `new_catalog_contains`, `generated_exact`, `strict_coverage`

### GeneralDictionaryMixedCatalogInhabited
`target_nonzero`, `query`, `branch`, `journal_models`, `nonvacuous_strict_coverage`

### GeneralDictionaryMixedCatalogReachable
`registry_checked`, `all_source_decisions`, `prepared`, `survivor`, `selected`, `enabled`, `packet_guard`, `novel`, `source`, `value_step`, `reachable`, `installed_model`, `recorded`, `old_catalog_empty`, `new_catalog_contains`, `reachable_strict_coverage`

### GeneralDictionaryPersistentCatalog
`safeCatalog_step`, `safeCatalog_trace`, `recorded_trace`

### GeneralDictionaryProvenanceGeneratedIntervals
`branch_models`, `instance_of_shape`, `selected_instance`

### GeneralDictionaryRecordedScalarIntervalEvidence
`recorded_generated`, `origins`, `generated_known`, `branch_models`, `instance_of_recorded`, `selected_instance`

### GeneralDictionaryRequestCatalog
`eligible_iff`, `member_iff`, `covered_iff`, `safe_included`, `supported`, `catalog_step`, `catalog_trace`, `shape`

### GeneralDictionaryRequestCatalogCompute
`packet_exact`, `catalog_exact`, `coverage_exact`

### GeneralDictionaryRequestCatalogEvidence
`instance_of_catalog`, `structural`, `covered`, `dictionary_evidence`

### GeneralDictionaryVariableClauseCatalog
`requests_independent`, `current_covered`, `scalar_instance`, `recorded_visible`, `selected_scalar_instance`, `selected_root_interval_instance`

### GeneralDictionaryVariableClauseCatalogExample
`changed_context`, `coverage`, `instance_after_refresh`, `evidence_after_refresh`, `inhabited_changed_context`

### GeneralDictionaryVariableRegistryIntervals
`journal`, `generated_intervals`, `selected_instance`
