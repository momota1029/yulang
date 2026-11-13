# Cycle155 定理の日本語索引

各節の量化・前提はその節の定理群に共通する枠組みです。現在headのShapeは単一の点引数(slot,slot)を要求し、nominalではnamesの単射性とinputNamesの一致、scalarではinputNames=[]を保持します。一般の繰返しcaptureや多引数headを網羅したものではありません。定理ごとの正確な引数・依存するchecked証明・暗黙型は `dots-cycle-155-types.md` の全110件の型を参照してください。

## GeneralDictionaryInstalledRequestProvenance

`singleton_variables`, `packet_covered`, `installed_supported`, `supported_install_append`

任意の状態・packet・batchについて、generated.variables=[]なら各所属要求のsingletonも変数なし。記録所属・actual requestsへの包含・変数なしからpacket_covered。任意のinstallはそのpacketの変数なしnamedSchemaを仮定して発行要求のSupportedを持つ。最後のappend定理だけは実際のValue Stepと旧batchのSupportedも要求し、旧batchと新発行要求の結合を支える。到達可能性なしにModelsを結論してはいない。

## GeneralDictionaryProvenanceClassification

`dictionary_evidence`, `dictionaries_evidence`

任意のregistry・root・Value到達状態について、全ての選択focusの有限nominal ShapeとSupportedを証するグローバルCoveredを仮定する。任意の現在journal modelと、そのfocusの実際のClassify selected有限payloadからEvidenceを導く。リスト版はAll₂に沿って同時に証明する。

## GeneralDictionaryProvenanceHeadBranch

`selected_instance`, `node_evidence`

任意の到達状態・focus・可視checked宣言について、Structural（有限nominal Shapeまたはscalar Shape、および対応要求のSupported）と実際のLocal selectedを仮定する。任意の現在journal modelで選択key/childrenのInstance。node_evidenceは同じchildrenの辞書EvidenceをAll₂で受け取りnodeのEvidence。

## GeneralDictionaryProvenanceScalarBranch

`report_exact`, `branch_models`, `instance_of_shape`, `selected_instance`

任意のcurrent context/root/宣言について、role一致、非nominal scalar slot、入力名なし、query=[scalar]、同一slotの引数対、RootDefinedからなるShapeを明示する。report_exactはその検査結果。到達可能な状態と対応要求Supportedを加え、任意の現在modelでBranchModels。可視checked宣言・MetadataでInstance、Local selectedを加えると選択key/childrenに一致するInstance。named outputなしや終端宣言は要求しない。

## GeneralDictionaryProvenanceTreeBranch

`branch_models`, `ready`, `instance_of_shape`, `selected_instance`, `selected_branch`, `value_node_evidence`

任意の到達状態・focus・可視checked宣言について、現在有限nominal Shapeと対応要求Supportedを前提にする。任意の現在journal modelでBranchModels、準備性、Metadataを加えたInstance。選択判断との一意整合により選択されたInstance/BranchModelsとなり、子EvidenceのAll₂を加えるとValueのnode Evidence。一般の現在Shape導出は別の未証明課題。

## GeneralDictionaryRecordedBatchModels

`covered_nil`, `covered_append`, `generated_cons`, `reachable_shape`, `reachable_models`

任意batchの各要求に、現在記録済packet、actual request所属、singleton変数なしを持たせたCoveredを使用する。空/append閉包、generated cons分解を証明。到達可能性とCoveredからbatchのcoherent/known shapeを導き、任意の現在journal modelでbatch Models。要求ごとに異なるpacketを使ってよい。

## GeneralDictionaryRecordedTreeBranch

`branch_models`, `ready`, `instance_of_shape`, `selected_instance`, `selected_branch`, `value_node_evidence`

任意の到達状態・focus・可視checked宣言について、現在有限nominal Shapeおよび対応要求のRecorded Coveredを明示する。任意の現在journal modelでBranchModels/準備性、Metadataを加えたInstance。選択と整合するInstance/BranchModels、子Evidenceを受け取るnode Evidenceまで導く。最終結論を前提にした定理ではないが、ShapeとRecorded Coveredの一般導出は主張しない。

## GeneralDictionaryRequestBatchAssembly

`shape_of_singletons`, `variables_of_singletons`, `models_of_singletons`

任意状態・解釈・有限batchについて、各所属singletonのshape/変数なし/Modelsという各定理の前提からbatch全体の対応性質を導く。Models合成ではsingletonの変数なしを必要とし、任意の共有変数に関する整合性を省略していない。

## GeneralDictionaryRequestProvenance

`supported_of_recorded`, `supported_of_observed`, `supported_append`, `shape`, `models`

任意registry/root/current state/batchに対し、各要求のSupportedは到達可能なearlier state・そこからの実際のValue trace・その状態でのObserved、または現在Recorded Covered。各注入とappendの同値を証明する。現在の到達可能性を加えshapeを導き、任意の現在journal modelで対応batch Models。earlier stateの到達可能性は必須のまま保持する。

## GeneralDictionaryRequestProvenanceTrace

`recorded_step`, `supported_step`, `supported_trace`, `reachable_trace`, `models_after_trace`

任意registry/rootと実際のValue Step/Stepsについて、Recorded CoveredおよびSupportedは現在packet保存または履歴の延長により保存される。到達可能な始点から終点も到達可能。始点Supportedと実際のtraceから、任意の終点journal modelで同じbatch Models。

## GeneralDictionaryReservedClassifierSoundness

`current_requests_exact`, `structural`, `selected_path_root`, `covered`, `classifier_evidence`, `inhabited_classifier_evidence`

既存の実reserved install fixtureについて、任意captureで実際の要求=[request]、scalar Structuralを構成。選択rootの子が空でLocalがfunctionalなため全SelectedPathのfocus=rootとなり、Coveredを仮定でなく証明する。任意の現在journal modelに対し実Classify payloadのEvidence。具体的positive modelでEvidenceかつ非Stableの非空な例を示す。

## GeneralDictionaryReservedEqualityStep

`raw_countermodel`, `not_raw_equal`, `equality_step`, `installed_not_stable`, `models_iff`, `reachable`, `final_evidence`, `reachable_dictionary_after_feedback`

実reserved install fixtureのraw contextの反例modelからraw equality不成立を証明する。一方journal equalityが成り立つので実Value equate(2,0)が可能、従って非Stable。任意assignmentについてfeedback後Modelsとinstall後Modelsが同値、feedback後状態は到達可能、全そのmodelで現在Evidence。非空な辞書/到達例を同時に示す。feedback後のStableはここでは結論しない。

## GeneralDictionaryReservedInstalledClassification

`selected`, `decisions`, `value_selected`, `classified`, `selected_not_yet_stable`

既存reserved fixtureのinstall後スナップショットについて、旧選択判断/decisionsおよびValue Local selectedとClassifyを具体的に導く。選択済であってもStableではないことを同時に示す。分類完了と飽和停止を同一視しない。

## GeneralDictionaryReservedInstalledEvidence

`current_instance`, `current_evidence`, `ordinary_continuation_evidence`, `actual_reserved_dictionary`

実reserved install fixtureについて任意の現在journal modelで現在InstanceとEvidence。任意のordinary-only continuationについて終点modelからEvidenceを運ぶ。具体的な初期到達性、真の未割当reserved source、install、positive modelを伴う辞書例で空虚性を除く。

## GeneralDictionaryReservedMixedProvenance

`source_observed`, `reserved_covered`, `supported`, `installed_batch_models`, `after_batch_models`, `inhabited_mixed_provenance`

同じ実fixtureで元source0のObservedと新reserved source2要求のRecorded Coveredを構成し、結合した2要求のSupportedを証明。任意のinstall後modelまたは実feedback後modelでこのbatch Models。positive modelを伴う具体例も示す。

## GeneralDictionaryReservedOutputEquality

`nominal_repeated_scalar`, `output_equal`, `source_equal`, `journal_equal`

任意有限arityとscalar baseについて、repeated scalar nominal testの意味論を具体的なnominal値への等式として再構成。reserved fixtureで任意journal modelのoutput2とsource0が同じ三つ組nominal値になり、journal equality(2,0)を導く。raw contextだけから同じ等式を主張しない。

## GeneralDictionarySelectedProvenanceCoverage

`dictionary_evidence`, `dictionaries_evidence`, `root_dictionary_evidence`, `completed_tree_evidence`, `covered_of_global`

任意registry/root/Value到達状態について、実selected descendantsだけの構文的StructuralとSupportedを持つCoveredを仮定。任意現在journal modelと、SelectedPath終点における実Classify selected有限payloadからEvidence。All₂版、root版、既存Resolves/Completedからの版を導く。強いglobal coverageはこの局所coverageを含意する。executorが正確であるという仮定や結論は導入しない。

## GeneralDictionaryReservedSuccessorBoundary

`raw_equal`, `no_target_slot`, `output_not_known`, `point_closed`, `no_reobservation`, `stable_excludes_output_refresh`

実reserved installの等式反映後状態についてRawEqual(2,0)、source2のcarrier slot不存在、Known不成立を証明。全nominal記述子がPointClosedなので、任意のRevisionに対しImprovesは偽。最後の定理は「もしStableであれば、任意のRefresh証明を持つnext contextでsource2がKnownになることはない」という必要条件のみ。Stable自体や全refresh不存在は証明していない。Refinesはcarrier拡張を許すため、現在slotが無いという事実だけで全refreshを排除できない。

## GeneralDictionaryNonterminalProvenanceApplication

`parent_requests`, `parent_structural`, `child_requests`, `child_structural`, `selected_path_cases`, `covered`, `classifier_evidence`, `inhabited_recursive_application`

既存の実非終端install fixture（三項nominalの親、scalarの子、名前付き出力）を対象とする。任意captureの親要求は既存観測要求singleton、子要求は空。親は実初期観測と実install traceからSupported、子は空要求からSupportedを導き、各現在head Shapeを構成する。任意の実SelectedPath終点はrootまたはchildに限られるためCoveredを仮定なしに証明。任意の現在journal modelに対し実Value Classifyの再帰payloadのEvidenceを新しい一般pipelineで導く。具体的model、子数1、非空のnamed outputを伴う例を示す。古いEvidenceやBranchModelsをCoverage構成の前提にしていない。

## GeneralDictionaryReservedNominalRefresh

`snapshot_models`, `output_member`, `output_known`, `refresh_step`, `equality_successor_not_stable`, `refreshed_models`, `refreshed_reachable`, `refreshed_inhabited`

reserved fixtureの等式反映後について、carrierを2から3slotへ拡張したsnapshotを具体的に構成。任意の現在journal modelが新snapshotのModelsを満たし、source2は旧sourcesに所属し、新snapshotでKnown。Refines・解釈不変・全model妥当性・source保存を持つRefresh証明から、実Value refreshを導く。従って等式反映後もStableではない。任意assignmentでrefresh前後のjournal Modelsは同値、refresh後は初期状態から到達可能でpositive modelも持つ。最終refresh後のStableは未証明。新slotのrowSourceは既存0を用い、未証明の新row条件を追加していない。

## GeneralDictionaryReservedRefreshedEvidence

`metadata`, `recorded`, `requests_exact`, `covered`, `supported`, `current_instance`, `current_evidence`, `reachable_inhabited_dictionary`

実nominal refresh後の3slot contextを対象とし、Metadata、記録packet所属、任意captureの実要求=[request]、Covered/Supportedを構成。slot1の現在scalar Shapeと到達可能性を用いて、任意のrefresh後journal modelに対し現在InstanceおよびEvidenceを一般定理から導く。Local・Stable・executorの仮定はなく、旧contextのEvidenceをそのまま流用しない。到達可能性、positive model、Known source2、現在辞書を結合した非空の結果も示す。最終Stableやrefresh後Classifyは主張しない。
