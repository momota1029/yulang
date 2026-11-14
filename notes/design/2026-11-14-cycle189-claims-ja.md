# Cycle189: 初期 leaf の実 Evidence と、同一 plan の出力条件

以下の roles/registry/root/state/candidate/model/有限 list/自然数は、各条件の下で全称量化する。存在結論だけを存在量化する。完全な型は新しい Audit/Cycle189PublicTypes 群に保存する。全て辞書健全性へ向かう補助または局所結果で、一般の完全性・主型性・B4全体の達成ではない。

## 一般の機構（初期状態という範囲制約を保持）

### GeneralNominalOutputCoverage189
- schema_known / schemas_known: 任意有限再帰Query・origin・mode（list版はoffsetも）について、既存Completeなら実schema.unknown=false。
- generated_known / generated_known_iff: 任意source state・interpretation・有限request列について、実generated.unknown=falseと、各requestの正規化patternの翻訳QueryがCompleteであることは同値。modelの存在ではない。
- effects_ready: 任意centered state/root/plan、各実requestに関連型equationがあり、planの全associated RHS翻訳がCompleteなら、実EffectsReady。
- selected_named_outputs: Checked、実WF Initial、実Local.selected、同roleの全可視宣言についてrootの各出力のequation coverageと全associated翻訳Completeから、current ModelsとChosenClassEffectsを満たすmodelが存在。V6 selectedの「出力conflictなし」を使う。出力modelをアルゴリズムで構築した、またはconflictが起こらないという主張ではない。

### GeneralNominalHeadLeafPlan189
leaf = candidate.declaration.requirements=[]。空出力 = root.demand.outputs=[]。head Queryの形状は任意、再帰深さやhead変数数を制限しない。
- emitted_empty / input_schema_empty / named_schema_empty / children_empty: leaf（named版は空出力も）から実emission・schema・childrenが空。
- head_to_plan: leaf、空出力、同じmodelのHeadEquationsと実HeadModelsから完全なPlan.Holds。
- initial_plan: Checked、実WF Initial、実Frame、leaf、空出力からcurrent ModelsとPlan.Holdsを同時に満たすmodel。model・private projectionの成立は仮定しない。
- installed_requests_empty: 任意stateの実requestsが空でleafなら、任意supportで実installした後の実requestsも空。
- output_equations_empty: 任意state/plan/modelで実requestsが空ならOutputEquations。
- initial_installation_model: initial_planと同条件から、任意supportについて正確なInstallationModelsを満たすmodel。現在・更新後の出力条件とlive ledgerも含む。
- initial_selected_installable: 上記に実Local.selectedを加えると実Installableを持つsupportが存在。生成完了・choice・value support・安全性を具体的に導く。

### GeneralNominalInitialLeafStep189
- selected_candidate: Checked、実Initial、実selected、選択keyに一致する全可視宣言がleaf、空出力から、Frame/正確なchildren/Installableを持つcandidateとsupportを構成。Frameをcallerが渡す必要はない。
- committed_or_step: 同条件から、そのcandidateが実Committed、または実WF Stepの後続がある。Committedはpacketがjournalにあることではなく全modelの意味的成立なので、無条件の新規Stepにはしていない。
- selected_novel_step: 実Frameとleaf/空出力、同candidateが未Committedなら実Stepかつ後続Modelsがinhabited。
- selected_novel_not_stable: 同条件で実Stableではない。

### GeneralNominalInitialLeafEvidence189
- stable_committed: 任意stateで実Stable、実Frame、実Installableから実Committed。初期状態に限定しない。
- committed_instance: 任意state/Frame、leaf、空出力、実Committedと任意current modelのModelsから、そのmodelの実RecursiveEvidence.Instance（children=[]）。
- stable_selected_evidence: Checked、実WF Initial、実WF Stable、V6 Local.selected(key,children)、key一致の可視宣言がleaf、空出力なら children=[]、かつ **任意modelのcurrent Modelsから実WF boundary.Evidence(root,node key [])**。Frame・model存在・Committed・別のEvidence判断は仮定しない。

これは初期root/whereなし/出力要求なしという範囲で、存在的な実行可能性から全modelの既存辞書判断まで接続した結果。一般reachable stateに対するEvidenceNodeではない。

### GeneralNominalInitialFrameUnique189
- initial_unique / boundary_initial_unique: Checkedなregistry、初期state、同root/keyの任意2実Frameから、そのPlan全体が等しい。証明を含むpacketも等しい。
- effects_on_frame: 初期stateの実ChosenClassEffectsのmodelを変えず、任意指定Frameのplanに対するready/head/outputを取り出す。
- selected_frame_model: Checked、実Initial、実selected、指定Frame、そのFrameだけのreadyから、同じplanのcurrent/head/outputを同時に満たすmodel。188に残った「別eligible planかも」は除去したが、このmodelのHeadModelsは結論に追加していない。

### GeneralNominalInitialOutputExact189
- conflict_iff: Checked、実Initial、実Unique、指定Frame、readyから、実StepBoundary.OutputConflictと、指定planのcurrent/head/outputを同時に満たすmodelがないことが同値。正のhead baselineは導出し、仮定しない。
- no_output_conflict: 実Initial/Frameで空出力なら実OutputConflictはない。既存の空request結果の特殊化で、独立した進展として数えない。
- selected_named_frame: Checked、実Initial、実selected、指定Frame、root出力のequation coverageと指定planだけのassociated RHS Completeから、同planのcurrent/head/output model。全可視宣言への条件を外したが、selectedの意味的no-conflictを使う点は変わらない。

## 非空性の回帰（一般機構の証明とは別）
InitialLeafFixture189/InitialLeafLocal189/InitialLeafNonvacuity189は既存TerminalFork scalar sourceとintDisplay leaf宣言を再利用する。boundaryは変更しない。inhabited_stable_selectedでChecked、実Initial、実Stable、実selected、Modelsのwitness、実Evidenceを同時に構成する。単に「初期stableなら」という不可能な前提の含意を通しただけではない。回帰補助44定理は親目標の閉鎖本数に数えない。

## 13項目の定義台帳（定義と証明を区別）

| 項目 | 状態 | 実装先・制限 |
|---|---|---|
| Checked | 一般の定義あり | GeneralDeclarations.Checked;十分な宣言検査 |
| Models | 一般の定義あり | HeadStepEffects.Models;live ledgerを含む |
| RootPending | 一般の定義あり | HeadStepBoundary.fields |
| RootK2 | 一般の定義あり | 同fields;実中心/循環ガード |
| CandidateK2 | 一般の定義あり | 同fields |
| InspectionPending | 一般の定義あり | 同fields;partial translation限界あり |
| Survivor | 一般の定義あり | HeadCandidates;head-only |
| Reorders | 一般の定義あり | RegistryReordering |
| DictionaryEquivalent | 一般の定義あり | 既存payload比較 |
| Step | 一般の定義あり | HeadStepKernel.Step;今回初期leafで実enabledを導出 |
| Stable | 一般の定義あり | HeadStepKernel.Stable;変更なし |
| Generated | 一般の定義あり | 実journalの生成関係 |
| Evidence | 一般の定義あり、橋は断片 | 既存RecursiveEvidence;今回初期stable leafの全model橋 |

V6はSkeleton構造を持たないため、架空のフィールド分母は書かない。一般reachable EvidenceNode、child materialization全般、最終Statementは未証明。一般フィールドの新規閉鎖は0。既知multi-tag生成阻害は修復していない。
