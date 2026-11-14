# Cycle187: 現在候補のhead拡張と独立した検査制約

## 主張と限界

I32のWF/V6境界。任意のroles、Checked registry、同境界のInitialから到達したstate、現在の実Frameを持つcandidate、任意のassignmentについて、**同じassignment**が現在Models・実HeadModels・centered headInspectionのProjectionModelsを満たすなら、旧fullSourcesと候補の宣言済みcapture端点の値を保ち、ModelsとHeadModelsとProjectionModelsを保ったまま、candidateの全HeadEquationsを満たすassignmentへ拡張できる。

歴史planの登録、候補の以前のinstall、root-only、点区間のみ、言語断片のcovered仮定は不要。ただしFrameはcandidate.inputが現在sitesに登録済みであることを要求する。「未install候補」は「未登録input site」ではない。

これは健全性のためのモデル構成の補助であり、全言語の健全性・完全性・主型性の完成ではない。Preparedのあるモデルが現在Modelsやcentered ProjectionModelsも満たすとは示していない。新しい候補のOutputEquations、Plan.Holds、子materialization、一般EvidenceNodeは未証明。使わない将来の予約outputキーまで不変とは主張しない。

## 各定理（47本、すべて補助）

以下の任意性は各定理の型どおり。省略していない完全な型と公理は `lean/Audit/Cycle187FrameTypes.lean` と `notes/verification/cycle187/frame-reproduce.txt` に保存。名前の先頭は `Yulang.GeneralNominal`。

### CaptureBounds187（任意state/report/model/registry/invocation/declaration）
- `occurrence_iff`: 任意名・区間について、bindingsの同名occurrence所属 iff 同名captureがreportに存在してそのsource端点が一致。
- `occurrence_nonempty`: report所属captureがあれば、その名のoccurrencesは非空。
- `merged_iff_raw`: 実merge方程式、宣言済み入力名、非空occurrencesの下で、任意値のmerged Fits iff 全同名raw capture区間のFits。
- `projected_merged`: ProjectionModelsと実merge方程式の下で、所属・宣言済み名・実originを持つcaptureの任意観測値はmerged Fitsを満たす。結論Fitsを前提に置かない。
- `fits_equivalent`: 任意Equivalentな2型について、同一assignment/区間のFitsは同値。

### CaptureOrigins187（任意state/query/区間、完了・モデル前提なし）
- `shape_visit`: visitはcaptureの名/区間列を変えない。
- `shape_append`: report連結のshapeはshapeの連結。
- `inspect_shape`: 一つのqueryのcapture名/区間列はorigin変更に不変。
- `many_shape`: query列についてorigin関数と開始indexを変えても名/区間列は不変。
- `bindings_shape`: bindingsはshapeにsource写像を施したもの。
- `many_bindings`: query列のbindingsはorigin関数と開始indexに不変。

### SchemaCapture187（任意query/列、Finished、実origin）
- `schema_capture`: 任意のactual schema useには、同名かつ同originの実captureがinspectionにある。
- `schemas_capture`: 同じ主張を任意query列とoffsetへ拡張。

### SchemaTests187
- `visit_root`: 任意visitの根のtestと観測anchorが存在。
- `visit_retained`: 任意旧test/anchor witnessはvisit後も残る。
- `append_left`, `append_right`: 任意test/anchor witnessはreport連結の左右から残る。
- `schema_tests`, `schemas_tests`: 任意Finished inspectionとactual schema testに、inspection test所属と観測anchorが存在する（一つ/列）。

### HeadRawBounds187（任意現在candidate/Frame）
- `frame_occurrences_nonempty`: 任意宣言済み入力名のraw occurrencesは非空。Finishedから導出。
- `bounds_iff_raw`: Checked/reachable、登録historical plan、同numeric identity/宣言、同じ現在Modelsと実mergeの下でBoundsFit iff historical binder値が各useの全raw区間にFits。
- `revisit_extension_iff_raw`: 同じ前提の下で、現在Modelsと有限supportを保つ全head拡張の存在 iff 上記raw条件。

### HeadDeclaredBounds187
- `frame_name_use`: 任意現在Frameの各宣言済み入力名にはheadSchemaの実use indexがある。
- `raw_iff_declared`: 任意historical/candidate/Frame/modelで、use-index別raw条件 iff 全宣言済み名のraw条件。
- `revisit_extension_iff_declared`: HeadRawBoundsの同じ前提で、全head保存拡張 iff 全宣言済み入力名のhistorical binder値が全同名raw区間にFits。

### HeadProjectionBounds187
- `head_bindings`: 任意candidateのcentered headInspectionと実packetのbindingsは同一。
- `projection_bounds`: 任意現在Frame/modelで、centered ProjectionModelsと実merge方程式から全BoundsFitを導く。
- `revisit_extension_of_projection`: Checked/reachable/同identity・宣言のhistorical plan、Frame、現在Modelsに、centered projectionとmergeを足せば全head保存拡張がある。

### HeadInitialExtension187
- `projection_compatible`: 任意reachable state/現在Frame/modelで、centered projectionとmergeから全Compatibleを導く。tests・観測存在・Fits・binder衝突整合性を導出。historical plan不要。
- `frame_extension_of_projection`: Checked/reachable/現在Frame/現在Modelsと上記2条件から全head保存拡張。historical plan不要。

### HeadProjectionFrame187
- `roots_append`: 任意二reportのroot支持は連結で保持。
- `many_bounded_roots`: 任意query列/offsetで、実際に使うindex範囲のoriginとslotが支持されればreport全originが支持される。範囲外getDの値を仮定しない。
- `head_report_roots`: 任意現在Frameのcentered inspection全originは既存fullSourcesに入る。
- `report_sources`: 同Frameのprojectionが読む全sourceは既存fullSourcesに入る。
- `projection_iff`: 任意2assignmentが既存fullSourcesで一致すれば、centered ProjectionModelsは同値。

### HeadMergeFrame187
- `merge_sources`: 任意raw bindingsの端点と宣言済みcapture端点の支持だけから、全merge atomのsource支持。全予約キーの支持は不要。
- `candidate_raw_sources`: 任意現在Frameのcontext sourcesは有限support内。
- `candidate_endpoints`: 同Frameのraw binding端点は有限support内。
- `candidate_merge_sources`: 同Frameの全実merge atomは有限support内。
- `merges_iff`: 任意2assignmentが有限supportで一致すれば実merge方程式は同値。
- `extension_retains_inspection`: 初回候補のhead拡張は、現在Modelsだけでなくcentered projectionとmergeも保存する。

### HeadBranchFrame187
- `ordinary_iff`: 任意現在Frameと有限supportで一致する2assignmentについて、実packet Ordinaryが同値（cross、merge、selfChecksを含む）。
- `private_models_iff`: 同じ前提で実privateContext Modelsが同値。
- `raw_projection_iff`: 同じ前提でraw packet ProjectionModelsが同値。
- `branch_extension`: Checked/reachable/現在Frame、同じmodelの現在Models・privateModels・raw projection・centered projectionから、これらを全部保持した全head保存拡張。
- `head_models_exact`: 任意candidate/modelについて実HeadModels iff privateModelsかつraw ProjectionModels。新しい枝意味論を置かない。
- `head_models_extension`: 冒頭の主張。実HeadModelsを保ち、centered projectionを保ち、全head方程式を追加する。

## 13項目と未証明の区別

|項目|状態|
|---|---|
|Checked|一般nominal registry検査の定義あり|
|Models|core/保存effect/current出力の定義あり|
|Step|実HeadStepKernel.Stepの定義あり|
|Stable|同Stepの停止状態の定義あり|
|Generated|raw journal到達の定義あり|
|RootPending|head-only分類の定義あり|
|RootK2|head-only分類の定義あり|
|CandidateK2|head-only分類の定義あり|
|InspectionPending|head-only分類の定義あり|
|Survivor|head-only分類の定義あり|
|Evidence|FeedbackEvidenceの定義あり、一般EvidenceNodeは未証明|
|Reorders|一般定義あり|
|DictionaryEquivalent|一般定義あり|

V6のOutputConflictも定義あり。一般フィールドの今回新規閉鎖は0。V6のSkeleton構造体は存在しないので架空のk/14は作らない。既存WFTransferのExact・SaturationTotal・OrderIndependentと、今回の補助結果を区別する。DictionarySound・NoFalseRejection・Statement全体の新規完了はない。

## 次に必要な3つの橋

1. 現在の選択/安定条件から、同じassignmentに現在Models・実HeadModels・centered ProjectionModelsを同時に与える。Preparedの存在量化を勝手に強めない。
2. 新しい候補のOutputEquationsと子materializationを、今回の保存拡張へ接続する。旧effect/live出力の保存と新候補の出力成立は異なる。
3. 実生成子の辞書を親Evidenceへ組み立て、一般EvidenceNodeへつなぐ。既存upstreamのmulti-tag generatedChildren反例は別担当の境界修復が必要で、このcycleは修復も新発見も主張しない。
