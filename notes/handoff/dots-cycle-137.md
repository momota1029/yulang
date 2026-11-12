# Cycle137: 検査の有限 footprint と現在文脈の辞書証拠

開始: 2026-11-12T08:27:19Z。ユーザー指定の締切: 09:22:19Z。
新規取得した integration: `7ce74a0f2f14b326b824382a85fbe2d150fa9961`。
standing orders / inbox を最初に読み直し、08:54にも取得し直して同一 I-24 を確認した。
前回136は completed、公開済み、writer解放済み。前回と同じ作業への並行書込みなし。

## 最終的な主要成果

**任意の再帰的な検査が既に Finished なら、同一source carrier・同一正規化view上の実際の
Refinesだけで、その検査レポート全体を保存できる。** 入れ子・非point区間・originを任意に含む。
途中成果で必要だったfootprint一致・占有・report等値の追加前提を除去した。
既存InstanceはFinishedを含むため、Instanceと完全な既存Evidenceの運搬にも追加guardは不要。
実際の普通の更新と認証済みrefreshを交互に行う有限列へ接続し、同じ最終モデル・payloadを保持する。
SourceFormedの記録からの結果は、packet membershipと記録context→開始contextの普通のExtensionを明示する。

scalar成功時はdescriptorがNoneであり、固定viewとbodiesOpaqueから新たなSomeへの変化を排除する。
nominal成功時は既存のSomeを実際のRefinesが保持する。構造型は固定viewの子に帰納し、
append/visitのFinishedを分解する。結論に相当するEvidenceやJointを新たな前提としていない。
実モデルを持つ入れ子のnominal/scalar例で、内部引数(2,3)は非pointで、footprintが占有されていなくても
この一般版が使えることを確認した。

最終source: `197b693655908f4edf82abf593e4ad53878ec16c`。
focused656 jobsと93宣言のtrust-zero公理監査PASS。読取り独立レビューでも循環や結論相当仮定なし。

## 途中段階からの積み上げ

任意の registry・source context・モデル・需要・宣言キー・子リストについて、
有限な検査箇所だけが保存される descriptor refresh 後に、**現在の文脈**で同じ
親 Instance と辞書 witness を使える条件を証明した。過去 packet の context を
現在 context とみなしていない。子の証拠も、一つの最終モデルと現在 context で要求する。

- 再帰的な query から descriptor の読み取り箇所を計算する。変数 pattern は子孫を検査しない。
  nominal の両端・入れ子の type argument・構造型の子を扱い、非point区間も含む。
- 正規化 view を固定し、計算した footprint の descriptor だけを一致させれば、capture、
  checked interval、anchor、test を含む検査レポート全体が保存される。
- 保存条件は選択された宣言キーだけに限定できる。他候補のレポート保存は要求しない。
- 同一carrier上の実際の Refines はsourceの単射性から埋込みが恒等になり、既存の Some descriptor
  を保持する。従って選択キーの footprint が既に占有されていれば、descriptor等値も
  report等値も仮定せずに保存を導ける。占有は十分条件であって全候補に成立とは主張しない。
- SourceFormed の実際の記録から取り出した Instance を、普通の拡張・認証されたrefresh・
  普通の更新列、さらに条件を満たす実際の混合更新列を通して、最終contextへ運ぶ。
  Refresh certificateだけで新しいStepが有効とは主張しない。混合列は各遷移に実際のStepを要求する。
- 有限な実際の辞書witnessに現れる (需要,キー) だけを保存すれば、payload・キー・子の順序と
  多重度をそのまま保てる。DictionaryEquivalentによってfootprint条件も変わらない。
- 具体例は実際のrefreshと非空モデルを持つ。親は変数patternなので新しく記述された子を
  検査せず保存される。一方、その子を実際に検査するqueryのblockedレポートは変化する。
  子はK2拒否なので、完全な再帰辞書を作ったとは主張しない。

Astraの定義、Evidenceの意味、Step/Stable/Generated、lake設定は変更していない。
B4SkeletonV4の未証明フィールドは **8/13のまま**。本結果はevidenceNodeの部品であり閉鎖ではない。

## 復元・公開・制限

前回終了後のworkspaceが古いcycle32 snapshotになっていたので、最新integrationから復元した。
Lean/cacheが無く、公式Lean4.35.0を取得してfocused依存を再構築した。約637 jobsの初回復元後、
キャッシュを再使用。ツールチェーン展開時にディスクが満杯になり、取得済み展開archiveを除去して
空きを回復した。証明ソースや既存キャッシュを消していない。

I-24に従い `lean/Audit.lean` と `lean/README.md` は上流と同一blobのまま凍結。
旧巨大Audit blobの承認待ち操作は再試行していない。新しい小さなAudit shardと新しいmodule guideを使った。
GitHub appでwork/dots-mainだけを非force・expected SHA付きで更新し、承認待ちは発生しなかった。

中間公開:
1. `889ed528fb3eb1406f1cc4a794d165708dd4d2b2`: 初期4モジュール、28宣言監査。7本文をbyte照合。
2. `3020ccdd34785b7ea53a90f8c91de65b8ef3c306`: 追加finite footprint/selected key/actual trace。
   11本文をbyte照合。再帰tree `2b86a20f50e43e3c1847cf69909574216d6f3324` は非truncated、
   2740 entries。新規/変更17ファイルと凍結2ファイルの全19 blob SHAがローカル内容と一致。

心拍: 開始直後、08:37、08:44修正、08:47。途中で予定時刻08:47を実際より早く書いた誤りを
08:44の訂正commitで明示修正した。成果公開と心拍は別に行った。

最終source tree `4631c14d9b4cf42cad7993c607d9477435c7af17` は非truncated、2747 entries。
変更24ファイルと凍結2ファイルの26 blob SHAを内容から再計算して全一致。
9件の最終追加本文もbyte照合し、work/dots-main refの197b6936到達を確認した。

## 検証と失敗の扱い

- 復元focused build: PASS637 jobs。
- 初期focused build: PASS641 jobs。最初のAudit28宣言PASS。
- 第二source checkpoint focused build: PASS649 jobs (`--wfail`)。
- Audit/Cycle137.lean と Audit/Cycle137Followup.lean: 計66宣言、`--trust=0` PASS。
- 使われる公理は標準propext/Classical.choice/Quot.soundのみ。sorry、新axiom、native_decideなし。
- 初回diff gateは未commitの新規ファイルを検出したため失敗し、正確にstage/commitして再検証PASS。
- 開発中の構文/暗黙引数/pointSite簡約の失敗は修正してから検証した。
- 共有cacheへのhelper build中にAuditが一度object欠落で失敗。全buildを止めて順番にfocused buildと
  両Auditを再実行しPASSした。失敗した実行を成功として数えていない。
- 全体lake build、巨大legacy Audit、全project AxiomGate、Rust suite、新Yulang2実行は未実施。
  全体検証は禁止に従って監督役へ残す。diff gateのPASSは全buildのPASSではない。

- 最終combined focused build: `lake build --wfail Yulang.GeneralDictionaryFinishedTrace Yulang.GeneralDictionaryFinishedInspectionExamples Yulang.GeneralDictionarySelectedTree Yulang.GeneralDictionarySelectedLocalityExamples`: PASS656 jobs, exit0。
- `lake env lean --trust=0 Audit/Cycle137Finished.lean`、`Audit/Cycle137Followup.lean`、`Audit/Cycle137.lean`: 全てexit0、合計93個の重複なし宣言。
- ログ機械検査: 全93宣言がpropext/Classical.choice/Quot.soundの範囲内。新規18モジュールのimport登録を全件確認。
- 最終差分検査の全出力（exit0）:

```text
verify-lean: . @ e63891550 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

## SourceBoundary 13項目

「一般の定義あり」は言語全体の網羅性やB4の証明済みを意味しない。

| 項目 | 状態・制限 |
|---|---|
| Checked | 一般の定義あり。既存の検査済み宣言registry |
| Models | 一般の定義あり。実際のjournalとsource models |
| RootPending | 一般の定義あり。source observationの網羅性は保守的 |
| RootK2 | 一般の定義あり。現在のfeedback/cycle述語 |
| CandidateK2 | 一般の定義あり。現在のfeedback/cycle述語 |
| InspectionPending | 一般の定義あり。未対応inspection/materializationはpending |
| Survivor | 一般の定義あり。source compilation全体の完全性は未証明 |
| Reorders | 一般の定義あり。既存のvisible/where順序関係 |
| DictionaryEquivalent | 一般の定義あり。既存のpayload同値 |
| Step | 一般の定義あり。Astraの実際のfeedback stepsを変更せず使用 |
| Stable | 一般の定義あり。Astraのno-step安定性を変更せず使用 |
| Generated | 一般の定義あり。実際の生成closure |
| Evidence | 一般の定義あり。独立したsource-indexed recursive Evidence。固定view実refinement運搬を今回証明。全安定状態のnode橋は未証明 |

## B4SkeletonV4: 未証明8/13

| フィールド | 状態 |
|---|---|
| progress | OPEN。一般のinstallation descentは未証明 |
| execution | OPEN。完全な一般executorなし |
| halted | OPEN |
| closure | 実際のfeedback boundaryについて上流で証明済み |
| stepModels | 同じ実際のboundaryについて上流で証明済み |
| frontierLocal | 実際の非計算的frontierについて上流で証明済み |
| localIdentity | 同frontierについて上流で証明済み |
| whereAccessible | OPEN。readback前提が残る |
| treeExecution | OPEN |
| canonicalLocalOrder | OPEN |
| dictionaryRefl | 上流で証明済み |
| evidenceNode | OPEN。既存記録の現在contextへの運搬を改善したが、全stable選択の記録網羅性は未証明 |
| generatedChildren | OPEN。stable selected Joint/applicabilityが残る |

## 次の具体的課題

1. 候補補題 `finished_refinement_source_transport`: 同一view・同一carrierという制限を、source識別子の埋込みと検査結果の対応へ一般化する。
   変わるviewではcaptureのslotやshape番号が変わり得るため、今回のreport完全等値を無条件に主張しない。
2. 候補補題 `stable_selected_joint_in_model`: 実際のstable・SafeKnown・Unique・Modelsの前提から、選択に対するjournal-compatibleな枝と記録の対応を証明する。
   Stableの定義変更やEvidenceそのものの仮定追加で穴を埋めない。
3. 候補補題 `feedback_evidenceNode`: 選択された親と全生成子の現在context証拠を一般boundaryのevidenceNodeに接続する。
   V4のEvidenceNodeは全状態を量化し、SourceFormedを前提にしていない。今回のSourceFormed限定の
   記録運搬だけではこのフィールドは閉じない。無断で到達可能性前提を追加していない。

新しい意味論判断の質問は積んでいない。残る課題は上記の明示した証明義務。
raw stable-selected/notJointの古い例はjournal modelが空であり、モデル付きevidenceNodeの反例ではない。
モデル付きjournal obstructionにはStable証明がない。この二つを混同していない。

## 定理名と量化範囲

全93宣言の量化子・前提を省略しない型は
[theorem-signatures](../design/2026-11-12-cycle137-theorem-signatures.md) に記録した。
以下は対応する日本語の主張一覧。補助定理・回帰例も含む93宣言であり、93個のB4課題を閉じたという数ではない。

### GeneralDictionaryCurrentContextReplay

任意のregistry・context・モデル・需要・キー・子について、普通のExtension、親のreport保存、中間と最終の同じモデルの妥当性から現在Instanceを得る。SourceFormedとpacket所属・現在context同定があれば記録から導出でき、最終contextの子Evidenceを合わせて親Evidenceにする。具体的なrefreshの後の任意の普通の実更新列にも適用し、実行列と非空モデルを示す。

宣言: `instance_replay`, `sourceFormed_recorded_current_instance`, `sourceFormed_recorded_current_evidence`, `refreshed_parent_after_ordinary_trace`, `refreshed_tail_execution`, `refreshed_parent_nonvacuous`。

### GeneralDictionaryFinishedEvidence

任意のcontext・実Refines・同一viewについて、任意の旧Finished reportを完全保存する。任意registry・モデル・需要・キー・子の旧Instanceと新contextのモデルから新Instanceを得る。任意の旧Evidenceも同じpayloadで保存する。SourceFormed・記録packet・普通の初期Extension・実Refresh・最終モデルがあれば旧Instanceを前提にせず記録から取得する。

宣言: `report_finished`, `instance_refinement`, `evidence_refinement`, `recorded_refresh`。

### GeneralDictionaryFinishedInspection

任意の再帰QueryまたはQuery列、bounds、origin関数、開始indexについて、同一view・実Refines・旧Finishedだけで新inspect/inspectManyが旧reportのtransferと一致する。任意の入れ子と非point区間を含み、footprintや占有条件はない。

宣言: `inspect_finished`, `inspectMany_finished`。

### GeneralDictionaryFinishedInspectionExamples

具体的nominal/scalar queryのFinishedを示し、slot2のdescriptorはNoneなのでfootprint全体の占有は偽と示す。任意の同一view・実Refinesの次Observationに一般検査保存を適用する。既存の実モデルとFinishedと非占有を同時に証明し、内部引数(2,3)が非pointである。

宣言: `nested_finished`, `footprint_not_occupied`, `nested_survives`, `nonvacuous_nested`。

### GeneralDictionaryFinishedRefresh

任意のnominal query・bounds・originで旧Finishedなら両端descriptorが存在する。任意の変数group列ではfootprintが空で、flat nominal queryでは両端だけになる。実Refines・同一view・旧Finishedから任意のflat nominal report保存を導く。後の一般再帰定理の補助。

宣言: `finished_nominal_lower`, `finished_nominal_upper`, `variable_footprints`, `flat_nominal_footprint`, `flat_nominal_finished_preserved`。

### GeneralDictionaryFinishedTrace

任意registry・root・状態について、制限付きStep/Stepsから実際のfeedback Step/Stepsを得る。各refreshは同一carrier/viewと実Refreshと実Stepを持つ。任意の最終モデルにおける旧Instance/Evidenceを同じキー・子・payloadで運び、SourceFormed記録からも運ぶ。ノード別report/footprint/占有guardなし。具体的なdescriptor変更Stepとそのモデル全てでの現在親Instanceも示す。

宣言: `step_feedback`, `trace_feedback`, `step_instance`, `trace_instance`, `trace_evidence`, `recorded_trace_instance`, `Actual.descriptor_changing_step`, `Actual.current_parent_without_guard`。

### GeneralDictionaryInspectionLocality

任意の変数queryのfootprintは空。任意reportのappend/visitとtransferは可換。任意再帰query/listについて、同一viewと有限footprintでのdescriptor一致からinspect/report保存を導く。任意registry・需要の有限guardからPreservesAtを得て、最終モデルと旧Instanceを用いて現在Instanceを得る。最終contextの各子Evidenceを加えれば親Evidenceになる。

宣言: `variables_footprint`, `transfer_append`, `transfer_visit`, `inspect_local`, `inspectMany_local`, `report_local`, `preservesAt_of_footprint`, `instance_of_footprint`, `node_of_footprint`。

### GeneralDictionaryInspectionLocalityExamples

具体的親のfootprintはslot0だけで、実refreshはそこで一致する。任意の最終モデルで親Instanceを得て、実モデルの存在も示す。入れ子queryでは両端slot2,3も読み取り範囲となり、実際に子を検査するqueryではblockedレポートが変わる。変数patternと入れ子patternを混同しない回帰。

宣言: `parent_footprint`, `parent_footprint_agrees`, `current_parent_from_footprint`, `nonvacuous_parent_from_footprint`, `nested_nonpoint_footprint`, `inspected_child_report_changes`。

### GeneralDictionaryInspectionTransport

任意reportのtransferでbindings/selfChecks/Finished/ProjectionModels/Materializationの意味が保存される。任意の単項nominal-variable queryで参照descriptor一致ならreport一致。任意registry・需要・宣言でreport一致なら生成要求が一致し、同じ最終モデルと旧BranchModelsから新BranchModelsを得る。親report保存と旧Instanceから現在Instance、現在contextの子Evidenceを加えて親Evidence、全需要のreport保存なら既存Evidence全体を保存する。

宣言: `transferred_bindings`, `transferred_selfChecks`, `transferred_finished`, `transferred_projection`, `transferred_materialization`, `nominal_unary_report`, `generated_eq`, `branch_of_report`, `instance_of_reports`, `node_of_reports`, `evidence_of_reports`。

### GeneralDictionaryInspectionTransportExamples

具体的Observationが実refreshedContextと一致し、親のreport保存を満たす。任意の実refreshedモデルで現在親Instanceが成立し、具体モデルも存在する。生成された子slot2のdescriptorはNoneからSomeへ本当に変わる。子辞書の存在は結論に含めない。

宣言: `reobserve_eq`, `parent_preserves`, `current_parent_instance`, `nonvacuous_refreshed_parent`, `child_descriptor_changed`。

### GeneralDictionaryRecordedRefresh

任意SourceFormed状態・所属packet・普通の初期Extension・実Refresh・親report保存・最終モデルについて、記録から現在Instanceを得る。任意の普通の実更新tail後にも同じキーと子で成立する。最終contextで各子Evidenceが与えられれば親Evidenceを合成する。

宣言: `recorded_refresh_instance`, `recorded_refresh_tail_instance`, `recorded_refresh_tail_evidence`。

### GeneralDictionaryRefinementInspectionFacts

任意context/Observationで同一viewかつ参照headが未解決deferredでなければ新nominal descriptorはNone。任意reportのappendがFinishedであることは両方Finishedと同値、visitはFinishedを変えず、任意boundsのblockはFinishedではない。

宣言: `none_of_visible`, `finished_append`, `finished_visit`, `block_not_finished`。

### GeneralDictionaryRefreshDescriptors

任意same-carrier reobservationへの実Refinesの埋込みはsource単射性により恒等。任意descriptorの恒等renameは元と等しい。従って任意slotに既に記録されたSome descriptorは新Observationでも同じSomeである。

宣言: `embed_identity`, `rename_descriptor_identity`, `descriptor_preserved`。

### GeneralDictionaryRefreshTrace

任意registry/root/siteの制限付き更新と列が実feedback更新であると示す。各refreshは実Stepと当該siteのreport保存を持つ。任意の最終モデルで旧Instanceを同じキー・子で運び、SourceFormed記録と初期Extensionからも導ける。後のFinishedTraceでノード別guardを除去したが、この一般report条件版も保持する。

宣言: `step_feedback`, `trace_feedback`, `step_instance`, `trace_instance`, `recorded_trace_instance`。

### GeneralDictionarySelectedLocality

任意registry/context/需要/キーで、選択キーの有限footprint占有と実Refinesからdescriptor一致を導く。同一view・最終モデル・旧Instanceと選択キーfootprint一致または占有から現在Instanceを得る。SourceFormed記録・初期Extension・実Refreshと選択キー占有から記録packetの現在Instanceを得る。全候補の占有は要求しない。

宣言: `footprint_of_occupied`, `instance_of_footprint`, `instance_of_occupied`, `recorded_instance`。

### GeneralDictionarySelectedLocalityExamples

実際の親の選択キーfootprint占有を計算で確認。任意の実refreshedモデルでSourceFormed記録を現在親Instanceへ運び、具体的実モデル・親Instance・子のK2拒否が同時に成立する。

宣言: `parent_occupied`, `recorded_parent_current`, `actual_nonvacuous_parent`。

### GeneralDictionarySelectedTree

任意の有限辞書witnessについて、観測される(需要,キー)のfootprint条件は各子へ制限できる。同一view・最終モデル・旧indexed Evidence・この有限条件から同じ木のEvidenceを得て、Readbackがあれば同じpayloadへ消去できる。実Refinesと観測キーの占有でも条件を導ける。DictionaryEquivalentな木では有限条件は同値。

宣言: `footprint_child`, `indexed_of_footprint`, `erased_of_footprint`, `indexed_of_occupied`, `footprint_equivalent`。

### GeneralDictionaryTreeTransport

任意辞書の子の観測は親のchildObservationsに含まれ、有限witnessのreport保存条件をrootと子に制限できる。最終モデル・旧indexed Evidenceと有限report条件から同じ木を保存し、Readbackがあれば同じpayloadを得る。DictionaryEquivalentで条件は同値。後のSelectedTreeより強い全候補条件の版も保持する。

宣言: `child_observation`, `preserves_root`, `preserves_child`, `indexed_of_reports`, `erased_of_witness_reports`, `preserves_equivalent`。

報告と型一覧も独立レビューを実施。93個の監査対象・93個の型・source宣言の対応を照合し、前提の脱落なし。

最終source公開後、新規18モジュールの各ソースを個別に `lake env lean --trust=0` で再検査し、18件すべてexit0。
キャッシュのビルド結果だけに依存した照合ではない。追加心拍は08:57・09:07にも公開した。

## 報告確定

報告準備完了: 2026-11-12T09:13:27Z、開始から46.15分。
最終公開の検証後に心拍をcompleted・writer releasedへ更新する。新規18モジュール、3監査shard、登録1、
設計ノート2のsource24ファイルを公開済み。今回の型一覧・報告2ファイルと既存心拍を含め、公開対象は計27パス。
公開保留のソースはない。最終終了時刻と報告先はcompleted心拍で確認できる。
