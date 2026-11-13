# dot cycle167 — final-current Evidence と全Trusted slice の反例

## 起動と制約

2026-11-13 14:27:19 UTC の起動、実作業開始14:33 UTC。最新指示による締切15:22:19 UTCを、文書の長時間継続指定より優先する。前cycle166はd2efa569393ee0507be7034995c490337ac6e646、completed心拍・報告あり、稼働中writerなし。integration/m1-finalを取得し直した基点は8d83c0c2690584834d0fd78e1915895e41e44f7e。standing-orders、inbox、報告を再読し、ACTIVE/I27を確認した。監督版の競合解決を優先し、公開済み165の復元済み行は変更していない。公開先はwork/dots-mainのみ。

## 主成果

**producerのEvidenceを実際のscalar refresh後の現contextで回復した。一方、同じ到達状態のconsumerは、rawでは既知でもShared Trusted ReadyAtでないことを反例モデルで証明した。これは未解決仮定の追加ではなく、全Trusted sliceに対する否定である。**

### 現文脈Evidence〔健全性補助〕

`GeneralDictionarySharedCapturedFinalEvidence` と `...FinalCurrentEvidence` は、任意のassignmentについて `Models observed.current assignment` から、実際に再検査したfinalPacketのOrdinary/ProjectionModels/Outputs、BranchModels、current Instance、producerの葉辞書Evidenceを構成する。保存時contextとの同一視、存在モデルへのすり替え、結論であるBranchModels/Evidenceを前提にする手法は使っていない。具体的inhabitedモデルでEvidenceがあることも確認した。

### 一般のreport移送〔補助〕

`GeneralNominalReportSourceTransport` は任意のbefore/after状態・slot写像・reportを量化する。source識別子を保存する写像ならbindings、selfChecks、ProjectionModelsを保存する。Finishedの同値とMaterialization.Modelsの同値は、それぞれ必要なより弱い前提で証明した。これはinspection algorithmの不変性を自動的に示す定理ではない。`...SharedCapturedReportTransport.exact_relocation` は今回の新旧reportを別々に計算し、具体的な移送一致を証明する。

### 全Trusted sliceでの反例〔具体的な阻害〕

`GeneralDictionaryCapturedSettlementBoundary` は、aliasが空の任意状態でDischargedから同じidentityの記録済みpacketを得る一般補題と、Trustedに含まれるoutputがPacketSettledである一般補題を与える。実際のobservedではconsumerは未Dischargedであり、**任意のTrusted facts/readbacksについて**親outputを含めない。

`...CapturedAliasCountermodel` と `...CapturedInputCountermodel` は、target=int・captured source2=strの一つのモデルを構成する。このモデルはsource制約、親inputs、producer inputs、producer outputsを満たす。記録factの分類と親output不在から、**すべてのTrusted slice**のModelsを同じ反例モデルが満たすことを証明した。current側のsource2のheadはscalar intに限られ、任意の説明snapshotでscalar観察が成り立つなら同じscalar含意が必要になるため、`consumer_input_not_ready : ¬ ReadyAt observed 2` が従う。

この反例モデルをfull journalのモデルとは呼ばない。full journalではsource2≃intが成立するが、信頼されたsource＋sliceのモデル集合は異なる。この違いこそ反例の要点である。

`...CapturedInstallationBlocked` は任意のInstallable packet/supportについてPacketGuardを元のstateのDecisionGuardへ戻す一般補題を与え、実際のobservedでconsumerを指すguarded installationの前提が成立しないことを証明する。administrative更新、将来のsource-supported状態、全経路のdeadlock、`¬ Evidence`は結論しない。

`...CapturedEvidenceDelay.actual_evidence_with_trusted_delay` は同一のSourceFormed observedで、非空journalモデル、任意モデルでのproducer current Evidence、consumerのraw ready、Trusted ReadyAt不在を一つにまとめる回帰定理。両結果の非空虚性とcontext一致を確かめる。

## 定理索引と受入れ状態

新規9module・69公開定理。全名・正確な型は `lean/Audit/Cycle167PublicTypes.lean`。日本語での量化・前提・分類は以下に分けた:
- `notes/design/2026-11-13-cycle167-final-evidence-theorems.md`：23本。
- `notes/design/2026-11-13-cycle167-countermodel-theorems.md`：42本（Producer namespace内も含む）。
- `notes/design/2026-11-13-cycle167-installation-boundary.md`：3本。
- `notes/design/2026-11-13-cycle167-nonvacuous-regression.md`：1本。

I27の不足した既存19定理を新しい `Cycle167InheritedCapturedCoverage.lean` に登録した。既存AuditやLean行の修正はない。I21 Evidenceレーンを進め、I26の遅延を既存定義のまま確認した。Step/Stable/Generated/guard/意味論は変更していない。

| 13境界 | 状態 |
|---|---|
| Checked | 一般nominal定義あり、変更なし |
| Models | 一般定義あり。full journalとTrusted sliceの異なる非空モデルを明示 |
| Step | 一般Shared定義あり。既存4操作経路を使用、規則変更なし |
| Stable | 一般定義あり。今回の一般安定化・完了は未証明 |
| Generated | 一般定義あり、既存SourceFormed経路を使用 |
| RootPending | 一般定義あり。raw否定とTrusted ReadyAt否定の共存 |
| RootK2 | 一般定義あり、変更なし |
| CandidateK2 | 一般定義あり、変更なし |
| InspectionPending | 一般nominal定義あり、全Shared統合未完 |
| Survivor | 一般nominal定義あり、変更なし |
| Evidence | 一般定義あり。scalar refresh後の実際のproducer現contextへ接続 |
| Reorders | 一般nominal定義あり、変更なし |
| DictionaryEquivalent | 一般nominal定義あり、変更なし |

V5の継承会計は **未証明8/14** のまま。全Shared境界のevidenceNode、一般source-to-Evidence、完全性・主型性・canonical結果の完成ではない。MISSINGを新たに埋めたという主張ではなく、既存一般定義の具体的接続を進めた。言語全体の網羅性は別途残る。

## Yulang2比較

監査branchを再取得し55574b6052ef1534fd0fc36d6d3617ebede59a0eのx-oracle、parent-fixed、cycle5を読んだ。旧parent Left/Rightの実機例は今回のShared Trusted判定と同一とは証明していない。X2 where増大の差でspecを変更しない。cycle5は未定義`+`で36試行失敗しており、追加のF1証拠には使わない。旧binaryはこの環境に存在せず、新しいYulang2実行はしていない。詳細はcycle167-yulang2-comparison設計ノート。

## 検証・失敗・公開

- focused `lake build --wfail`：installation/final Evidence/report transportの対象724 cache-inclusive jobs、組合せ回帰725 jobs、exit0。全repo build・巨大Audit.leanは実行していない。
- supervisor復元分、前166依存、今回moduleを独立出力libraryへ `lean --trust=0` で再コンパイル。新規の全公開定理axiom/type、小audit、private/generatedも含む依存gateを検査する。正確な最終件数・公開後再実行は末尾台帳に記す。
- `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`：exit0、append-only PASS。REVIEW1件は新規dependency auditの `run_cmd`。環境の全宣言について依存公理を列挙する検査専用であり、production定理を作るものではない。コードを確認済みだがhuman-review表示は隠さない。
- 最初のaudit実行はcwdがrepo rootのため対象パスを見つけられずexit1。leanディレクトリで再実行して成功。
- restored replayの初回は新しい上流依存 `GeneralNominalActualBudget.olean` が未キャッシュで失敗。足りない依存だけソースから再構築し、26moduleの再実行が成功。全buildではない。
- 既存blobをまとめた読出しは出力上限に達しJSON parseで失敗。ファイルを小分けに読み直した。壊れたtreeは公開していない。
- 補助作業のdesign/auditの配置を公開前に指定のnotes/design、lean/Auditへ直した。既存公開ファイルは触っていない。移動に伴うcherry-pickのfile-location競合は正しい新規配置へ解決した。
- Evidence部とcountermodel部を独立に相互レビューし、現在context・全称範囲・非空虚性・将来状態を否定しない境界を確認した。
- 開始心拍effa379、途中成果ba929942、検証中の心拍690ac14。承認待ちなし。使用量枠は不明。自動化の停止・設定変更なし。

## 次の仕事

1. `GeneralDictionaryCapturedInputCountermodel` が示した固定状態の保留を保ったまま、source-supportedな別の初期例からconsumerを導入し、非終端親の有限辞書木へ接続する。
2. `GeneralNominalReportSourceTransport` をactual refreshの一般的なsource-preservation条件へ接続する。fresh report一致は独立に証明する。
3. I21/I25の一般Shared V5 evidenceNodeに必要な到達不変量を、今回のcurrent EvidenceとTrusted guardの区別を維持して整理する。

新しい意味論判断は行わず、I26の遅延指示に従う。今回の局所反例を理由にguardを弱めない。

## 追加の切り分け: settled producer の出力は実際にTrustedになる

source checkpoint `e65949934788380b72d566ef56a7bff39fd47753` を公開し、独立checkoutで取得した。凍結local `c720385c4a6066868ea0fe929daebfae5016b6d4` と全treeは心拍以外一致。独立出力libraryで34moduleと全cycle167小auditを `--trust=0` 再実行し、exit0、依存gate177宣言PASSを確認した。

その後、`GeneralDictionaryCapturedSettledProducerTrust.producer_output_trusted` を追加前提なしで証明した。実際のobservedにおいて、terminal producerのoutput factを含むTrusted facts/readbacks/supportが**存在する**。親の入力factを実経路に沿って移送し、正確なnominal descriptorによる入力readback、葉のsettlement、定数int recipeとOutputCertificateから構成した。単なるtag一致ではない。新しい7定理の日本語の量化・前提は `notes/design/2026-11-13-cycle167-settled-producer-promotion.md`。これで合計 **10module・76公開定理** となる。公開済みの69定理auditを変更せず、新しいpromotion audit/gateを追加した。

この追加により、固定observedの残る障害はproducer出力をTrustedに昇格できないことではなく、そのtargetを元capture source2へ対応づけるaliasにあると切り分けた。`notes/design/2026-11-13-unsettled-output-deferral.md` の「すべての正当なsource/settled説明をTrustedとして再構成することはimplementation coverage obligation」という未解決点に対応する。意味論を新しく選ぶ必要が確定したという主張ではなく、guardを弱めず監督役へ返す実装範囲の課題である。

追加のlean限定 `git diff --check` はexit0。全treeの同検査は原ログの末尾空白を表示する。正確なstdout保存と公開済みファイル不変を優先し、ログの空白は書き換えていない。

検証出力全文と終了コード: [own-diff](../verification/2026-11-13-cycle167-own-diff.txt)、[local replay](../verification/2026-11-13-cycle167-local-replay.txt)、[public replay](../verification/2026-11-13-cycle167-public-replay.txt)、[focused build](../verification/2026-11-13-cycle167-focused-build.txt)。

## 最終台帳

- 最終proof source公開: `4e96f96fa20d69c748178c001e23f055f7d86961`。local `d8673c622d` と心拍以外のtree一致を確認した。
- この公開commitを独立checkoutへ取得し直し、33moduleを独立出力libraryへ `--trust=0` で再構築、全Cycle167小auditを再実行してexit0。既存キャッシュがない上流依存を含む初回は34module、今回は再構築対象33moduleであり、検査を失敗した分を数から外したものではない。
- 主dependency gate177宣言、追加promotion gate14宣言、いずれも `propext / Classical.choice / Quot.sound` のみ。76公開定理すべてにaxiom登録があり、定理名の重複なし。新規production moduleにrun_cmd/unsafe等なし。
- 最終source差分は10module、入口import、13個の小audit。実行済みsourceとの唯一の後続Lean差分は、既に間接importされコンパイル済みの3moduleを入口に明示する3行の追記。証明moduleは変更していない。
- 最終append-only検査はremote refが後から進んでも再現できるよう、基点をSHAで固定して `bash tools/verify-lean.sh . 8d83c0c2690584834d0fd78e1915895e41e44f7e --no-build`、exit0。REVIEWは2件で、いずれも新規axiom gateの検査専用run_cmd。human-reviewフラグは保持する。
- 追加promotionのfocused buildは719 cache-inclusive jobs、exit0。small audit/正確な型の確認もexit0。独立レビューでfull descriptor readback、closed int recipe、Trusted outputとsource2不準備の整合を確認した。
- 最終検証全文: [final public replay](../verification/2026-11-13-cycle167-final-public-replay.txt)、[final diff](../verification/2026-11-13-cycle167-final-own-diff.txt)、[promotion](../verification/2026-11-13-cycle167-promotion-build.txt)、[source manifest](../verification/2026-11-13-cycle167-source-manifest.json)。全repo build/巨大audit/新Yulang2実行は行っていない。

### 終了時の上流再照会

15:09 UTC頃の再取得でintegrationは `47da90ca0483d773ec9f08efd95d4afb5c1aeb75` に進んだ。inboxの変更はなくACTIVE、STOPなし。追加はAstraのrecursive nominal peeling関連6module・audit・設計ノートで、現在のcycle167 sourceとは別の仕事。新ノートを読み、有限深さの `Display (list^n int)` を含むactual-inspectionのaccessibilityであり、一般ClassPProducerの完成ではないことを確認した。

今回の検証済み成果は開始時8d83c0c基点のまま公開し、締切前に未検証の統合を混ぜていない。次サイクルは47da90ca以降を取得して取り込む。integrationやAstraの作業を上書きしていない。移動したremote refを使ったmanifest作成が、未取込上流ファイルを見つけられず一度失敗したが、開始時SHAに固定して再生成済み。

最終公開差分は開始時基点から50ファイル（心拍1を含み、前cycle166の記録3ファイルを保持）。実作業開始14:33 UTC、検証完了15:10 UTC頃。公開と照合を含む終了時刻・経過分は同じ最終commitのcompleted心拍に記録する。scheduled開始14:27:19から55分以内の15:22:19締切を優先し、追加の大きな作業は始めない。
