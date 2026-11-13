# dot cycle166 — captured producer の実際の導入と scalar refresh

## 起動・範囲

2026-11-13 13:27:19 UTC の起動。実作業開始13:32 UTC、最新ユーザー指示による締切14:22:19 UTC。文書の長時間継続指定より55分上限を優先する。前回165は `63aab710204c91396e4957a8e52fc58778171b85`、心拍completed・報告あり、稼働中の前writerなし。公開先は `work/dots-main` のみ。

`integration/m1-final` を取得し直して `0c682814d7642e4e6adff828341b164a46da0321` を統合。standing-orders、inbox、前回報告・次の設計を再読した。inboxはACTIVE、I-26を維持し、終了前の再照会でもblob `466fa189c71441df601f03a6139c309b385b42f2`。Astra所有のStep/終了性/guardの定義は変更せず使用した。入口importの統合競合は監督版を基準に未収録importだけ追加した。

## 主成果と前提

**実際のcaptured producer導入までの3操作とscalar観測までの4操作を、非空モデルを持つShared traceとして構成した。consumerのI26信頼readiness・実際の導入は未証明。**

### 準備・選択・novelty〔具体例の補助と健全性〕

`GeneralDictionarySharedCapturedPreparation` は具体的なrefresh後状態について、任意invocationのFresh、linkage、Prepared、Survivorを証明する。`...ProducerEnabled` は同じ実際のjournalでK2不在、候補宣言の一意性、site/alias/既存packetの整合、Joint、merge closureを証明してInstallableを得る。選択結論を仮定に置き換えていない。

`...Novelty.not_committed` は末端が `str` の具体的モデルで、現在の親journalは満たすがproducerのint出力は満たさないことを示す。これは非空の本物の反例であり、全モデルがstrであるという主張ではない。この反例により「既にCommittedかもしれない」という条件を解消した。

### guard・実際の導入・現文脈Evidence〔健全性〕

`...ProducerGuard` は親の**入力**factを用いてslot3/4の読み取りを説明し、旧guardとShared DecisionGuardを接続する。未settled親出力をreadinessの根拠に使わない。葉なのでgeneration/coherenceも具体的に証明した。

`...ProducerResolution` の導入stepはnoveltyを明示した補助定理であり、`...Resumption.producer_step` が実際のnovelty証明を渡して無条件の具体的stepにする。全導入後モデルについてsource2≃int、かつ具体モデルの存在を証明する。

`...ProducerEvidence.current_evidence` は**導入直後のprivate現context**とその任意のModelsを量化し、producerの葉辞書 `node declaration.id []` のEvidenceを構成する。保存時contextとの同一視ではない。scalar refresh後の現contextへの輸送はこの定理には含まれない。

### scalar refreshと残るI26境界〔条件付き補助を実際のtraceに適用〕

`GeneralDictionaryCapturedScalarRefresh` は任意のcurrent状態について、context=candidate.privateContextと「全現モデルでsource2≃int」を前提に、全assignmentで更新前後Modelsが同値となるrefreshを作る。source2が新たにKnownになり、consumerのraw RootPendingが解消する。inspection不変のordinary Extensionではないことも証明する。

`...Resumption` は上記前提を実際のproducer導入で満たし、初期source→親install→fresh-slot refresh→producer install→scalar refreshという4操作、SourceFormed、モデル存在、packet保持、全現モデルでのscalar帰結を証明した。

`GeneralDictionaryCapturedTrustedBoundary.ready_from_trusted_alias` は、Trusted facts/readbacks、その中のproducer出力fact、**その同じtrusted sliceの全モデルでtarget≃source2**という独立前提のもとでShared ReadyAtを得る十分条件。全journal Modelsで成り立つ等式をtrusted sliceへ無断で輸入していない。親出力は等式を供給するが、`parent_settlement_requires_consumer` により親settlement自体がconsumer dischargeを要求する。これは依存関係の証明であり不可能性定理ではない。consumerの信頼readinessや完全辞書木を完成扱いしない。

`...CapturedConsequences` は任意Shared経路の逆向きModels保持、記録済みproducerと実際の経路からのscalar帰結、その後続経路での保持を証明する。記録・到達前提は明示した。

## 受入れ条件・13境界

I-21のEvidenceレーンで、具体的captured producerを本当に導入し、その現文脈Evidenceまで進めた。I-23/I-25の初期・到達可能性を明示し、到達不能なraw stateの例に置き換えない。I-26で保留のconsumerに辞書を与えない。

| 境界 | 状態 |
|---|---|
| Checked | 定義不変、既存checked宣言を使用 |
| Models | 定義不変、str反例・intモデル・refresh iffを追加 |
| Step | 定義不変、具体的4操作のShared経路 |
| Stable | 定義不変、一般の安定化・完了未証明 |
| Generated | 定義不変、実際の親からproducerを追跡 |
| RootPending | 定義不変、consumerのraw否定と信頼guardを区別 |
| RootK2 | 定義不変、具体producerで不在を証明 |
| CandidateK2 | 定義不変、具体producerで不在を証明 |
| InspectionPending | 定義不変、全Shared統合未完 |
| Survivor | 定義不変、具体producerの準備を追加 |
| Evidence | producer導入直後の現文脈に葉Evidence |
| Reorders | 定義不変 |
| DictionaryEquivalent | 定義不変 |

V5の継承した会計は **8/14、未完** のまま。全Shared境界のevidenceNode、一般のsource-to-Evidence、完全性・主型性・canonical結果を今回証明したとは言わない。

## Yulang2照合

監査branchを再取得し `55574b6052ef1534fd0fc36d6d3617ebede59a0e` を読んだ。最新cycle5、role-boundaries、casts-roles、x2-demand-boundary、role-system資料を確認。Y2-ROLE-003のassociated更新/再展開は文書上の対応であり一般saturation完了を実機確認した主張ではない。ROLE-006のordinary knownness比較も未確認。既存where/body需要試験は今回のtrusted aliasを確立しない。記録された実機binaryは利用できず、新しいYulang2実行はしていない。過去の試験revisionは `d4c8bc8fc8a49173180932cd25921a2c41057354`。

## 検証と公開

- 開始心拍 `5bd10abffa956741458eeb3003826757dbe09a4e`。
- 途中公開 `8d87dee4a54f8e88192fbbc60791078e69bc8ce7` は最新integrationを第二親に含む。
- source公開 `b4ca7904590a46793d6bc2e2f829e999848d7eab` と凍結local `b6a32fbf4977989644f17c84a3ce1d131be945b6` の全tree一致（心拍以外）を確認。
- 焦点を絞ったlake buildのみ。upstream714、準備/refresh706、最終組合せ715 cache-inclusive jobs、すべてexit0。全repo buildや巨大Audit.leanは実行していない。
- 第2公開時点の新規10module、84public theoremの型を索引化。新しい依存gateはprivate/generatedを含め185宣言、標準 `propext / Classical.choice / Quot.sound` のみ。run_cmdは検査だけのauditコードでありproductionではない。
- 個別コンパイル中、sourceファイルへの出力先の階層を誤った操作はファイル未作成で失敗し、正しい場所で再実行した。Resumptionのpacket所属でappendとconsを取り違えた証明を修正。unused simp警告は引数を除去して直し、最終--wfail成功。
- 最初のtree作成は入口の末尾改行を転送時に変えてしまいblob SHA不一致で422になった。元ファイルの正確なbytesを再送し、treeを再作成して一致確認。誤ったtreeは公開していない。
- diff-only gateで新規docstringの英単語admitをtacticと誤検知。意味を変えずhaveへ修正。上流integration基準では、前回165から既に公開されていたaudit追加とInstallableのlint修正がappend-only検査に抵触する。今回の新規変更とは分け、既存証明や監査範囲を戻さず維持した。今回の統合時点db221e731を基準とする検査結果と、上流基準の失敗全文を両方保存する。
- GitHub workflow照会はsource commitのPR-triggered・first-page結果が空。全CIの成功や全workflow不在とは言わない。
- 公開後の別checkout・独立出力libraryでのtrust0再実行、最終readbackは下記最終台帳へ追記する。

## 次の仕事・制限

1. `GeneralDictionaryCapturedTrustedBoundary.ready_from_trusted_alias` の独立trusted aliasを、既存I26のsourceまたはsettled入力根拠で導ける範囲を明確にする。未settled親出力を使う循環を隠さない。
2. scalar-changing refresh後の現文脈Evidenceを再構成する。ordinary Extensionではないので前回の一般輸送をそのまま使わない。
3. consumerが実際にguardを満たす別のsource-supported具体例から、非終端親の有限辞書木を構成する。一般V5は別途残る。

意味論の新しい判断は行っていない。質問待ちを作らず、既存I26遅延指示に従う。使用量枠は不明。自動化の停止・設定変更は行っていない。

### 最終contextでの限定した追加

`GeneralDictionarySharedCapturedFinalProducer` により、scalarContextで再構成したproducer packetの正確なreport、Finished、二重capture bindingsを証明した。新規総数は11module・87public theorem。これは検査の再構成だけで、最終contextのBranchModels/Evidenceではない。後者の依存型を広いsimpで正規化する実験2回はメモリ制約で停止した。失敗コードは公開せず、定義を弱めたり、新しい仮定で完成扱いしたりしない。各定理の日本語の量化・前提を3本の `cycle166-*-theorems.md` に記載した。

## 最終source・再実行台帳

最終source公開 `24d07fe6408f0214f5ecb29989cb91ff4e75e714`、local `264527ffdc0a29a6914bc9beac271baa6c4b1d2d`。公開commitを再取得し、心拍を除く全tree一致とintegrationの祖先関係を確認した。変更Lean39ファイル全てのbytes/git blob/SHA256を公開checkoutと照合し一致。manifestは `notes/verification/2026-11-13-cycle166-source-manifest.json`。

14:04 UTC、公開最終sourceの **26変更module（今回11＋監督役統合15）をすべて別出力libraryでsourceから --trust=0 再コンパイル**し、全10個のCycle166 auditと監督役2auditを再実行、exit0。依存gateは **190宣言**、標準3公理のみ。87public theoremの型も出力成功。全文は `...-final-public-replay.txt`。最後のfocused buildは716 cache-inclusive jobs、exit0、`...-final-focused-build.txt`。

今回だけの変更を統合時点db221e731から検査したdiff-only gateはPASS（audit-only run_cmdのREVIEW1件）。上流integration基準の継承差分による失敗も隠さず別ログを残した。本文記載の新規docstring誤検知は修正済みで、最終sourceには影響しない。全repo検証PASSは主張しない。

定理担当の書き込み・検証処理は終了。最終contextの検査結果だけは再構成できたが、BranchModels/Evidenceの輸送とconsumerのtrusted aliasは次回へ残す。終了心拍とartifact公開の最終hashは会話の報告に記す。

### 終了確認

14:09 UTC、artifact公開 `84372c0f9af683bd508394f2fbd338b3b4e910c7` を取得し、local `d5d8e8c425e937515ed0c9dc598feac7e3d9d999` と心拍以外の全tree一致を確認。manifestの39 Leanファイル全てと、87定理の日本語索引の収録を再検査して成功した。前回165最終からの公開変更は心拍を含め58ファイル（監督役統合分を含む）。報告自体もGitHubから読戻した。

実作業開始から約37分、起動時刻から約42分で検証・公開・報告台帳まで完了。55分上限を優先し、残る大きなEvidence輸送実験を再開せず、証明済み部分・失敗・次の有限分解を残した。終了心拍をcompletedへ更新し、並行writerは残さない。
