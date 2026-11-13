# dots cycle168 — ソースを保つ観察更新と現在の辞書証拠

開始2026-11-13 15:30 UTC。ユーザーの55分上限を優先し、16:22:19 UTCまでに公開・報告する。前167のcompleted心拍と公開報告を確認し、並行するwriterは開始しなかった。

## 復元と基点

`integration/m1-final` を取得し直し、常設指示・inbox I27まで・公開167報告を再読した。検証基点は `11be97cb1d76080ec7b72cccde0a5402c6835783`。先頭のAstra compound/spine変更を統合し、競合した `Yulang.lean` は両側のimportを保持した。前167の終盤の追加も保持。15:53の再取得でもintegrationは同じ、inboxはACTIVE。公開先は `work/dots-main` のみ。

## 検証した内容と正確な前提

1. **一般的なreport移送** (`GeneralDictionarySource168Transport`、3定理): 任意の旧・新context、ソースslot写像、宣言、引数boundsについて、ソース識別子とseedの保存、実際に計算したreportの移送一致、生成schemaの一致を仮定する。旧BranchModelsと新状態のModelsから新BranchModelsを導き、同じ子の現在Evidenceからnode Evidenceを構築する。新BranchModelsや親Evidenceを前提に置かない。
2. **実際のscalar refresh** (`GeneralDictionaryActual168Transport`、5定理): captured producerについて上の構造的一致を独立に証明し、実際の観察後journalを満たす任意のモデルで現在のproducer Evidenceを再構築する。既存current_evidenceの引用ではない。
3. **同じ有限証拠木全体の移送** (`GeneralDictionaryRecursive168Transport`、4定理、2定義): 旧木の各節点に現れる可視・同じkeyの宣言だけについて、現在の引数/report/schemaの対応を要求する。ソースとseedの保存から子の識別子の一致を導き、木の帰納法で同じ木・payloadを新contextへ移す。新Models/Metadataは明示的な前提。任意のrefreshで成立するとは主張しない。
4. **実際の木での適用** (`GeneralDictionaryCapturedTree168Transport`、6定理): 旧Preparedと実際のjournalから旧Instance/木を構築し、非恒等のscalar refresh後へ一般再帰定理を適用した。新しい非終端consumer木ではなく、terminal producerの木である。
5. **Shared journalからの一般的な解釈** (`GeneralDictionaryRecorded168Relocation`、6定理): SourceFormedと記録済みpacketから、旧Instanceを既存の履歴定理で得る。新しい `RelocatedTree` は有限の記録木と、その木が使うpacketだけの構造的移送条件を持つ。これから任意の現在モデルのEvidenceを導く。旧来の「全packetがordinary extension」の条件に限定せず、無関係な記録packetの移送も要求しない。木の存在や移送条件そのものは一般には未証明。
6. **実journalの非空な適用** (`GeneralDictionaryCapturedJournal168`、4定理): 実際のSourceFormed、記録membership、terminal childrenからRelocatedTreeを作り、current Evidenceを解釈した。旧/新Evidenceを仮定せず、実モデルの存在も示した。
7. **信頼された入力の保存** (`GeneralDictionary168SourceGuard`、10定理): 任意の実際のShared OrdinaryStep列についてReadyAtとDecisionGuardを保存する。再帰的な検査read集合の一致を証明し、既存Evidence保存と組み合わせた。既存source-supported container consumerはguard付き・SourceFormed・非空で、ordinary継続上も同じpayloadを保つ。descriptor refreshと任意継続のモデル存在は対象外。初期traceやその辞書自体を今回新しく証明したとは数えない。

8. **旧ordinary解釈との接続** (`GeneralDictionaryOrdinary168Relocation`、3定理): ordinary extensionからソース/seed保存と計算report/schema一致を導き、新しいRelocates条件を証明した。新解釈が従来のordinary-only解釈を含むことを、意味的Evidenceを仮定せず示した。
9. **記録nodeと未記録source leafの混合** (`GeneralDictionaryMixed168Tree`、2定理): 新しい有限MixedTreeは、移送可能な記録nodeと、現在のsyntax/stateだけで示すscalar/spine leafを混ぜられる。SourceFormedと現在Modelsから全木のEvidenceを帰納的に導く。leafのInstance/BranchModels/Evidenceを前提にしない。これは十分な証明書の構文で、新しいclassifierや実行規則ではない。
10. **混合coverageの真の拡張** (`GeneralDictionaryMixed168Display`、5定理): 実際のShared Display→Int状態でMixedTreeを構築し、同じ状態にはRecordedTreeがないことを既存の否定定理と接続した。一般の新解釈から非空なcurrent dictionaryを得る。Display辞書そのものは以前から証明済みで、今回の新しさは混合した構造的証明書と一般解釈への接続である。

今回のproduction追加は **10module・48公開定理**。全新moduleをYulang.leanからimportし、既存production/監査行は変更していない。

## 13境界とV5

| 境界 | 状態 |
|---|---|
| Checked | 一般nominal定義あり、変更なし |
| Models | 一般定義あり。現在journalモデルとsource-supportedな非空例を使用 |
| Step | 一般Shared定義あり。既存traceのみ使用、規則変更なし |
| Stable | 一般定義あり。今回の一般安定化・完了は未証明 |
| Generated | 一般定義あり、既存SourceFormed履歴を使用 |
| RootPending | 一般定義あり、変更なし |
| RootK2 | 一般定義あり、変更なし |
| CandidateK2 | 一般定義あり、変更なし |
| InspectionPending | 一般nominal定義あり、全Shared統合未完 |
| Survivor | 一般nominal定義あり、変更なし |
| Evidence | 一般定義あり。現在contextへの構造的移送とjournal解釈を拡張 |
| Reorders | 一般nominal定義あり、変更なし |
| DictionaryEquivalent | 一般nominal定義あり、変更なし |

V5は **未証明8/14** のまま。全Shared `evidenceNode`、Stableからの有限木・移送条件、完全性・主型性・言語全体の網羅性は未完。I26のguardを弱めず、前167の固定captured consumerの保留を解消したとも主張しない。Step/Stable/Generated/意味論は変更していない。

## 検証と制限

- focused `lake build --wfail`: 初期691/721jobs、再帰739jobs、journal742jobs、すべてexit0。後半は `--rehash` でソースhashも確認。job数はキャッシュを含む。
- 全repo build・巨大Audit.leanは実行していない。新しい小auditのみ。公理はpropext/Classical.choice/Quot.soundだけ。
- 初期公開 `b24a3ffe077b49ad6045a86e9091ed082825acc6` を別worktreeへ取り直し、3moduleを独立出力先へtrust0で再コンパイルし、全小audit・39宣言gate・基点からのappend-only検査に成功。継承依存のoleanはfocused build済みcacheを使い、全依存をゼロから再構築したとは主張しない。
- 具体例の最初のelaborationは4回exit137。seedの `rfl` 展開を既存の明示的packet_seed補題へ替えると成功した。途中のparser/binderエラーも修正済み。
- 1回、実行サーバー切断でコマンド開始に失敗。状態を読み直して未実行を確認し再試行した。
- public gateの `run_cmd` は依存公理・型を読み取る監査専用。production定理を生成しない。diff検査のREVIEW表示は末尾台帳に記録する。
- 読取専用の独立レビューで、移送前提の範囲、旧・新context、guardを弱めていないこと、非空虚性、既存結果を新結果として数えていないことを確認した。

## Yulang2との比較

`work/dots-audit` を再取得して `55574b6052ef1534fd0fc36d6d3617ebede59a0e` のままと確認。前167の比較記録を再読した。旧parent Left/Rightの実行記録と今回のShared Trusted/relocationの同値は未証明。旧runtime binaryは使用しておらず、新しいYulang2実行結果はない。旧実装に合わせたspec変更もしない。

## 次の仕事

1. 一般の到達可能状態・安定状態から、現在のinspectionとhistorical packetを結ぶ構造的移送条件を導く。
2. 新しいMixedTreeの存在をShared V5の選択/完了条件から導く。構造的証明書の解釈だけではこの存在は得られない。
3. captured consumerのrouting alias問題は、SourceFormedとTrusted sliceを区別したまま扱う。terminal producerの成功をconsumerの再開と取り違えない。

次の形式的な接続義務は `notes/design/2026-11-13-cycle168-v5-coverage-obligations.md` に分解した。MixedTreeの存在をV5へ仮定追加して解決扱いにしない。

## 最終台帳

- productionソース公開: `1004e5ff661d8b2ded5010c0ba31fb31226120d0`。
- ローカルと公開済みcommitの全tree SHAは `9f81c695f4aa1ec18ea9099653a6c322106ad92a` で一致。
- ソースmanifestの10module・48公開定理と、公開済み10blobを個別照合して一致。
- 最終focused build: `lake --rehash build --wfail` 対象792jobs、exit0。48定理のprint監査と、private/generatedを含む計120宣言の5gate（39+14+7+28+32）に成功。
- 実際のscalar refresh自体がordinary extensionではないことは、既存の `GeneralDictionaryCapturedScalarRefresh.not_ordinary_extension` が示す（privateContext→scalarContext）。今回のhistorical packet→current journal解釈はordinary extensionを仮定せず、構造的report/schema一致を使う。
- 公開済みソースを別worktreeから10moduleすべて新しい出力libraryへ `lean -j1 --trust=0` で再コンパイル。13小auditを再実行し、48公開定理・120宣言の5gateすべてPASS、exit0。
- `bash tools/verify-lean.sh . 11be97cb1d76080ec7b72cccde0a5402c6835783 --no-build`: 公開commit上でPASS、exit0。REVIEW7行は監査run_cmd6行（前167分1＋今回5）と、コメントの先頭語syntaxを検知した1行。productionメタプログラムの追加はない。人手確認の表示を無かったことにはしない。
- 48定理すべてのprint監査coverageを照合し、missing0/extra0。manifest・coverage・公開再実行・diffログをnotes/verificationに保存。
- 15:57心拍までに検証した全ソースを公開し、16:03に最終公開再実行が完了。全compiler/worker終了済み。最終報告とcompleted心拍はこの台帳を含むnotes-only commitで公開する。
- 55分上限内。承認待ち・未公開production変更なし。自動化の停止や設定変更は行っていない。
