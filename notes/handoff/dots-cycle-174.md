# dots cycle 174: agreed Local, finite role certification, and refresh evidence

**B4Bridges 未証明: 一般 ground agreed boundary で pending policy は 3 / 14、complete policy は 4 / 14。B4 全体は未完成。**
この 11 / 14 と 10 / 14 は既存 Astra の構造フィールド・ground progress を含む合成値で、新規定理の数ではない。特定 registry の role-DAG 正確性を一般 whereAccessible の解消として数えない。

これはサイクルの作業記録。終了・最終公開の確定は末尾の完了記録を参照。

## 基準・復旧・担当

- 開始 2026-11-13 21:22:53 UTC。ユーザーの55分上限によるhard cutoffは22:17:53 UTC。
- `integration/m1-final` を新規取得: `52cab5b90a716a99dbc55e9413b311bf7179272f`。standing-orders/inboxを再読、ACTIVE、最新I-29。前cycle173のcompleted心拍・報告と稼働プロセスを確認し、並行writerなしで開始。
- I-29の中心つき表現はAstra担当。本サイクルは新しく統合されたActualAgreed Localを使い、Actual Stepを変更しない。`defer=true`は実装上の制限であり、欠けた共有証明を言語上のpending規則とはしない。
- fresh integrationの約2,800 Lean sourceを取得木のblob hashと照合し、不一致なし。前173の公開済み追記報告も保存。公開は `work/dots-main` のみ。
- 途中でintegrationが`8443fa7cb287f5e31dd50aa4a6220fbcd5552e33`へ進んだことを読取確認。inboxはI-29のまま。追加canonical-hole transport群は読取で次の橋を検討したが、当サイクルの検証基準へ途中混入させていない。次回は改めて最新を取得する。
- 初回checkpoint `8662be82f33375d2661ed7459cac0560c247b6a5`、checker接続`df8d9c9a7023fde5da835e509917eb28373663e5`、uniform certificate / refresh修復`5004e3b1715dce343ee141b9e4e4a1ed5f2694c3`。開始と時間心拍も公開。既存sourceと監査ファイルは凍結、追記以外の書換えなし。

## 成果: 量化子と前提を含む主張

完全な型は `notes/verification/cycle174/completion-theorem-types.md` に収録予定。以下の「完全性」は明示した断片・判断に限り、M1全言語の完全性ではない。

1. **Ground174【補助/終了性】**: 任意roles/policy/gap/Checked registry、InitialSource ∧ PointSource ∧ GroundRootsからactual Stepでreachableなstateに対し、旧ground executorの終状態を使って有限execution・halted・SaturationTotalを得る。新Localのfrontiersで診断する。子accessibilityがあればtreeExecution。停止は既存ground_progressから導き、未証明Progressを仮定しない。executorとfrontier選択は非計算的。
2. **Evidence174【健全性】**: 任意のactual SourceFormed state、安定したselected focus、各current Modelsについて、Availableのinstallable+完全actual PacketGuard分岐からcurrent Instance。recorded分岐はstored-context→currentのordinary Extensionを明示要求。全子Evidenceは同じcurrent modelで親Evidenceへ合成する。pending policyではpolicy条件は自明、complete policyにはGapFreeを残す。
3. **Evidence174のordinary履歴【健全性/補助】**: enqueue/equate/fullguard install/mergeという実actual規則だけからなるOrdinaryAt/Stepを定義。edgeにExtensionやEvidenceを仮定せず、空journalのInitialSourceからの有限履歴でRecordedExtensionsを構築。任意深さの分類辞書を同じcurrent modelのEvidenceへ移す。descriptor refresh/reobserveを含む一般履歴や、選ばれたexecutorがこの履歴に属すことは示していない。
4. **Edge174【補助】**: 任意registryで全declared where-clause role辺をstrictに減らすRoleStratified rankがあれば、任意stateのagreed selected-child辺は実emit clauseに対応してrole rankが減り、whereAccessible。モデル/readback/所望のAccは前提にしない。same-role構造再帰はこの断片の外。これは新しい言語の拒否規則ではない。
5. **Exact174/Checked174【診断の健全性・完全性】**: 任意Checked registry、RoleStratifiedまたは成功したchecker、ground reachable state、任意treeに対し、executorの診断treeとの等式 iff 同じ最終状態のagreed LocalによるResolves。Completed iff Classifyも証明。未完成の子を含むtreeがありうるので、成功辞書の全域性ではない。I-29の将来の中心表現に対する定理でもない。
6. **Computed174【証明書探索の健全性・完全性】**: 任意有限registryとfuelで、実際の宣言role辺からtruncated heightを計算し、全辺を検査。check=true iff computed rankがRoleStratified。任意の既存rankは十分fuelでの安定化・完全性の証明にだけ使い、実行入力には使わない。∃fuelで成功 iff ∃RoleStratified rank。
7. **SearchOrder174【補助/探索順序独立】**: 任意の既存Reorders（宣言とwhere列の並び替え）に対し、全fuel・全roleのcomputedHeight、同fuel check、rankBudgetが一致。異なる終状態間のcanonicalLocalOrderを証明したのではない。
8. **Uniform174【証明書探索の完全性/診断】**: 親子roleをすべて列挙した有限roleNodesの長さをfuelに固定。任意の既存rankを「それより低い列要素数」に圧縮して、certify=true iff ∃RoleStratified rankを証明。呼出側のrank/fuel不要。成功時は上のground診断exactnessへ接続し、同じ固定stateのselected-child経路長はroleNodes.length以下。これは飽和Step数、tree幅、実行時間の上限ではない。certifyは実行可能だが全コンパイラは非計算的要素を残す。
9. **RoleExamples174等【回帰】**: checkedな非leaf wrapOnlyはfuel0で失敗・fuel1で成功、uniform certifyでも成功。checkedなdisplayのsame-role再帰は全fuelで失敗。どちらも一般certificate定理の特殊例。wrapOnlyには子roleのimplがなく、子辞書成功例ではない。falseはfuel不足/断片外を含み、言語拒否の意味を与えない。
10. **HistoryObstruction174【十分条件の障壁】**: ordinary ExtensionはKnownとPointIndexを双方向に保存する。任意の非空packet journalでRecordedExtensionsが前に成立し、refreshが新たなKnownを作る、またはreobserveがImprovesを満たすなら、後のRecordedExtensionsは不成立。reachableなそのようなstepの存在は主張しない。Evidence/B4の反例ではなく、強いhistory十分条件の限界。
11. **Refresh174【健全性の修復】**: 任意actual formed state、recorded packet、前だけのordinary Extension、fixed carrier/viewのRefresh証明書、任意の後journal modelに対し、同じモデル・同じroot/key/ordered childrenのcurrent Instance。後contextの全子Evidenceから親Evidence。InitialSourceのordinary actual有限履歴の後に、実際のKnown改善条件を持つ一回のrefreshを接続し、actual全履歴とEvidenceを同時に得る。後のExtensionは要求しない。繰返し一般refresh/reobserve・辞書完成は未完。
12. **Bounded174【外側診断の有限再帰】**: Protocol上でNat構造再帰するrunFuelを定義。全辺rank下降とrank(root)<fuelなら全ordered childrenのResolves。certify成功ならroleNodes.length+1で足り、Checked/ground Reachableから既存executorの最終診断と一致。手動rank/Acc/fuelを結論の利用側へ要求しない。0 fuelのplaceholderに言語のpending意味を与えず、証明された十分fuelの場合だけ正確性を主張。finalState/frontiersの非計算性は解消していない。

**Composition174は条件付き合成のみ。** Remaining.policy/history/whereAccessible/canonicalLocalOrderを残す。historyとGapFreeはgroundだけより広い一般agreed到達状態・需要を量化する十分条件で、最弱の必要条件と主張しない。historyには上記障壁がある。条件付きStatementをB4完成と数えない。

## V5の14フィールド（一般ground agreed boundary）

|フィールド|pending policy|complete policy|
|---|---|---|
|progress|既存ground_progressで証明|同左|
|execution|新ground executorで証明|同左|
|halted|同上|同左|
|closure|既存ActualAgreedから使用|同左|
|stepModels|既存から使用|同左|
|frontierLocal|既存から使用|同左|
|localIdentity|既存から使用|同左|
|whereAccessible|一般は未証明。role-DAGだけのper-registry定理|同左|
|treeExecution|当該field型のAcc前提で証明|同左|
|canonicalLocalOrder|未証明|未証明|
|dictionaryRefl|既存から使用|同左|
|evidenceNode|history条件付き、未証明のまま|history/GapFree条件付き、未証明のまま|
|generatedChildren|無条件に証明|GapFree条件付き、未証明のまま|
|initialReorders|ground初期制限で証明|同左|

## SourceBoundary 13項目

「一般の定義あり」はnominal carrier上の定義の有無で、全構文・全sourceの網羅完了ではない。

|項目|状態|
|---|---|
|Checked|一般の定義あり。既存宣言checking、role-DAGは別の任意断片certificate|
|Models|一般の定義あり。current ordinary stateとjournal|
|Step|一般の定義あり。actual-inspection Step不変更、一般非ground終了は未完|
|Stable|一般の定義あり。actual不可進行性|
|Generated|一般の定義あり。共有生成関係|
|RootPending|一般の定義あり。既存fieldsを使用|
|RootK2|一般の定義あり。既存actual/graph検査|
|CandidateK2|一般の定義あり。ActualAgreedのInspectedCycleを含む|
|InspectionPending|一般の定義あり。policy-parametric operational agreement。言語意味とは区別|
|Survivor|一般の定義あり。既存recursive候補|
|Evidence|一般の定義あり。current model健全性の一般bridgeは残る|
|Reorders|一般の定義あり。registry/where列並び替え|
|DictionaryEquivalent|一般の定義あり。最終出力の順序独立は未証明|

Initialはground executorでInitialSource ∧ PointSource ∧ GroundRootsに制限。定義を勝手に弱めていない。

## 検証・制限

- Lean4.35.0、各新source/auditに `lean -j1 --trust=0`。初回closure787/rebuild2、6source union870/8、8source union872/10、12source unionは下のログ参照。cacheのsource bytesを前サイクルと比較して変更/transitive dependentだけを再構築するfocused方式。clean全体buildではない。
- 全体 `lake build` と `tools/verify-lean.sh` は常設の禁止に従い未実行。全体PASS/CI成功は主張しない。監督役の全体検証が必要。
- 公理gateは新moduleの全namespace宣言の推移依存を検査し、propext/Classical.choice/Quot.soundだけを許可。定義や自動生成宣言を含む数を定理本数とはしない。
- 最初の試行ではnoncomputable abbrev、Result名前解決、tree_classifiesのimplicit引数、ordinary context同一性、mutual recursion、型表示optionを修正。失敗ログと修正版成功ログを分けて保存する。後から消して最初から通った扱いにしない。
- 既存Audit.lean、README.md、lakefile、spec、planは不変更。新moduleはYulang.leanへimport追記し、独立した小型Auditへ登録。
- Yulang2: work/dots-auditの公開x-oracleをfresh readしX1/C3-PARENTを参照。今回のActualAgreed/certificate/refreshを新しいYulang2実機で照合したとは主張しない。旧oracleは意味の証明の代用ではない。
- 意味論の新判断なし、質問ノートなし。使用量枠は不明。終了時diskは完了記録へ。開始時容量の正確な値はこの報告には未記録。

## 次の1〜3橋

1. **current-context historical Instance producer**: arbitrary actual refresh/reobserveへ、ordinary Extensionより弱い有限report/child-emission transportを構築。単回fixed-view修復は上記で実装。history全域条件をそのまま証明しようとしない。
2. **current Localの共通readback/rank**: role-DAG外のsame-role構造再帰へ。historical journal presentationだけではcurrent Localの全selected辺を覆わない。Availableのinstallable分岐と新しいcompatible presentation producer/coverageが必要。新canonical-hole noteの∃共通labels∀modelsを、各packet/modelごとの別label選択に弱めない。詳細は `cycle174-current-local-readback-bridge.md`。
3. **canonicalLocalOrder**: 同じregistryの列挙certificateが一致しても、別々の飽和終状態のLocal一致は残る。source coverage・I-29中心Stepへの移植はAstraの指示/統合を待つ。

## 追加: 繰返しrefining refresh履歴も構築

**RefiningTrace174【健全性】**: 任意InitialSource・空journalから、actual ordinary規則（新installを含む）と実際にKnownを改善するfixed-carrier/fixed-view refreshを任意回数混在させた有限履歴について、全recorded packet・全current Modelsでcurrent Instanceが成立することを帰納証明。edge guardにInstance/Evidenceを入れていない。過去packetは同じ最終モデルでtransport、新install packetはactual SourceFormedとprivate-context extensionから構築する。終点のpolicy＋actual Stable＋agreed Local selectedからcurrent Instance/親Evidenceまで得る。後状態のRecordedExtensions不要。上の単回部分から前進したが、任意のdescriptor reobserve/carrier-view-changing refreshや、選択executorがこの部分関係を走ることは未証明。したがって一般B4の計数は変わらない。

## 検証確定（最終公開前）

14新規source modules、19小型audit files、153 named declarations（定義等を含む）、125 named theorems。これを一般言語定理125本とは数えない。最終focused unionは878 dependency closure / 16 rebuild、exit 0。全19audit exit 0、completion namespace gateは243 declarationsで許容3公理のみ。全型表示もexit 0、import漏れ・禁止tokenなし。全体build未実行。

Scope独立レビューでも重大問題なし。特にRefiningTraceは終状態modelを後→前に運んで同じmodelの帰納仮定を使う。modelの存在自体は保証せず、親Evidenceには全子Evidence、selected endpointにはStable/policyが残る。今回、主型性の新しい一般定理はない。

基準52cab5に既存のファイルで変わったのはYulang.lean、design INDEX、前173の公開済み追記report/design、およびheartbeatだけ。4つの非heartbeat既存ファイルについて基準内容がbyte-prefixで保存されることを再取得で確認。frozen proof/Audit/README/spec/plan/lakefileに不一致なし。公開済み173の追記は回収であり、本サイクルの新成果ではない。

## T7b: 主入口からの依存到達性（読取のみ）

`tools/ReachCycle174.lean`を新設し、型とopaque proof bodyの両方を辿った。条件付きB4、certified diagnostic、certificate完全性/順序、refining履歴Evidence、history障壁の5 root群を別々に検査し、すべてexit 0。module由来261宣言（private/generated含む）の到達表と正確なrootsは `notes/verification/cycle174/reach/README.md`。namespace公理gate243とは集計対象が異なる。

未到達を不要と判定せず、削除・整理変更はしていない。特にconditional B4の依存閉包が通ることはRemainingのproducerがある証明ではなく、診断correctnessからcertificate完全性が未到達でも完全性の定理が無用という意味ではない。RoleExamplesは回帰testとして分離される。

## 実行可能certificateの性能制限

proofとは別に `tools/BenchCycle174.lean` でsynthetic role graphを実行した。これはCheckedなソース言語プログラムの例ではない。長さ4/8/12のchain（重複辺あり・なし）の6例はcertify=true、exit0。重複辺ありの単回粗測定は0/7/148 msだった。一方、長さ20まで含む拡大batchは60秒上限、別batchは45秒上限でtimeout(exit124)。途中stdoutがbufferされていたため、未完の個別caseの時刻は推測しない。

したがって「実行可能」を「実用速度」とはしない。現在のheight計算は同じsubtreeを再計算し、memo化等は未実装。性能検査の最初のIO/BaseIO推論エラーも保存し、修正版の成功/拡大timeoutと区別した。証明ソース14本と公理監査のPASSには変更なし。詳細・実行入力・失敗ログは `notes/verification/cycle174/performance/`。

## 完了記録

完了処理開始: 2026-11-13T22:13:06Z（開始から50.2分）。55分hard cutoff 22:17:53 UTC以内に公開・再取得照合・報告まで完了する。証明・小型監査・型表示・到達性検査は終了、稼働Lean/benchmark processなし。source14本は最終検証からbyte変更なし、各importは1回。ローカル保存commitはd94626814f（この完了記録直前）。終了時空き容量36 GiB。

途中成果・性能制限までの633a1f848bb86d680e7e50e5c3024a933e468ff8では、基準52cab5に対する111差分ファイルを再取得treeと照合し不一致0。最終はこの報告・completed心拍・publication-manifest.tsvを公開する。基準との差分総数は112（manifest自身を含む、新規107・既存5）。manifestには自身以外111ファイルのGit blob SHAを記録し、最終公開後にも再取得して照合する。最終commit SHAとその照合結果は会話へ報告する。

一般B4はpending policy3/14、complete policy4/14未証明のまま。全体build/CIは未検証、拡大性能batchはtimeout。未公開の証明ソースなし。writerは最終照合後に解放し、次サイクルまで新作業を行わない。
