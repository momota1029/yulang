# dots cycle152 — observed named outputs, real child, stable dictionary

一般V5 `B4Bridges`: **6/14供給、8/14未解決**。今回の具体例と条件付き定理を一般の `evidenceNode` 完成と数えない。

開始2026-11-12T23:27:19Z。55分上限2026-11-13T00:22:19Z。最終公開時刻はcompleted心拍。

## 復元
fresh integration/m1-final `dc145d71f`、standing ordersとinbox I25 ACTIVEを再読。STOPなし。前151のremote心拍completed、報告あり、writerなし。integrationをmergeし、importと設計INDEXの追加同士を保持した。spec・notes/plan・監督役定義は変更しない。I24のAudit.lean/README凍結を維持し、新規Audit/Cycle152.leanだけに監査を追加。

## 成果と主張の側
- **条件付き健全性**: 任意InitialSourceからのactual ordinary trace、Stable、生成された各選択需要のrecorded packetまたは明示的な構造coverage、任意current Models、有限Classifyを前提に、named scalar outputを許した全辞書のEvidenceを再帰的に証明。Jointは結論に相当する仮定へ戻さず構造から導く。各alias siteの同一宣言Shapeと実選択は依然明示前提。refresh/reobserveを含む一般traceへのcoverageは未証明。
- **補助**: source slotのscalar観測とrequest翻訳からなる独立certificateはordinary traceで双方向に保存。有限appendの分解と、VariableClausesによる実materialization requestへの適用を証明。fresh targetやnon-scalar観測をこの結果で扱ったとは言わない。
- **実正例・健全性**: List head、Display where-child、`out=Int`のnamed requestを保持。seed1により実InitialSourceを構成。scalar child宣言を加えたregistryで、実guarded install、Reachable、モデルの存在、全更新に対するStable、実2node Classify、全final ModelsでのEvidenceが同時に成立。root named-output requestは空でなくsingleton target1、where childも実canonical生成物。初期状態はnot Stableで、install後と区別する。
- **負の対照・補助**: scalar child宣言がない元のsingleton registryはそのまま残し、任意context/modelで実childのInstance/Evidenceがないと証明。親の選択・installを全木の成功と取り違えない。この対照はV5反例ではない。
- **必要条件・補助**: Related aliasの実selected keysが異なるならfocusへのInstallable packetは存在しない。この含意は、そんな状態のReachable/Stable/子Evidenceの構成ではない。行政更新やrefreshまで排除したとも言わない。

- **非scalarへの条件付き拡張・健全性**: 既存source slotに対応する有限closed nominal tree（nullary/unary/binary、内部point辺、scalar葉）の観測certificateから任意有限requestbatchのmaterialization Modelsを導く。すべてのprojection testの存在・全観測値のHoldsを示し、generated variables=[]とunknown=falseも別に証明する。free binder・row・fresh target・非point辺は対象外。実BranchModels/Instanceに接続し、同一モデルでalias Jointと有限辞書recursive coverageまで拡張。旧scalar coverageの包含も証明。List Intのrequestはnominal root testと投影scalar testの2つを保持し、旧scalar certificateではないこととモデルの存在を形式化。ただしこれはmaterialization正例で、scalar出力の完成例と同じReachable/Stableプログラムではない。

- **任意有限arity・健全性補助**: さらにFin nで全descriptor引数とquery/slotを対応させ、任意有限arityのclosed nominal requestについて全materialization Modelsを証明。旧binary certificateを埋め込む。これはmaterialization層の拡張で、branch/alias/recursive coverageの証明は前項のarity≤2 certificateのまま。

完全型と全定理名はtheorem index/types文書を参照。完全性・主型性・一般停止の新しい完成はない。

## 13境界項目と残る橋

|項目|状態|
|---|---|
|Checked|一般nominal宣言の定義あり。全言語忠実性は別義務|
|Models|一般定義あり|
|RootPending|一般定義あり|
|RootK2|一般定義あり|
|CandidateK2|一般定義あり|
|InspectionPending|一般定義あり|
|Survivor|一般nominal候補の定義あり|
|Reorders|一般定義あり|
|DictionaryEquivalent|一般定義あり|
|Step|一般定義あり。Astra担当、変更なし|
|Stable|一般定義あり。今回具体例を実証|
|Generated|一般定義あり|
|Evidence|一般定義あり。一般evidenceNode橋は未解決|

未解決8: progress、execution、halted、whereAccessible、treeExecution、canonicalLocalOrder、evidenceNode、generatedChildren。任意reachable stateに今回の構造coverageが成立することは仮定のまま。定義の存在と橋の証明を区別する。

## Yulang2との照合
work/dots-auditをfetchし、ROLE-MORE-003/004のwhere/body prerequisite差と関連oracleを確認。旧Y2が宣言whereを選別に使わない例から、新specのchild義務を消してはいない。このnamed-outputプログラム自体のY2実機は未実行。新しい意味論の判断はしていない。

## 公開・検証
初回checkpoint `8a6a66f014cfde4790696356e4400eb8d6d185b4`、tree `eb32a4ef80181b2d345ad53984f210ebf85a3806`全一致。
第2checkpoint `2079b46acb07409bb3a81b8f21bff889de9dbc2c`、tree `80925793007d2cd3c0f1aa8fc24a3e6071dc1302`全一致。
初回SHAのCore CI43330462874・Lean CI43330462819ともsuccess。以後のSHAのCIまで意味しない。
第3checkpoint `89fd8b230fa957d0282d14aca5919626fcac5d23`、tree `afce93d6203ec70d64131508b3f657ff05b93ad4`全一致。Core CI43332813810・Lean CI43332814133ともsuccess。

最終sourceは22modules・161公開定理。focused `lake build <22modules> --wfail` exit0、768jobs。`lake env lean --trust=0 Audit/Cycle152.lean` exit0。全宣言gateは436declarationsでexit0、許可依存はpropext/Classical.choice/Quot.soundのみ。完全型出力exit0。量化・前提の全文はtypes1〜8。独立read-onlyレビューもscalar完成例・closed/finite request全体に問題を検出せず。
最終source [`ed34179dfc8d1db50064335a6de3eccfbcba2ac8`](https://github.com/momota1029/yulang/commit/ed34179dfc8d1db50064335a6de3eccfbcba2ac8)、tree `174fbd8ac21f34c5b50606b2ce380c261d89d774`。remote取得後local全treeと一致、fresh integrationの祖先性もexit0。公開commitのclean worktreeでdiff-only gate再実行exit0。公開tree照合後のtrust0再監査exit0。

最終sourceのCore CI[43333773515](https://github.com/momota1029/yulang/actions/runs/43333773515) success。同一treeの直前source `8b1c61bf67fbf613b529d4191c4372196fc31a1e`ではCore[43333503050](https://github.com/momota1029/yulang/actions/runs/43333503050)・Lean[43333503280](https://github.com/momota1029/yulang/actions/runs/43333503280)ともsuccess。最終source自体のLean runは一覧にないため、そのSHAでのLean CI成功とは記さない。全体lake buildと全監査はstanding ordersに従いdotでは実行しない。

## 制限・修正
開始後の心拍で推定時刻23:37を記した誤りを実時計23:35のcheckpointで訂正し、以後dateから生成。初期に別ファイルを同一worktreeで分担したが、git-concurrency再読後ただちにisolated worktreeへ移し、親だけが統合・commit・公開。衝突や内容損失はない。差分verifyの初回は未commitのAudit/importを検出しFAIL、commit後に再実行PASS。第2checkpoint後の心拍更新は末尾改行差によるblob SHA409となり、remoteを再読して新SHAで同じ内容を更新した（成功）。最終公開監査でremote履歴がfresh integrationを祖先に含まないことを検出し、同一treeの非force merge-parent commit ed34179で修正、公開commit自身の祖先性とdiff gateを再検証PASS。全Lean証明にsorry/new axiom/native_decideなし。使用量枠は不明。

## 次の候補
1. 任意reachable stateでのalias selected-key整合を証明、またはdisjoint-output案の全反例義務を満たす。
2. 既存source観測にないfresh named target、free binder・row・非point辺のmaterialization証明。
3. ordinary-only制約を外すrefresh/reobserveのdictionary transportと構造coverage。

## 完了

最終文書・completed心拍を含む公開を最後に照合しwriterを解放する。全45files（integrationとの差分、Lean22modules＋imports＋audit＋設計/型/検証/報告/心拍）。cacheは既存未追跡物で公開対象外。新しい意味論の質問や承認待ちはない。証明追加は完了後に広げず、55分上限より前に検証・公開・報告まで終了。厳密な最終所要時間はcompleted心拍の値。
