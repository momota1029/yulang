# dot cycle144 — 実support再帰辞書の安定完了と有限readback

**一般V5未証明: 8 / 14本。** 本文は作業中記録。最終検証・所要時間は末尾に確定する。

## 復元と範囲

- scheduled 2026-11-12T15:27:19Z、実開始15:26:06Z。時刻は遡って丸めない。
- integration/m1-finalを新規fetchし `6cff680ccafc24ab298e1b890adcb6d7bba15034`、standing orders/inbox I25を再読。STOPなし。
- 前回143 completedと報告、公開head `9c58272b1f1844c9bf7cc6dcea4abee9dadcfbe8`、旧writer/buildなしを確認。
- userの55分上限優先、保守的終了期限16:21:06Z。途中公開・心拍は後掲。work/dots-main以外に公開していない。
- Astra所有の一般State/Step/Stable/Generated、凍結Audit.lean/README.md、spec/plan/configは不変更。

## 閉じた部分目標

### A. 実再帰例の分類・Stable・全モデル辞書・一歩終了形

cycle143の `SupportRecursiveExample.finish` は、List Intに対するDisplayの実source-supported parent installで到達する非空journalだった。今回その**同じ状態**で:

1. 現在contextでparentがkey1＋child1個、childがkey3＋child無しのLocal selected。初期sourceからのDecisionGuardを保ち、support boundaryのClassify/Resolvesを構成。
2. concrete modelが存在し、同じ `.node 1 [.node 3 []]` のsource Evidenceが**任意の最終journalモデル**で成立。
3. source≥2を個別に変える最終モデル族から、任意のcertified refreshが予約originをKnownにできない。PointClosedだけでこの結論を代用していない。
4. このfixtureのContextComplete、point-valued observations、sites=[parent,child]、edge=(parent,child)、generatedはこの2点だけ。List IntとIntの入力差からcross mergeを排除。
5. 任意generated点の任意installable packetは既にCommitted。refresh/equate/reobserve/enqueue/mergeも排除して、**実support Stable**。
6. parent/childのJointを、任意final modelでのcurrent BranchAtとalias/key事実から実証。leaf BranchAtはsource Instanceを普通制約extensionで直接運ぶ。既存Evidenceを逆向きに使う経路はreviewで除去した。
7. 初期状態の任意actual Stepはこのfinishになる。finishからStepは無い。任意finite traceの終点はstartかfinish、Stable終点 iff finish。これは固定fixtureの一歩終了形であり、一般Progress/canonical-orderでない。

`ContextComplete` は固定fixtureだけ。前回のactual reachableなContextComplete反例を取り消さない。terminal childの架空installは作っていない。

### B. 一般の有限readbackをClassifyなしで構成し、必要十分条件も証明

`SupportReadback`: 任意roles/registry/tracked state/rootで、actual Reachable＋Stable、全Generated点でLocal selected、選択点Joint、独立current Local ChildのAccから、一つの有限dictionaryを構成。Classify/Evidence/完成payloadを前提にせず、得た同じpayloadは全final modelsでEvidence。root Jointはモデル存在も与える。

`LocalReadback`: 任意B4 SourceBoundaryで、**selected-child closure**（独立Reach）の全点がLocal selected、ChildがAccならClassify selectedの有限辞書を構成。実行・Stable・Joint・モデルを使わない。全歴史Generated点の成功を要求する前述版より弱い局所条件。supportへのsemantic specializationは別にReachable/Stable/モデルありの場合のJointを要求し、こちらだけではモデル存在は保証しない。

`LocalReadbackExact`: 任意SourceBoundaryで

`∃ dictionary, Classify selected dictionary` iff
`selected-child closure全点Local selected ∧ Acc Child root`。

逆方向はUniqueから任意selected Localの子リストが分類済みリストと一致することを使い、隠れた別分岐を除外する。純分類の必要十分条件であって、実executor停止や一般whereAccessibleの証明ではない。

`SupportReadbackRegression`: Aの具体fixtureで全前提を証明してgeneric抽出へ接続。Accは2つのLocal形から直接構成し、既存Classifyを使わない。Classify/Evidenceが抽出出力となり、最後だけ独立分類の関数性でpayloadを正確に同定する。

### C. 非自明aliasを許す限定スケジュールと実merge例

`EarlyMergeChoices`: 任意registry/actual support traceに対し、merge時に少なくとも片側alias classが未記録ならCoherent（alias群の全packet key一致）を保存する。Scheduledはactual initial/admin/install/mergeだけで、mergeにこの純構造条件を加える。key一致、Current、singleton registry、alias空を前提にしていない。SourceFormedへの埋込、Coherent、記録focusのJointキー部分を導出。一般executorがこのスケジュールに従うとは未証明。同時semantic modelのJoint部分は別。

`EarlyMergeRegression`: 実install→certified reobserveのモデルあり非空journalでCoherentかつ¬Current。ここにはmergeは無く、administrative許容性の回帰としてのみ扱う。

`EarlyMergeBoundary`: actual reachableでpacket-freeならsite1個なのでnovel mergeは不可能。初回実installがdistinct childをemitし、別のpresent siteとSameInputsなら、formed ExactからMergeGuardを作りactual early mergeを構成する。

`EarlyMergeExample`: そのparametric構成を実際に具体化。checked Display(List Int)宣言に同入力whereをclause10/11として2個置き、初期guarded install→実guarded merge。child IDは異なる。親packet1個、alias非空、具体モデル、actual Reachable、Coherentを証明。merge対象の**両子クラスは未記録**であり、両方にpacketがあるクラスのmergeではない。両子のassociated outputsも空で、output等式相互作用の実証には数えない。

### D. support付き順序不変と失敗子を残す診断

`SupportLocalOrder` は任意roles、Reorders first last、first.roles=roles、**同じ tracked state**、任意root/frontierでInspection、DecisionGuard、SupportPending、全support Localの同値を証明。全diagnostic Resolves、独立Child、既存Acc、既存Classifyも同値。Classifyの存在を新たに与えず、異なるexecutor終状態を比較しないので一般canonicalLocalOrderは未解決。

`EarlyMergeDiagnostics` はCの実merge後、parent selected key1の子2個がそれぞれrejectedになることをsupport込みで確認。`.selected 1 [.rejected,.rejected]` の有限Resolvesが成立する一方、任意outcomeについてparentのClassifyは不存在。親自体をrejectedに潰さず、失敗子を保持する。

`DiagnosticAccessibility` は任意B4 SourceBoundary、任意registry/state/root/treeで、有限Resolvesがあれば独立ChildのAccを導く。成功Classifyを仮定しない。Localの関数性によりterminal失敗leafに隠れたselected childが無いことを証明している。Cの実到達可能・具体モデルあり・journal/alias非空の状態に適用し、**AccでもClassifyが存在しない**正確な例を得た。同じ例のStableも後段のEで証明した。これは失敗子を保持する診断仕様の回帰であり、一般V5不可能性の主張ではない。

`DiagnosticTotality` はさらに任意SourceBoundary/registry/state/rootに対して、有限Resolves存在 iff (独立ChildのReach閉包上で全点Local存在 ∧ Acc Child root)を証明。前向きは診断木とLocal関数性から閉包上の証人を取り、後向きはAcc帰納で失敗葉も保存する。成功dictionaryの必要十分条件と別の定理であり、actual Local全域性自体や実executor停止は証明していない。

独立レビューでも、同一snapshot限定、モデル非空、成功を仮定しない診断、診断と成功分類の区別を確認した。

### E. 実merge後の失敗診断もStableまで閉じた

`EarlyMergeClosure` でC/Dの**同じfinish**を対象に、任意source modelをfinal modelへ持ち上げ、予約originを変えるモデル族、ContextComplete、PointClosedを証明。sitesは親と2子、edgesは親→各子、Generatedは3点だけ。親と子のSameInputsはList Int≠Intで排除し、子同士は既存Aliasなのでnovel mergeなし。任意enabled installは親では既存2edgeと全モデルbranchでCommitted、子では現在rejectedと矛盾。予約origin refresh、equate、reobserve、enqueueも排除して**actual SupportSteps.Stable**を得た。

最終`stable_diagnostic_without_classify`は追加仮定なしで、actual Reachable ∧ concrete Models ∧ Stable ∧ independent Child Acc ∧ (∀outcome, ¬ Classify root outcome)。Dの完全診断はparent selectedと2 rejected leavesのまま。Stableでも選択親の失敗子をparent rejectionに潰さない仕様を具体化したもので、診断木を返す一般V5への反例ではない。associated outputsは空というfixture制限は残る。

`EarlyMergeNoEvidence` はこの同じfinishについて、任意valuation・任意payloadの親/子semantic Evidenceも不存在と証明。唯一のList宣言はInt子に対して実inspectionがFinishedでないことをkernel計算で示し、子Instance/Evidenceを否定する。親Evidenceからは完全な2子リストが得られるので先頭子で矛盾。一般のrejected⇒noEvidenceを使わず、実モデル存在と並べている。実到達・Stable・診断あり・成功辞書なしという意味論側の回帰まで得た。

## 一般境界の状態

「一般定義あり」はgeneral nominal carrierの現定義。言語全域のparser/elaboration網羅性ではない。

| SourceBoundary項目 | 状態 | 現在の具体化と制限 |
|---|---|---|
| Checked | 一般定義あり | GeneralDeclarations。全言語producer接続は別 |
| Models | 一般定義あり | tracked.currentのsource+packet+site意味論、Exact ledger |
| Step | 一般定義あり | support guard付きinstall/mergeと実administrative更新 |
| Stable | 一般定義あり | 同じ実Stepの閉性。一般停止証明は未完成 |
| Generated | 一般定義あり | 実emitted edgesとalias閉包 |
| RootPending | 一般定義あり | source lower-head保留 |
| RootK2 | 一般定義あり | source/feedbackの循環判定 |
| CandidateK2 | 一般定義あり | candidate inspectionの循環 |
| InspectionPending | 一般定義あり | 従来pendingとSupportPending |
| Survivor | 一般定義あり | 現在raw-context候補。Jointとは別 |
| Evidence | 一般定義あり | source occurrence索引・同一モデルの再帰Evidence。一般橋はJoint残余 |
| Reorders | 一般定義あり | source registry reordering |
| DictionaryEquivalent | 一般定義あり | payload/source対応に基づく既存比較 |

無条件のV5橋は6/14、未証明8/14のまま:
`progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode, generatedChildren`。
閉じた6本は`closure, stepModels, frontierLocal, localIdentity, dictionaryRefl, initialReorders`。
今回の具体的Stable/Joint/trace正例と一般条件付きreadbackも、この8本の一般フィールドの解消には数えない。

## inbox受け入れ条件との照合

- I-21/23（辞書側Evidence）: actual support Reachable/Stableを満たす非空再帰例で、完成payloadの全final-model Evidenceを得た。一般定理はJoint等を明示した条件付きreadbackまでで、一般evidenceNodeは閉じていない。
- I-25（初期と到達可能性）: positive recursiveとactual mergeの双方がactual Initialからの実Stepで到達。raw arbitrary journalの反例にすり替えていない。I-25一般橋の未証明8本は維持。
- I-24（凍結監査/README）: 新しい小さなCycle144 auditとmodule-guideを使用。凍結ファイルは変更ゼロ。
- I-19（Localの全域性）とI-21のStep/Stable/Generated一般定義はAstra担当のまま。DiagnosticTotalityは任意Localが存在するとは主張せず、有限診断の存在条件だけを証明。
- I-20（merge）: 既存の実merge操作を使用したinhabited回帰と限定scheduleの辞書キー整合性を追加。一般merge規則の定義は変更していない。

## Yulang2との対応・未検証

work/dots-auditを再fetchしてX1–X25 oracleを確認。X1はopaque nominal list＋where Display宣言check0、wrapper近似で子Display実使用run roots[1]。今回のLean fixtureはこの成功形に対応するが、新spec→旧runtimeのsource adequacyやprovenance-aware support実装一致を証明していない。旧oracleはX2の増大whereも通しており、今回の一般停止証明に流用しない。このサイクルでYulang2の新しいruntime実行はしていない。

## 次の本来の残差

1. 一般reachable・Stable・selected alias classのJoint。同時モデルを維持しつつ、historical packetの意味論からcurrent BranchAtへ運ぶ。literal Currentは実反例があるので無条件に使わない。
2. 両クラスが既に記録済みのmerge。構造Early条件だけでは覆わない。MergesClosed/SameInputsからcross-key一致を一般に導くか、実条件不足を特定する。
3. nonempty associated outputsと両alias class記録済みを含む実mergeへ回帰を拡張し、current BranchAtの同時モデルを保存する残差を明示する。今回の空outputs・未記録子mergeの成功を一般ケースへ拡張しない。Astra所有の一般Progress/where accessibility/canonical-orderとは分離する。

意味論を独断で追加していない。新しい言語設計質問はなし。使用量枠は不明。

## 検証と途中公開（最終確定前）

- focused `lake build <Cycle144の15modules> --wfail`: PASS,753jobs（依存キャッシュ込み）。
- `lake env lean --trust=0 Audit/Cycle144.lean`: PASS,104public theorem、全public宣言との集合一致、漏れ/余分なし。許容公理propext/Classical.choice/Quot.soundのみ。
- `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`: PASS。全体build/fullAuditは実行していない。
- 独立review: LocalReadbackExact、実mergefixture、支持付きLocal順序、失敗子diagnostic/Accを確認。leaf BranchAtはEvidenceから逆算しない直接source Instance輸送へ修正後に公開。
- 初期試行のconstructor引数/型推論エラーは修正し再build済み。未検証のまま通ったとは扱っていない。
- 中間公開0ca5afcで集約`Yulang.lean`の内容転送が切り詰められ、remote/local tree不一致を検知。直後ca2fc408で完全な元内容＋追記を復元し、fetch後tree完全一致を確認。現行branchの既存imports削除はゼロ。公開成功だけで完了とせず、内容の照合で検出して修復した。
- 計画/設定/凍結Audit/README/既存Yulang定理は変更していない。

中間source公開: `7d2624d9` (9 public)、`b0c48623` (50 public)、`cd7e3ca4` (80 public)、`ca2fc408` (104 public、修復済み)。

全追加public定理名と前提付き型の索引: [theorem inventory](../design/2026-11-12-cycle144-theorem-inventory.md)。
