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

## Yulang2との対応・未検証

work/dots-auditを再fetchしてX1–X25 oracleを確認。X1はopaque nominal list＋where Display宣言check0、wrapper近似で子Display実使用run roots[1]。今回のLean fixtureはこの成功形に対応するが、新spec→旧runtimeのsource adequacyやprovenance-aware support実装一致を証明していない。旧oracleはX2の増大whereも通しており、今回の一般停止証明に流用しない。このサイクルでYulang2の新しいruntime実行はしていない。

## 次の本来の残差

1. 一般reachable・Stable・selected alias classのJoint。同時モデルを維持しつつ、historical packetの意味論からcurrent BranchAtへ運ぶ。literal Currentは実反例があるので無条件に使わない。
2. 両クラスが既に記録済みのmerge。構造Early条件だけでは覆わない。MergesClosed/SameInputsからcross-key一致を一般に導くか、実条件不足を特定する。
3. Astra所有Progress/where accessibility/canonical-orderと衝突せず、今回の辞書側一般残差を閉じる。具体traceを一般橋へ数えない。

意味論を独断で追加していない。新しい言語設計質問はなし。使用量枠は不明。
