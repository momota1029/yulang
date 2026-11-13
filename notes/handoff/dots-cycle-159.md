# dots cycle159: semantic capture collapse and positive nested branches

## 時間・主定理・公開
V5未証明フィールドは **8/14** のまま。
progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder,
evidenceNode, generatedChildren。

実開始2026-11-13T06:23:20UTC。通知runは06:27:19UTCだが早い実開始に
合わせて55分上限を保守的に07:18UTCとした。終了時刻・最終状態は末尾へ記録する。
integration/m1-finalを新規取得し707d524c308e1142dbf3dd3582636b4d33567b15から開始。
standing-orders/inbox、前cycle158報告、completed心拍を再読。ACTIVE、
Evidence/I-25担当、前writer終了を確認し独立worktreeを使用。
公開先はwork/dots-mainのみ。固定local commitの内容をGitHub APIで作成し、
非force/expected-headで公開した。

source checkpoint:
- b9e7e1f505250c6e602cc75567b26206ce7c336d: capture/semantic schema橋
- fd4620848ebb3be2e68ecc684ddea0821d00584f: full terminal branch橋と正の初期source例

両checkpointは取得し直し、固定local sourceとのgit diff一致を検証した。
心拍は開始、06:32:30、06:46、06:54、07:03に公開。06:32→06:46は
約14分となり10分間隔を超過した。以後は復帰し、最終はcompletedへ更新する。

## 閉じた部分目標
並行作業の所要時間は合計しない。
### 1. singleton/merge切替の意味（約0〜20分）
任意の非空capture occurrence列について、membershipが同じならFitsが同じ。
複製captureをsingletonへ縮めると、literal source IDは異なり得るが、
同じモデルでmerge条件が成立すれば両端点が意味的にEquivalentになる。
さらに旧propagateのModelsと新baseのModelsからsingleton側propagateを導出。
新private merge成立を結論そのものとして仮定しない。

### 2. nested reinspectionとschema（約5〜27分）
深さ2のnominal queryで旧outer引数(lower,upper)から(lower,lower)へ変えるShapeを定義。
繰返しbinder captureが2件から1件に減り、両reportはFinished。
旧ProjectionModelsと点leafからfirst/lastの意味同値を導出し、captureの意味と
固定schemaのmaterializationを輸送。literal report/binding/source一致は不要。

terminal・単一input binder・点leaf・非output変数scope条件の下では、
旧BranchModelsと新raw Modelsから**新BranchModels全体**を導出した。
旧propagation/projection/materializationを分解して、新private merge、
selfChecks、projection、schemaを組み立てる。新BranchModelsは仮定しない。
この一般定理はShape revisionを使うがCertified/Step自体は仮定しない。

### 3. 正の非点nested witness（約0〜25分）
前cycleの異なるleaf値ではProjectionModelsを得られなかったため、
同じleaf型を持つ8-slot nested sourceを作った。root boundsは非点(0,3)。
full ProjectionModels、checked terminal declaration、private merge model、
BranchModels、Prepared、Survivorを証明した。
ordinary0≤3を明示してInitialSourceと到達可能な初期ValueBoundary状態にも接続。
この到達は初期/reflexiveでありinstallation/refreshではない。

### 4. 実certified improving collapse（約14〜30分）
4-slot fixtureでInitialSource、SourceFormed、実administrative Value reobserve、
Certified/Improves、正モデル、両ProjectionModels、capture2→1を証明した。
旧duplicate allocationのmerge modelを具体的に構成し、
新singleton propagation/endpoint equivalenceを導出。literal capture IDsは異なる。

### 5. 実到達と既存Evidence（約27〜33分）
同じregistry/rootでSourceFormedと実reobserveを再構成し、具体的な
old/current BranchModels、Prepared、Survivor、既存Instance/Evidenceを証明。
`.node31[]`の正の辞書Evidenceであり、旧branch/newbranchを仮定にしない。
現在journalのModelsも初期の正モデルとcertificate.exactから証明した。
installed packetを持たず、子/schemaは空のterminal例。これは**一つのモデル**の
非空性であり、任意の現在モデルについてのEvidenceNodeではない。

### 6. 空でないroot schemaと正確な境界（約30〜35分）
associated equation `0 := input7`、target source3を持つ別rootで、
実際に空でないgenerated schema、old/current materializationとBranchModelsを証明。
このoutput-bearing rootのoperational到達は証明していない。
terminalかつProducedな宣言ではproduced output binderが空であることも証明。
上記のnamed outputはinput-backedで、生成output binderとは区別する。

`int`は`[bottom,int]`と`[int,int]`の両方にFitsするがlower端点はEquivalentでない。
この反例で「共通の実型だけから端点同値」を否定した。reobserve健全性の反例ではなく、
点条件が唯一可能な条件だとも主張しない。次はactual-modeだけの一方向Fits輸送を試す。

## 厳密な制限
- 全言語evidenceNode、完全性・主型性・実行器・停止性は未達。
- 深さ2/単一binder/点leafの有限fragment。任意nested queryの相互帰納ではない。
- terminal branch theoremはwhere子を持たない。emitted child identity輸送は未達。
- 非点positive nested initial例と実reobserve例は別fixtureとして区別する。
- 旧BranchModelsと新raw Modelsは一般定理の明示的な意味仮定。
  具体例で非空性を確かめても任意reachable stateでの成立には一般化しない。
- source/candidate/Step既存定義は変更しない。新guarded Value Stepではない。

## 各定理の寄与
下表の分類は各moduleの全公開定理に適用する。128定理の完全な名前一覧は
verificationのsources.json。完全性または主型性を閉じた定理はない。
点leaf・terminal等は**証明fragmentの制約**であり、言語仕様の拒否規則ではない。

|module（GeneralDictionary接頭辞省略）|定理数|側|
|---|---|---|
|CaptureMultiplicity|7|補助|
|CaptureSemanticCollapse|3|補助|
|PositiveNestedBranch|11|補助／正の回帰|
|PositiveNestedInitial|8|補助／正の回帰|
|PositiveNestedProjection|10|補助／正の回帰|
|SemanticCollapse|7|補助|
|SemanticCollapseAllocation|3|補助|
|SemanticCollapseAllocationExample|5|補助／正の回帰|
|SemanticCollapseBranch|3|健全性の条件付き輸送補助|
|SemanticCollapseBranchExample|21|補助／正の回帰|
|SemanticCollapseEvidenceExample|5|健全性のモデル付き回帰|
|SemanticCollapseExample|20|補助／正の回帰|
|SemanticCollapseOutputExample|14|補助／正の回帰|
|SemanticCollapsePointBoundary|5|補助／過強な推論の反例|
|SemanticCollapseSchema|2|健全性の条件付き輸送補助|
|SemanticSchemaTransport|4|健全性の条件付き輸送補助|

## SourceBoundary 13項目
全13項目は現Value boundaryで定義済み。全言語網羅性とは別。

|項目|現定義|残る区別|
|---|---|---|
|Checked|GeneralDeclarations.Checkedとroles一致|front-end adequacyとは別|
|Models|SaturationState.Models(current)|意味論の定義|
|Step|ValueSteps.Step|一般progress/execution/halting未達|
|Stable|ValueSteps.Stable|reobserve後branchの一般保存を意味しない|
|Generated|SaturationState.Generated|一般選択子bridge未達|
|RootPending|NominalState.RootPending|現在context既知性|
|RootK2|FeedbackK2.RootK2|既存規則|
|CandidateK2|FeedbackK2.CandidateK2|既存規則|
|InspectionPending|CycleK2/SupportPending|全観測網羅性とは別|
|Survivor|RecursiveCandidates.Survivor|一般Evidence接続未達|
|Evidence|DictionaryRecursiveEvidence.Evidence|一般evidenceNode未達|
|Reorders|RegistryReordering.Reorders|canonicalLocalOrder未達|
|DictionaryEquivalent|DictionaryPayloadOrder.Equivalent|主定理全体ではない|

## 検証・失敗・公開制限
Lean4.35.0。新16module、公開128定理。
focused `lake --wfail build <16targets>` は742jobs PASS。
全16sourceを独立cacheへ `lean --trust=0` で再compileし、private/generatedも
含む374宣言の依存公理gate PASS。保存したAudit/Cycle159DependencyGateも374PASS。
16個の公開定理auditを実行し、source上の128名と出力集合を照合して欠落なし。
公理はpropext/Classical.choice/Quot.sound以内。sorry/new axiom/native_decideなし。
全moduleのentry import、git diff --check、既存source凍結を検査した。
公開定理名は行頭・インデントの両方を再走査し、取りこぼしなし。
source SHA256・build・audit・gate・checksはnotes/verification/dots-cycle-159-*に保存。
root Audit/README等は凍結。既存source変更はYulang.leanのimport追加のみ。
全体lake build/root Audit/verify-leanは実行しない。監督役の全体検証は別途必要。

共同作業中にgenericとconcrete allocation moduleの名前が一度衝突し、
共有cacheのoleanを上書きした。公開sourceの上書きはない。concreteを
AllocationExampleへ改名しgenericを再compile。その後全新sourceを独立cacheへ
再compileして依存検査に成功。試作中のList membership証明エラーも修正した。

## Yulang2・次の部分目標
notes/audit/y2-claims-casts-roles.mdのY2-ROLE-003/004とspec06§6.5を再読。
再展開とlower/upper cross制約の方向は一致。不変区間の中心を新設しない。
今回の点leafは定理fragmentの制約であって言語仕様の点化ではない。
Yulang2 CLIは未実行。新たな仕様決定や質問はない。
次は深さを固定しないinspect/inspectManyの意味的simulation、
nonterminal materializationの新request/子identity、およびEvidenceへの接続。

## 再検証と引き継ぎ
source最終checkpoint:a82c8f87a015917bc55f2cc618950ea24291ad91。
監査artifact:601df8cc789d146e8dc31c125a49a112bbd9fb56。
第三checkpoint:f100bd0abeecf48e86b5bf5aa9bb11193ce808d6。
不変commitを取得し直して、固定local sourceとのbytes一致を検証。
sourceとartifactの全tree比較でも、意図した心拍以外の差分なし。
独立reviewでoperational fixtureのregistry/root/current journal model一致と
一般定理の結論を仮定していないことを確認した。
fd4620848とa82c8f87のworkflow APIは空一覧。PR-triggered先頭ページのみなので全CIの
不存在や成功は主張しない。監督役の全体検証が必要。
workspace空き39GiB、/tmp430MiB。quota取得不可で不明。
詳しいmodule対応と次のmode-sensitive分解は
notes/design/2026-11-13-cycle159-module-guide.md。

07:06頃にintegrationとinboxを再取得し、同じ707d524c3、ACTIVEを再確認。
公開branchの最新refもGitHub APIで自分の心拍commitと一致し、他writer変更なし。

## 終了
2026-11-13T07:13:30Z、実開始から50.2分で最終公開準備。55分上限内に公開・照合を終える。
全workerとbuildは終了。最終心拍はcompleted。終了理由は検証と公開を含む時間枠。
報告の最終commit SHAと公開照合結果は会話への完了報告に記載する。
