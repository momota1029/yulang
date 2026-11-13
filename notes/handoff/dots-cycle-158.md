# dots cycle158: nested historical transport and mixed current evidence

## 時間・主定理・公開
V5未証明フィールドは **8/14** のまま。
progress, execution, halted, whereAccessible, treeExecution, canonicalLocalOrder,
evidenceNode, generatedChildren。

実開始2026-11-13T05:27:20UTC。55分締切06:22:19UTCを優先。
約50分時点で本報告を準備し、公開・照合まで締切内に終える。
終了理由は時間上限。25分で閉じなかった部分は、実混合完成木と
reobserveの構造的阻害・意味的代替、および独立再検証。

integration/m1-finalを新規取得し、f7c5fd1d58386305d85fdcb60d9f31c334e5740cから開始。
standing-orders/inbox、前cycle157報告、completed心拍を再読。ACTIVE、
上限なし、Evidence/I-25担当。前writerの稼働なしを確認し、別worktreeを使用。
06:12の再確認でもintegrationは同じ。公開先はwork/dots-mainのみ、
GitHub APIの非force/expected-headで更新した。

主要source checkpoint:
- 29d1c4067dc4348a9730fe53770b21dfb05b33b1
- 618fbf426ed26d96426556b37bf0f2eb302400da
- d701766f7423d1585d07f5e584a53c2183571e44
- 最終28module source:1786fa12441bdd46f9b6b28f333597b361989e1d
- 検証artifact:8d0f1fd2085142768a13e05d34da27fce2e6d8b8
- 次の分解:f5788bf679c0e2991e8525d00da63b34fe62de75

各不変commitを取得して期待bytesと比較した。心拍は開始、
05:36、05:46、05:55、06:05、06:10に公開。最終はcompletedへ更新する。
本報告のcommit SHAは会話への完了報告に載せる。

## 閉じた部分目標
並行作業を含むため所要時間は合計しない。

### 1. 過去nominal packetから現在Instance（約0〜20分）
任意の有限nested nominal/variable queryについて、Finishedな検査結果を
source-preserving Refinesで輸送。点・非点、繰返し捕捉を一般補題で扱う。
boundsはembeddingで写し、source由来のtest/originは保持する。
現在のbinding一致を仮定せず導出する。

実記録packetのinstallationから過去のFinished、lookup、role、RootDefined、
Metadataを導出。現在lookupとprivate/projection/materialization branchも導出し、
既存のInstanceへ接続した。current BranchModelsやInstanceを仮定しない。
primitive interpretation一致も実Value traceから導出した。

HistoricalNominalCoverageは実journal所属・occurrence一致・Refines・構文条件だけ。
そのselected-path coverageの下で、既存Classify/Completed treeから再帰Evidenceを導く。
任意reachable/Stable状態でこのcoverageが自動的に成立する主張ではない。

### 2. scalar applicationを含むwhere子（約8〜23分）
where引数が変数またはnullary scalar applicationのregistryでは、
実Generated子のlower≤upperをmaterializationと現在Modelsから導出した。
端点順序を別途仮定しない。解釈の履歴保存によりregistry構文条件から
journal条件を導く。現在scalar Shapeと有限request catalog所属を接続し、
再帰selected辞書のEvidenceへ進めた。

実Initial→Value install、別々に割り当てられたscalar端点、正モデル、
旧VariableRegistryの範囲外を回帰で証明した。
一般の引数付きcompound constructorや任意where式は未対応。

### 3. 実混合完成木（約20〜35分）
各selected nodeが「過去nominal coverage」または「現在generated scalar coverage」
のいずれかなら、既存の再帰辞書Evidenceを導く。
where構文制約はheadのnested nominal patternを排除しない。

実Value到達・Stable・正モデルの2-node fixtureで、この定理を端まで使用した。
rootは記録されたunary nominal packet、生成scalar leafは歴史packetを持たない。
実Local選択、Classify、Resolves、Completed、coverageを証明し、
任意の現在Models assignmentでEvidenceを導出した。
この完成木はunary nominal+scalarであり、深いnested operational例ではない。

### 4. reobserveの正確な境界と意味的代替（約27〜37分）
二つの安易な一般化を否定した。
- genuinely Improvingな同一carrier Revisionはdescriptorを保持するRefinesではない。
- 実Value到達・Stable・正モデル・Generated・selectedを満たすleafでも、
  対応する歴史packetがない場合がある。

前者はEvidence輸送そのものの不可能性ではない。
Certified Revisionの任意の現在モデルにおいて、同じsourceのold/new descriptorの
nameとarityが一致し、各parameter位置で一つのobserved valueが両方の区間にFitsする。
type/row双方のcross ParameterChecksと、各old位置に対応するcurrent parameterを導出。
Refines、endpoint equality、report equalityを仮定しない。

実certified improving (2,3)→(2,2) reobservation、正モデル、no-Refinesと
意味的compatibilityを同時に回帰した。これは既存reobservation Stepの例であり、
新たなguarded Value Stepや完全辞書輸送の証明ではない。

## 厳密な制限
- 一般evidenceNode、全言語の完全性・主型性・実行器・停止性は未達。
- Refinesは名目的descriptor保持を要求する。任意reobserveへ拡張しない。
- mixed theoremのregistry制約は未使用宣言を含むwhere引数全体にかかる。
- nested非点・繰返し捕捉回帰のpositive_nonpointはModels+Finishedのみ。
  その異なるleaf値はpositive ProjectionModels/BranchModelsを証明しない。
- nested8→9例は構造的Refinesのみ。新source8がreservedでなく、new-Knownもなく、
  実Refreshではない。正の深いnested operational例は次の課題。
- 実2→3Value refreshのunary current InstanceとK2不在は証明済みだが、
  そのfixtureの選択・完成木は別途未証明。上記2-node完成木とは区別する。
- semantic revision bridgeは全Report・capture singleton/merge切替・current
  materialization・子identityの輸送まで閉じていない。

## SourceBoundary 13項目
全13項目は現Value boundaryで定義済み。全言語網羅性の証明とは別。

|項目|現定義|残る区別|
|---|---|---|
|Checked|GeneralDeclarations.Checkedとroles一致|front-end adequacyとは別|
|Models|SaturationState.Models(current)|意味論の定義|
|Step|ValueSteps.Step|一般progress/execution/halting未達|
|Stable|ValueSteps.Stable|履歴packet所属やbinding一致を意味しない|
|Generated|SaturationState.Generated|一般選択子bridge未達|
|RootPending|NominalState.RootPending|現在context既知性|
|RootK2|FeedbackK2.RootK2|既存規則|
|CandidateK2|FeedbackK2.CandidateK2|既存規則|
|InspectionPending|CycleK2/SupportPending|全観測網羅性とは別|
|Survivor|RecursiveCandidates.Survivor|一般Evidence接続未達|
|Evidence|DictionaryRecursiveEvidence.Evidence|本cycleは条件付き橋と実回帰|
|Reorders|RegistryReordering.Reorders|canonicalLocalOrder未達|
|DictionaryEquivalent|DictionaryPayloadOrder.Equivalent|主定理全体ではない|

## 検証・失敗・公開制限
Lean4.35.0。新28module・公開定理157。全moduleをYulang.leanへimport。
最後のfocused --wfail buildは依存閉包906jobs、成功。
正確な全28sourceを独立cacheへ--trust=0で再compileし、
private/generated補助も含む370宣言の依存公理gateが成功。
23小監査で全157公開定理と追加1definitionを検査。
completedは公理なし、他はpropext/Classical.choice/Quot.sound以内。
保存したAudit/Cycle158DependencyGate.leanも再実行して370宣言PASS。

source SHA256、全公理出力、build/gate/checksをnotes/verificationへ保存。
audit出力のqualified-name集合と公開157定理の集合を照合し欠落なし。
禁止構文、entry import coverage、git diff --check、凍結path不変更を確認。
既存sourceの変更はYulang.leanへのimport追記のみ。
全体lake build、root Audit、verify-leanは常設指示により実行しない。
監督役の全体検証は別途必要。

公開途中の7dc0bd113はentry importが後続2moduleより先に入るraceを起こした。
不変commit照合で検出し、618fbf426で不足sourceを補い、完全一致を再確認した。
以降は固定local commitから全bytesを採取してから公開した。
7dc単体を統合対象にしない。

独立cacheの初回copyは/tmpを満杯にした。自分の失敗copyを除去し、
workspace cacheへ移して再検証した。sourceの消失なし。
試作中のList補題名誤りなどは修正後の同scope検証で成功。
最終auditにerror/warningなし。末尾の空きはworkspace39GiB、/tmp431MiB。
利用quotaは取得できず不明。

618fbf426と1786fa124のworkflow APIは空一覧だった。
APIはPR-triggered先頭ページだけなので、全CI不存在/成功を意味しない。
全作業員とbuildは終了し、次cycleの並行writerを残さない。

## Yulang2・次の部分目標
Yulang2 auditのY2-ROLE-003/004とspec06の再展開・lower/upper cross規則を照合。
実機Yulang2 CLIは実行しない。新しい言語意味論の決定・質問はない。

次はsemantic reobserveのinspect/inspectMany相互帰納。
origin/binder coverageとFitsを保ち、literal report equalityを要求しない。
captureが複数からsingletonへ変わると、allocationがmerge sourceからliteral
boundsへ切り替わるため、その意味的関係を独立に証明する必要がある。
全current requestの根拠も別途必要。歴史packet存在を万能の仮定にしない。

詳細:
- notes/design/2026-11-13-cycle158-module-guide.md
- notes/design/2026-11-13-cycle158-next-revision-transport.md
- notes/design/2026-11-13-cycle158-nested-operational-gap.md

最後の約12分は追加の語彙的補題ではなく、正確な非空性の区別、
次の輸送橋の分解、全公開定理の監査集合照合、不変commitの再取得、
保存済みgate再演と公開の整合性検査に使用した。
