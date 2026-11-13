# dots cycle160: actual-modeによる非点区間のEvidence保存

## 結果と未解決欄

V5の残りは **8/14** のまま。
`progress / execution / halted / whereAccessible / treeExecution /
canonicalLocalOrder / evidenceNode / generatedChildren` は今回も未証明。
一般B4、完全性、主型性を完成したとは報告しない。

今回、前サイクルの「leaf上下端が同値」という制限を、terminalな深さ2の
capture collapseについて外した。rootから生成されるschemaがactual modeで
あることを使い、旧Fitsから現Fitsへの包含で保存を証明した。
非点区間bottom/intと、捨てる側int/intの具体例では、Fitsが真に広がり、
旧endpoint-equivalence条件が偽でも、同じmodelで旧・現Evidenceが成立する。
さらに初期ordinary等式からCertifiedを導いた実reobserve Step、Reachable、
SourceFormed、Checked registry、現journal Models、非空関連出力schemaと
旧・現Evidenceを一つの正の回帰定理で結んだ。
これはStable、最終出力installation、任意の到達状態のEvidenceではない。

## 開始時の復元と範囲

開始2026-11-13T07:30:00Z。今回通知07:27:19Zから55分の08:22:19Zを最優先。
integration/m1-finalを取得し直し、c4fba7cafa2912e582c0bf7b621f8786a81b0cf1を確認。
standing-orders/inbox全文、最新I-25、cycle159の公開報告と設計、AGENTSを再読。
ACTIVE、サイクル上限なし。前cycle159はcompleted、worker終了を確認して再利用。
Astraの宣言/State/Step/candidate laneへ書き込まず、dotのEvidence laneを担当。
実装前の設計をnotes/design/2026-11-13-cycle160-actual-mode-plan.mdに置いた。
07:56頃の再fetchでもintegrationは同じで、inbox ACTIVEを再確認した。

## 主張・前提・位置づけ

全200公開定理の名前と量化した型は
`notes/verification/dots-cycle-160-signatures.txt`、ファイル対応とSHA256は
`dots-cycle-160-inventory.json`に記録。各moduleの日本語相当の意味、前提、
狭い断片と次の境界は `notes/design/2026-11-13-cycle160-module-guide.md`。

- 任意のactual-only schemaについて、旧Models、test/variableの包含、出力同値、
  入力Fits包含、現在capture originの旧側被覆があれば、同じmodelで現Models。
  test/variableの存在と全称、pair/capture-origin sharingをすべて保存。
  schema生成のactual-only性も証明し、terminal rootでは仮定しない。
- 任意の既存Shapeを持つ深さ2・単一入力binder・terminal宣言、Checked、query一致、
  旧BranchModelsと現source Modelsの下で現BranchModels。leafの点性は不要。
  schema scopeはCheckedのScopedから導出。旧証拠を前提にInstance/Evidenceへ接続。
  Certifiedと旧journal Modelsがあれば現source/journal Modelsも導出するが、
  任意の履歴から旧Evidenceが得られるという未解決不変条件は隠さない。
- 任意のrenameとmodelで、全source IDについてrename前後の割当型の同値からObservesのpush/pullを
  nominal/structural pathを通じて導出。generated schemaはrequest retargetと可換。
  actual-only、output同値、input Fits包含、capture-origin対応、旧Modelsの下で
  renamed schema Models。新Modelsそのものは仮定しない。ただしallocatorが
  これらの意味的前提を供給する一般定理は未証明。非単射2→1の正例も検証。
- lower modeへ同じwideningを無条件に流用すると失敗する具体例を証明。
  mode制限の必要性であり、YulangやCertified revisionの反例ではない。
- 非空関連出力を持つ具体的初期sourceで、ordinary双方向制約から全modelに対する
  revisionのexact性を証明。実Step/Reachable/SourceFormedと具体的な共通modelの
  旧・現Evidenceを構成。結論を仮定してCertifiedに包み直したものではない。

これらは健全性の条件付き輸送補助、補助定理、正負の回帰。
terminal/深さ2/単一binderは証明断片の制限で、言語の拒否規則を新設していない。


|新module（GeneralDictionary接頭辞省略）|公開定理数|側|
|---|---:|---|
|ActualSchema|11|健全性の条件付き輸送補助|
|ActualSchemaOrigin|14|健全性の条件付き輸送補助|
|ActualSchemaOriginExample|5|補助／正の回帰|
|ActualSchemaScope|11|健全性の条件付き輸送補助|
|CertifiedNonpointEvidence|2|健全性の条件付き輸送補助|
|CheckedNonpointEvidence|4|健全性の条件付き輸送補助|
|CollapseReadiness|5|健全性の条件付き輸送補助|
|NonpointBranch|3|健全性の条件付き輸送補助|
|NonpointCertified|18|健全性の条件付き輸送補助|
|NonpointCertifiedOutput|24|補助／正の回帰|
|NonpointCollapse|2|健全性の条件付き輸送補助|
|NonpointEvidence|2|健全性の条件付き輸送補助|
|NonpointExample|22|補助／正の回帰|
|NonpointModeBoundary|4|補助／mode制限の反例|
|NonpointOperationalEvidence|11|補助／正の回帰|
|NonpointOutput|14|補助／正の回帰|
|NonpointStrict|24|補助／正の回帰|
|NonpointStrictEvidence|9|補助／正の回帰|
|NonpointStrictOutput|15|補助／正の回帰|

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

Lean4.35.0。新19module、公開200定理。focused buildは749jobs PASS。
全19sourceを独立cacheへ `lean --trust=0` で再compileし、private/generatedも
含む574宣言の依存公理gate PASS。公開定理auditと保存gateを独立cacheで実行。
公理はpropext/Classical.choice/Quot.sound以内。sorry/new axiom/native_decideなし。
全moduleのentry import、git diff --check、既存source凍結を検査する。
既存source変更はYulang.leanのimport追記だけ。root Audit/READMEは凍結。
全体lake build/root Audit/verify-leanは実行していない。監督役の全体検証が必要。

正確なコマンド・ログ・source SHA256・公開定理名はnotes/verificationに保存。
小さい試作のsimp/abbreviation照合エラーを修正した。
registry_checkedのunused simp警告を除去後、--wfail focused buildを再実行PASS。
型一覧出力で未対応option pp.widthを指定した一回は失敗し、除去して再出力した。
これらを未解決の検証成功として数えていない。

e1834b594c103ab53148a58b755d283614ca389fのworkflow APIは空一覧。
PR-triggered先頭ページのみのAPIなので、全CIの不存在/成功は主張しない。
workspace空き39GiB、/tmp430MiB。使用量quota取得不可で不明。

## Yulang2・次の部分目標

notes/audit/y2-claims-casts-roles.mdのY2-ROLE-003/004とspec06§6.3/6.5を比較。
再展開、lower/upperのcross制約の方向と整合。不変区間の中心を新設しない。
今回actual-onlyは生成schemaの既存modeに関する証明で、言語を点区間に制限しない。
Yulang2 CLIは今回未実行。新たな仕様決定や質問ノートはない。
次の候補は3つに限定する。
1. 非terminalの新request/child identityからorigin/Fits対応を導出する。
2. Shapeの深さ2制限を外しinspect/inspectManyの意味的simulationを証明する。
3. 選択履歴から全current journal modelで旧BranchModels/Evidenceを得る不変条件を
   導出し、一般evidenceNodeへ接続する。

## 公開と引き継ぎ

公開はwork/dots-mainのみ。source checkpoints:
0dd12f18b0807a7b9974c96148b01dda1a42e879、
8eb4d8490b3222baa1e2cecb31de0f16395471ee、
e1834b594c103ab53148a58b755d283614ca389f。
各不変commitを取得し直し、固定local sourceとの全tree差分が心拍だけであることを確認。
後続のregistry確認・監査artifactと最終報告も同じ手順で検証する。
最終commit SHAは会話への完了報告に記載する。
