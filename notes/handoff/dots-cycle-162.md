# dots cycle162: I26 Settled境界での選択・Evidenceの橋

## 結果・未解決

V5は **8/14 open** のまま。progress / execution / halted /
whereAccessible / treeExecution / canonicalLocalOrder / evidenceNode /
generatedChildrenは一般形では未証明。一般B4・完全性・主型性・終了性の完成ではない。

Astraが追加したI26の実Settled guard/Step/Stableを使い、選択済み辞書の正負の境界と
条件付きEvidenceを接続した。既存State/Step/guard/budget定義は変更していない。

- 新SupportPendingならselected Local/Classify/完成辞書がない。選択された任意深さの
  descendantにも適用。意味論Evidence自体の否定ではない。
- 新Classify selectedは、旧Value Classify selectedと、その選択child graph上の
  全DecisionGuardとの同値。任意の無関係な需要にguardを要求しない。
- 空fact ledgerでは旧Value guardから新guardを導け、初期sourceの旧新Stepは同値。
  一般stateのStable同値を主張しない。
- **実Settled Stable**から、selected-key Jointを明示して全final-model Evidenceを
  導いた。新Stableから旧Stableを導く誤った経路は使わない。packet-free terminalな
  root/generatedの場合のみ、既存source形状からJointを解消した。
- 辞書tree全体では、選択descendant各点のStableとselected-key JointからEvidenceを
  導いた。child Evidenceを仮定して結論を言い換えたものではないが、一般Jointは未解決。

## 正例と意味論上の境界

実guarded install・Reachable・Stable・Classify・全model Evidenceを持つ再帰例と
名前つき出力例を移した。その一方、記録されていないterminal子についてDischargedが
ないため、親packetはUnsettledとなる。意味論的に完成した辞書とledgerの片付きは別。
再帰例は出力なし、名前つき例の出力先はsource既知なので、これを誤った消費保留の
反例とはしない。

reserved-output例は実Settled install→equate→refreshを持ち、fresh ID2がTrustedな
出力ledgerからHeadJustified/ReadyAtになることを証明。別query157のDecisionGuardも
成立する。ただしpacketの子は空で片付きは自明、queryは生成・installされたとは
証明していない。非terminalな出力だけを根拠とする消費者が実際に待機・再開する
end-to-end例は未達であり、次の具体的検証対象である。

## 復元・担当範囲

予定開始09:27:19Z、実作業開始09:29Z、最終上限10:22:19Z。
新規取得integration/m1-final:70461874b8cb9b974260d5bdcb02a415603ad34f。
standing-orders/inbox/AGENTS/git-concurrency、公開cycle161とcompleted心拍を再読。
前cycle最終45266223b7e7611b657e803672c72e6d8390902dから復元。
既存writer終了を確認し、同じ作業への並行書込みなし。
監督役のentrypoint・cycle161報告・source replay・心拍のmerge競合は監督役側を優先。
I21 Evidence laneのみ。Astraのガードや終了性の設計を変更しない。

## 現在の13項目

|項目|現定義|残る区別|
|---|---|---|
|Checked|GeneralDeclarations.Checkedとroles一致|front-end adequacyとは別|
|Models|SaturationState.Models(current)|意味論の定義|
|Step|SettledSteps.Step|Astraの実guard使用、一般progress/execution未達|
|Stable|SettledSteps.Stable|旧Value Stableを意味しない|
|Generated|SaturationState.Generated|一般選択子bridge未達|
|RootPending|NominalState.RootPending|現在context既知性|
|RootK2|FeedbackK2.RootK2|K2拒否の優先維持|
|CandidateK2|FeedbackK2.CandidateK2|既存規則|
|InspectionPending|Value pendingまたはSettled SupportPending|選択排除は証明、意味論Evidence否定ではない|
|Survivor|RecursiveCandidates.Survivor|一般Evidence接続未達|
|Evidence|DictionaryRecursiveEvidence.Evidence|final contextのModelsに対する意味論|
|Reorders|RegistryReordering.Reorders|canonicalLocalOrder未達|
|DictionaryEquivalent|DictionaryPayloadOrder.Equivalent|主定理全体ではない|

## 検証と制限

Lean4.35.0。focused build、全新sourceの独立cache trust0再compile、公開名/型/公理と
private/generated宣言の依存公理gateを実施。最終件数と終了コードは末尾に追記。
許可する公理はpropext/Classical.choice/Quot.soundのみ。sorry/new axiom/native_decideなし。
root Audit.lean・README・lake設定は凍結。全体build/root Audit/全体verifyは実行せず、
監督役の全体検証が必要。新moduleはすべてYulang.leanからimport。
独立reviewで新Stable/旧Stableの区別、Jointとpacket-free条件、treeの各点条件を確認。
試作中のdependent elimination・暗黙型推論エラーは修正してから再compileした。

Yulang2は既存Y2-ROLE-003/004とspec6§6.3/6.5を文書照合。区間中心の新設なし。
今回新しいCLI実機テストは実施していない。I26を旧Yulang2との同一規則とはしない。

## 公開

work/dots-mainのみ。checkpoint2d14f9f4c909cb367c6c4d8e0723674da9784b7bは
Gitで再取得し、固定local955cd2615との差が意図した心拍だけと確認した。

## 検証確定（09:53 UTC）

新11module・公開100定理、公開名とauditの照合PASS、100型の出力EXIT0。
独立cacheの全source trust0再compile PASS。private/generatedを含む132宣言の
依存公理gate PASS。audit12本PASS、標準3公理以外なし。focused build最終788jobs PASS。
差分限定verify-lean --no-buildはEXIT0。report-only collectAxiomsのrun_cmd1件を
REVIEWとして記録した。宣言を挿入するメタプログラムではない。
