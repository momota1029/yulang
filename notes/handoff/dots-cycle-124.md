# Cycle124: shared dictionary transactions, RHS provenance, and refinement

**一般 source の B4Bridges V3: 未証明（未充填）12 / 全12。一般B4は未完成。**

開始: 2026-11-11T19:30:44Z。最終経過時間・報告公開・writer解放は completed
heartbeat に記録する。期限は20:22:19UTCで、ユーザーの55分上限を文書の長い
実行時間指示より優先した。終了理由はI-15(a): 最終検証・公開・報告を含む
サイクルの時間枠。25分時点までに最初の記録・provenance・全辞書transactionの
中核が通ったが、別invocation・実slot増加・兄弟の共通modelまでの一連の部分目標は
25分に収まらなかった。時間を埋める別fragmentの分類器は追加していない。

## 復元した状態と指示

- fresh integration: `36170f419826a57f7f32ffc7a1fcd6905c9bb300`。
- 開始前の公開head: `6b974c88e764e07fd679fe5423cdeda0ea4f1a82`。
- cycle123のcompleted heartbeatと公開報告を読み、前writerの解放を確認した。
  crash復旧は不要。残っていたcheckoutとLean cacheを再利用し、cacheは複製しない。
- integration取り込みで衝突したのはheartbeatのみ。integrationの版を残してから
  cycle124のheartbeatへ更新した。他のsourceや未公開作業は失っていない。
- inboxはACTIVE、hash `2631f8a557ab1a3b3551556a3f516746e3e8fa65`。
  I-19はcycle123で公開・検証済みなのでI-18項目5を継続した。20:03の再読でも
  同じACTIVE/hashだった。Astra担当の項目1・2の既存定義は変更していない。

## 閉じた部分目標

時間帯は重なりを含むwall-clockの目安で、合算した作業時間ではない。

1. **実際のordinary記録からRecordedを生成、約19:32–19:37。** 任意のStateと
   sourceに位置づけられたLocatedについて、全head上下界・全output等式のatomsを
   実際に追加する。source/type/row IDs、観察、intervalを保持し、Recordedを
   callerの証明から実行の出力定理へ移した。更新後Modelsの必要十分条件と、
   既に含意された式の追加によるmodel保存を証明した。
2. **実宣言の明示RHS/defaultのprovenance、約19:35–19:49。** 独立Suppliesと
   executable lookupのiff、宣言済み名の被覆、一意性、宣言順の変更での不変性を
   証明した。明示Equation/Patternの変数とdefault Roles.Termの位置変数を区別し、
   名前が同じでもtarget21/22の二つの出力を落とさない。
3. **全辞書を一つの共有状態へ記録、約19:38–19:55。** 有限Prepared treeの全node
   から一つのbatchを計算する。実Planと明示的なterm解釈を持つValidから全nodeの
   Recordedとsource Evidenceを作る。ある固定source witnessを先に選び、その後の
   任意の最終modelで全nodeの式が成り立つ。batch順のmodel不変性と共同充足性はiff。
   同じ実visible declarationからcanonical childrenとrootのRHS provenanceを返す
   OutputPlanも、lookup exactness・元のchild plan・出力source保存・被覆まで通した。
4. **別source invocationで同じimpl keyを使う場合、約19:55–20:01。** 旧Frameは
   capture/allocationを宣言IDだけで索引し、別呼び出しも同じbindingに固定していた。
   新しいtransactionは完全なOccurrenceで索引したframe familyを使う。同じchecked
   Wrap key2の二つの根で、入力100/101・出力200と入力500/501・出力600を保持し、
   両lookupとregistry順変更を検証した。一つの旧Frameでは両方を表現できないことも
   証明した。これはrevisitの共有方針やfresh allocatorの決定ではない。
5. **任意のRefinesと実slot増加、約19:59–20:05。** Locatedの端点・target・termを
   埋め込みで移し、Recordedと全assignmentでの式の意味を保存した。元packageの
   正確な像liftPackagesについて、同じsource辞書と全refined modelの証拠を保つ。
   実際に1slotから2slotへ増やし、旧slot0を1へ移す回帰を追加した。新source9と
   旧type10/row20を分離し、満たすmodelと同じ三node辞書100/101/102を示した。
6. **別々のmodelを兄弟の共通modelに取り違えない、約20:04–20:06。** 同じ自由な
   元状態でint packageとstr packageはそれぞれ充足可能だが、両者を含むbatchは
   不整合であり、順を逆転しても同じと証明した。重複packageは12atomsを保持する。
7. **最終検証・source公開・報告。** 11moduleすべてのfocused aggregate、79宣言の
   trust-zero audit、全量化子のsignatures、diff-only gate、remote全tree照合、
   exact source commitのhosted full build/Auditを確認した。

## 主張の側と量化子

[全79宣言の正確な型](dots-cycle-124-theorems.md)を併記する。78 theoremと
1 refinement certificateの監査件数であり、79本のB4主定理を完成したという意味ではない。

- **EquationRecording / BatchRecording: 健全性・完全性のordinary部品。** 任意の
  State・Located列・一つのAssignmentについて、更新後Models iff 元Modelsかつ
  全列の式。充足性を自動で保証せず、その存在条件を明示する。順序不変はmodel集合。
- **Transactions: 辞書式の健全性・補助。** 任意のChecked Registry、rootごとの
  supplied Frame、明示的term関係、有限Prepared treeとValid証拠に対し、実際に
  全nodeを記録した状態で一つの固定source witnessが全modelを満たす。有限treeや
  frameを探索して得る定理ではなく、一般resolverや停止性を完成したものでもない。
- **AssociatedProvenance / PlannedOutputs: 宣言出力の構文的健全性・完全性。**
  任意の宣言・名前一意性に対してlookupと独立Suppliesがiff。被覆は実signatureを
  前提にする。実checked visible keyについてchildrenと要求されたroot outputsを
  同一宣言に結び、全出力occurrenceを保持する。関連型の値の評価ではない。
- **InvocationExamples: 表現の補助。** 実checked Wrapの別source instantiationで
  異なるcaptureを保持する正例と、一つの宣言索引Frameには入らない反例。既知性や
  feasibilityを判定したとは言わない。
- **RefinementEvidence: 状態更新をまたぐ式の健全性・意味保存。** 任意のRefines、
  Located、global Assignmentについて、型とrowのsource写像を使い同じ式の意味を
  保つ。任意の元packageの像に対して同じsource辞書を保存する。任意の新packageや
  source Stepとの対応を仮定なしで得たのではない。
- **各Examples: 補助／回帰。** 明示/default優先、別target、別invocation、実slot増加、
  非空model集合、共同充足性の正負例を含む。新しい主型性の一般定理はない。

## まだ繋がっていない境界

**重要な残り:** Transactions.Validは実Planと、依然として明示的な
`terms root key located`を要求する。OutputPlanはchildrenと明示/default RHSを同じ
宣言に結んだが、Located.outputがそのRHSを意味するという接続はまだ無い。

一般の宣言/captureからLocatedを作るには、nominal constructorのCommon解釈、
中心を選ばないintervalの表現、compound materialization、default位置変数と
明示変数の正確な導出が必要。現TyTermにnominal nodeはなく、constructor catalogueは
layoutだけで、Captureは上下端を持つ。任意の端点を中心として選んだり、nominal名を
variant tagへ符号化したりして、この穴を隠していない。

また、Prepared treeと全Plan/termsは入力。transaction_storedは不整合な式も記録でき、
その場合の全model主張だけなら空集合上で真になる。そこでmodel iff・共同充足性の
必要十分条件・正負の具体modelを別に検証したが、一般feasibility decisionは未実装。
frame familyは完全Occurrenceを索引するので、需要が変わったrevisit間の整合性や
allocator freshnessは未証明。liftPackagesも元packageの正確な移送像だけを述べる。

## SourceBoundary全13項目

| Field | 現在の状態 | 残り |
| --- | --- | --- |
| Checked | 一般certificate定義あり | 完全checker、constructor/Common対応。 |
| Models | 一般shared-state定義あり | 完全な宣言/role modelではない。 |
| Step | MISSING | 一般状態更新・再生成。 |
| Stable | MISSING | EOFを含む兄弟fixpoint。 |
| Generated | 一般emission/Plan/lookup部品あり | 実candidate frame・freshness・materialization。 |
| RootPending | 一般partial snapshot定義あり | Neededは保守的で最小適用性を導いていない。 |
| RootK2 | 一般partial normalized定義あり | 実source正規化との対応。 |
| CandidateK2 | MISSING | 実candidate inspection。 |
| InspectionPending | 実source fieldはMISSING | V3 schemaは対応済み、実predicateなし。 |
| Survivor | MISSING | Planはhead照合・feasibility・選択ではない。 |
| Evidence | full role fieldはMISSING | 全tree式記録・provenance・refinementは追加。RHS→term解釈と実選択が未接続。 |
| Reorders | 一般定義あり | fixed入力の宣言/child/output順は証明済み。最終state/candidate対応なし。 |
| DictionaryEquivalent | 一般source/payload構造定義あり | full boundaryの観察意味との接続。 |

B4Bridgesのどのfieldも具体的な一般source instanceとしては閉じていない。
新しい定理で拒否範囲を実装都合に弱めたり、意味論を新たに決定したりしていない。

## 検証

- final local focused aggregate: **542 jobs、exit0**。全11新moduleを明示して実行。
- scoped trust-zero audit: **79宣言、exit0**。1宣言は公理なし、それ以外も既存の
  propext / Classical.choice / Quot.soundだけ。全件のAudit登録・import・signatureを照合。
- exact signatures: exit0。暗黙parameterも表示した全型を別紙に保存。
- `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`: exit0。
  既存Lean行の削除なし、lake config不変、Auditはimportと末尾追記のみ。
- `git diff --check`: exit0。途中のelaboration/tactic失敗は修正し、最終結果のみをPASS扱い。
- **full local lake build、full local Audit、監督役の別AxiomGateは実行していない。**
- [完全なfocused出力](dots-cycle-124-verification.md)。

最終source: [11d696483de2e0dac53b979ffbe8668c688bc7d9](https://github.com/momota1029/yulang/commit/11d696483de2e0dac53b979ffbe8668c688bc7d9)。
source tree: `3517a73ff8e678b0ca5189f2c66e8870df8c121a`。
**2403 tracked filesの全treeがlocalと一致**。変更pathだけの部分比較ではない。

exact source commitのhosted CI:
- [core](https://github.com/momota1029/yulang/actions/runs/43093686533/job/130776960187): success。
- [proof](https://github.com/momota1029/yulang/actions/runs/43093686518/job/130776960555): success。

runnerのcheckout SHAも確認済み。**full build1374 jobs**、full Auditの**8629件の
公理出力**（227件が公理なし、許可外公理0）、各example commandが成功した。
このcycleの79件もすべて含まれる。出力件数は重複を含みうる監査出力数であって、
新しい独立定理の数ではない。これはhosted full検証であり、local fullを行ったという
意味ではない。監督役の独立AxiomGateまで実行済みとは主張しない。

## Yulang2との照合・質問

work/dots-auditの`notes/audit/y2-claims-role-boundaries-cycle-2.md`、
ROLE-MORE-001〜005を読んだ。旧advertised-whereの挙動を新specの候補前提へ輸入しない。
正本はspec06 §§6.2–6.3、§6.5と既存のinterval設計。新しいYulang2実機実験は行っていない。
今回は新しい分類規則を作らず、source保持・式・宣言RHS provenanceを扱った。
新質問ノートは0件。既存のcycle70 invocation-sharing boundaryを勝手に回答していない。
nominal/interval/defaultの不足は実装上の接続未達として設計ノートに残した。

## 公開・復旧・制限

source checkpointは`b41cbe7204e1`、`2e918af355db`、`11d696483de2`。
work/dots-mainだけへexpected-head・non-forceで公開した。全blobのGit hashと全treeを
照合し、他branch・spec・plan・lakefileを編集していない。source時点でintegrationからの
差分はheartbeatを含め17path。報告3ファイルを含め最終20pathになる。

前writerとの同時書き込みはない。開始時の古いgit transport work tracking refをlive API
headと混同していない。中断した検証sessionは明示的に終了し、未知のremote mutationは0。
一部のshell/compiler応答が遅くなったため、入力を固定したcombined source checkを併用し、
最終的には全moduleの通常のfocused buildも通した。中断した処理を成功として数えない。
startup heartbeatのupdatedは概算だった。その後の値と最終所要時間は実際のUTCで記録した。
10分/待機中の心拍と途中公開を分離し、時刻は各公開heartbeatに残した。

quotaは不明。作業時の空きdiskは約38GiB。失われたsourceはなく、全検証済み変更を公開した。
最終報告treeの照合とwriter解放はcompleted heartbeatに記録する。

## 次の最初の部分目標

1. **OutputPlanの明示/default provenanceを実term解釈へ接続する。** nominal carrier、
   center-free interval、二種類のbinder scopeを保ったelaborationが要る。今の任意termsを
   actual RHSから導くことがEvidenceの残りの最短経路。
2. **actual candidate inspectionからinvocation別Frameを導く。** 同じroot/keyのchild
   coherenceはPlanで証明済み。freshness、共有source、revisit coherenceを外部入力から除く。
3. **実生成とRefinesをgeneral Stepへ結ぶ。** 今回のdictionary witness保存は部品として
   使えるが、任意のsupplied finite tree・traceを一般driverの証明に読み替えない。
