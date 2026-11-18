# dots cycle251 — mixed-time compiler / I-48停止性ゲート

## 結果と方針転換

開始2026-11-18 00:31 UTC。開始時integration `9ec236c79` のstanding orders/inboxを
再読し、cycle250成果と公開treeの一致、writer不在を確認。実Planのmixed-time
packet compilerを進めた。01:12の再取得でintegration `00793b4ac` のI-48を初確認。
その時点でLean追加を停止し、測度・反復再現・依存義務の設計ノートを作った。
**停止性の測度は未確立。部品追加を続けない。次回は停止性設計を最優先。**

新規28モジュール、237個の明示宣言をfocused strict buildおよびcollectAxiomsで
検証。27モジュール236宣言はI48確認前に公開済み。最後のSourcePlanProducerの
1定理も確認直前に検証済みで、今回保全する。I48確認後の新Lean実装はない。

## 証明範囲（詳細の全名・hashはCompleteAuditファイル）

以下は任意の対応plan/frame/assignmentについて、各定理に明示したSafe・coverage・
registry・初期Models等の前提の下の主張。source言語全体の無条件受理ではない。

- MixedSchema/MixedPacket: old origin/contextとcurrent capture/binderを分け、全8field
  を独立Holdsと同値にcompile。old/現を一つのmappingに潰さない。
- RoleEnvironment/Schema/Equations: old値、lower/upper、binder、targetの別roleを定義。
  actual/lower/upperとoutput優先、nominal args actual、positional defaultを区別。
  同値なrole環境への輸送と式のexact性。default位置は名前binderではない。
- StableRoleEnvironment/Head: actual entryから作るcomputed fresh solveがcapture
  方程式を供給し、old snapshotのoriginとnew aggregateのboundを同じwitnessで結ぶ。
  freshモデルを仮定して済ませず構成する。Neededはchecked scopeからinputNames内。
- RoleRequests/Child/Emission: actual child identity/arity、compound/variable capture、
  input上下要求（変数パターンでも両方）、named outputs、root requestsを抽出。
  translation失敗をunknownとして分離。Holdsだけではunknown時に自明となり得る。
- RolePacket/Congruence/StableRolePacket: 実全8fieldのfinite compiler exact、translation
  readyBool exact、同一witnessのinstall_exact。readyは意味適格性の証明ではない。
- RoleBinder: outputは実output target、point singletonは旧endpoint、非点/複数は
  既存binder allocation。I45 source Step規則全体の移植を済ませたとは言わない。
- PlanProducer/RegisteredPlan: actual Planから(root,declaration,inputNames)整合を
  構成し、予約済みhandleは再seedせず再利用。coverage/coherenceを供給して有限
  checker成功。初回producerと登録済み反復producerを混同しない。
- PlanTrace/Models: actual有限Plan列から各更新後frameに応じたpacket Deltaを生成。
  Knownなら構造成功、length一致・target固定。独立PlanHoldsとPermittedが同値、
  初期Models/Holds/public一致を同じassignmentに置いたpublic_models_iff。
  有限列入力はsource Accの証明ではなく、effect Deltaはこのtraceと未統合。
- RoleEffects/Class/Completeness/JournalEffect: 実Supplies・lookup・翻訳に基づく
  default/output/class式を生成。失敗を落とさずNoneとし、独立OutputHoldsから
  compile成功とモデルの完全性。historical/current要求を別々に取得するeffect
  compilerもexact。ただし同一明示envを読むので、plan.bindingsと最後のinstallの
  対応、実source Live再生成、candidate uniquenessは別義務。
- SourcePlanProducer.initialize_and_install: reachable mixed sourceから旧journalと
  consumersに一致する安全frameを初期化し、実Plan producerのchecker成功と
  install_exactへ接続。旧blockモデル追加仮定なし。source eligibilityから
  RolePacket.Holdsを自動導出する定理ではない。

## 回帰と停止性に関する発見

- RoleReadRegression: old origin=empty、新capture=widthという区別を保つ実型例。
  誤った単一値への置換は不成立。source受理回帰ではない。
- RoleModeRegression: positional defaultとnamed actualの差、nominal内部actual、
  outputによるlower override、unknownの空式が自明でもknown=falseであること。
- PlanProducerRegression: 既存OptionalInstall229の実checked Planを2回処理し、
  登録表再利用とchecker成功を確認。新境界で意味モデルがあるとは主張しない。
- SnapshotGrowth: private targetが常に[2]でも、snapshot raw updateで構文高さnの
  treeが生じ、全段Safe/同値なのに高さ上界がない。任意rawの表現側反例であり、
  新source到達反例ではない。DuplicateUnionはそのfamilyのroot一段局所修正だけ。
  一般に冪等ですらなく、停止性の解決ではない。

I48設計 `2026-11-18-cycle251-i48-termination-gate.md` に、有限root集合、distinct
owner数、slot総数、term constructor深さ、将来public escapeの未証明を列挙。
239型はI45維持で防ぐ予定、240型は同じownerならslot再利用だがsource全体の
新root/child生成を排除できていない。従って測度未確立として止まる。
新たな言語意味の選択を求める閉じたYulang反例はなく、質問ノートは追加しない。

## 検証・公開・制限

Lean4.35.0、全28moduleを依存順に `--trust=0 -DwarningAsError=true` で再build。
CompleteAuditは237宣言、許容公理依存はpropext/Classical.choice/Quot.soundのみ。
全commandとexit0はfinal-build.sh/txt。実fixtureのため旧依存49moduleもstrict build。
前回1425依存source hash不変、今回import closure1600sourceを記録。旧Lean凍結、
barrel追記のみ、新規Lean禁止語なし。全体lake build/verify-lean/Yulang2は未実行。
全体検証は監督役担当。独立read-only reviewで上記境界を再確認した。

環境の短い再起動でtool内一時値が失われ、途中tree作成でbase欠落を検出した。
その不一致treeへrefは進めず、正しいbaseから再作成して全tree一致後に公開した。
公開はwork/dots-mainのみ。既存247/248復旧quarantine・248/249 lockは対象外。
開始/10/20/30/40分の心拍を公開。I48の停止指示による研究中止は約41分時点、
残りは設計・検証・保全。最終公開時刻と照合はpublication-receiptに記録する。
使用量枠は不明。新source Acc・後継12性質・199〜240の新境界移植・EvidenceNode
は未完了であり、受入条件達成と数えない。

## 次の指示候補（I48の順番を守る）

1. source Stepが生成し得るroot/child/public descriptorの有限basisとconstructor
   深さ上界を設計し、owner/slot総上界とprivate escape不変条件を説明する。
2. 239/240型が同じ表現で本当に再現しないかsource規則に即して調べる。
   再現すれば閉じた反例、説明不能ならその理由を残し部品追加は停止。
3. これが閉じた後だけAccをLean化する。packet/effect/Permittedの残橋はその後。
