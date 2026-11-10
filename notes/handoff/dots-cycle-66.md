# Cycle66: root-stable ownership across actual recursive captures

## Result and exact boundary

**部分目標は閉じた。** 実candidate runnerが生成したwhere子を任意有限回再captureしても、captureとchildの全ambient endpoint occurrenceのownerを、最初のroot tableで実際に計算できる橋を閉じた。前cycleの「一段ごとに親tableへ戻す」境界から、全履歴で一つの元root tableを使う形へ進めた。固定例だけの結果ではない。

新しい `CommonRoleRecursiveSourceAllocation.History` は、実 `CommonRoleWhereSourceModels.run` の正のreturnと実child membershipだけで辺を作る独立な帰納的関係。宣言・old demands・local binder mapは各辺で異なってよい。所有者・alias等式・モデル・子辞書・深さ上限は仮定しない。

新しい実行器 `follow` は、任意有限の宣言/binder map/child位置の列を実際に実行し、直前の実returnのdemand履歴を次のcaptureへ渡す。その正のreturnから `History` を導き、元root領域への包含を導く。`prepareAt` は実candidateへ計算済みownerを付ける。`follow_conservative` は、そのpayloadを消すと元runnerの三通りの結果がそのまま戻ることを証明する。実履歴の後ではlookup失敗を追加しない。

captureされたlocal binderの番号とambient名を混ぜない。元candidate内のbinder番号・区間・state・child順序を保持し、compound bindingにはその両endpointに現れる全source occurrenceのownerを登録する。別のcallでlocal binder番号が同じでも、元sourceが違えばownerも違う。異なる子の観測型が偶然同じでもsource identityとして統合しない。

**境界:** ここで閉じたのはambient endpointの元root ownership。`bindingSource : Nat → Nat` が決めるordinary demandの意味的な名前空間は、依然としてcaller入力。今回のowner登録からその写像を生成したとは主張しない。新しい存在変数・associated equalityが導入する名前をroot表へ追加する一般source registryも未完。

`History` は任意有限の履歴を許すが、可能なgoal全体の有限性や履歴長の上界を主張しない。`follow` はcallerが選んだ正のpathの有限実行utilityであり、非正のcandidateまたは存在しないchild位置ではそのpathを返さない。これをpending/selected/ambiguous/rejectedへ読み替えない。命令列の自動選択、兄弟のfairness、再生成、停止、意味的飽和は未接続。

任意の明示root graphのsnapshot保持も証明したが、ordinary stateからのgraph構築・意味的十分性・feedbackは証明していない。既存linear structural interval captureの範囲を維持し、繰り返しhead binderなどへ文法を広げていない。T1c外側入口、一般resolve_exact、X13〜X16外側入口、M1三つ組は未完。

## Theorems and quantified claims

新規 `lean/Yulang/CommonRoleRecursiveSourceAllocation.lean` の14公開定理をAuditへ登録し、Yulangからimportした。既存Leanは追記のみ。以下はすべて同モジュール内。

1. `history_included`（補助・健全性）: 任意のslots・root・goalと実有限Historyについて、goalの両endpointの全ambient名は元root表に含まれる。
2. `captured_included`（補助・健全性）: 任意のslots・old demands・宣言・goal・binder map・実正returnについて、全captured bindingの両endpoint名は元goalに含まれる。モデルは仮定しない。
3. `payload_included`（補助・健全性）: 同じ全入力と実正returnについて、captured bindingと全where childを順に連結したpayloadの全名は元goalに含まれる。
4. `prepareAt_conservative`（局所健全性・完全性）: 任意のtableと全実入力について、goal名のtable包含を明示前提とすると、owner payloadを消したprepareAtは元runの三結果と厳密に一致する。
5. `prepareAt_exact`（局所健全性・完全性）: 任意のtable・実入力・Prepared結果について、prepareAtの正return iff 元candidateの正returnかつ実lookupがそのownersを返す。包含やモデルの前提は不要。
6. `history_conservative`（局所健全性・完全性）: 任意の実Historyとその後の任意candidate入力について、元root表でのprepareAtは元runを保存する。4の包含前提を実履歴から導く。
7. `history_owners`（補助・健全性）: 任意の実Historyとその後の実正returnについて、計算可能な元root ownersが存在し、全payload名列の順序・重複と各ownerの正準性を満たす。
8. `owner_identity_exact`（局所健全性・完全性）: 同じ任意tableで成功した二つの実lookupと任意の左右occurrenceについて、ownerが等しい iff 元ambient名が等しい。異なる子・bindingの比較にも使える。
9. `history_allocation`（補助・健全性）: 任意の実Historyと後続正returnについて、全payload位置でnewRootが計算した元ownerのretainに一致し、任意の有限root graph・role・visible head列で全snapshot保持が成立する。
10. `next_history`（補助・健全性）: 任意のroot・到達済みcursor・instruction・実next returnについて、返ったgoalも実History内にある。
11. `follow_history`（補助・健全性）: 任意の到達済みcursor・任意有限instruction列・実follow returnについて、最後のgoalは元rootからの実History内にある。深さ固定ではない。
12. `follow_conservative`（局所健全性・完全性）: 任意のroot・初期demand・有限instruction列の実成功と任意後続candidate入力について、元root表のprepareAtからownerを消すと、その実累積demandを使った元runに一致する。
13. `follow_owners`（補助・健全性）: 同じ任意の実有限pathと任意後続正returnについて、元rootの計算済みownersが存在し、全payload名列と正準性を満たす。
14. `registered_binding`（補助・健全性）: 任意の実History・後続正return・実captured binding・その両endpointに現れる任意名について、元root tableの実first-occurrence lookupが正準ownerを返し、その元名が一致する。

上記は局所source橋。主型性やB4全体の健全性・完全性の完成定理ではない。実装utilityの限定をdocstringへ明記し、言語仕様による拒否判定とは区別した。

## Verification

検証済みlocal source commit: `65481008e6b5e2fc6ded4e6c3fb34cfa6077bfd7`。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleRecursiveSourceAllocation` — exit 0。最終sourceの全文:

```text
✔ [306/306] Built Yulang.CommonRoleRecursiveSourceAllocation (1.4s)
Build completed successfully (306 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/yulang66-audit.lean` — exit 0。14定理の公理監査と10実行回帰。全文:

```text
'Yulang.CommonRoleRecursiveSourceAllocation.history_included' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.captured_included' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.payload_included' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.prepareAt_conservative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.prepareAt_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.history_conservative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.history_owners' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.owner_identity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.history_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.next_history' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveSourceAllocation.follow_history' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveSourceAllocation.follow_conservative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.follow_owners' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursiveSourceAllocation.registered_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

許容されたpropext / Classical.choice / Quot.soundのみ。実owner検索とpath実行は計算可能で、区間中心を選ばない。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ 65481008e (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` — exit 0。

focused buildと個別監査は120秒上限つきbackground processと親shell waitで実行。初回実装にdependent case分解後の等式の向きのelaboration errorが1箇所あり、rflへ直して最終版を通した。型や前提は弱めていない。補助のAPI名確認で存在しないlemma名も一つ確認したが、実装では実在するList.mem_of_getElem?を使った。

**全体lake build、全Audit、広域AxiomGate、全verifyはローカルでは実行していない。** 上のverifyはdiff checks only。exact sourceのGitHub CIは後述。

### Reproducible executable regressions

監査fileのimportと14本の公理表示の後に、次の10例を実行した。

```lean
open Yulang Yulang.CommonRoleRecursiveSourceAllocation
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)
open Yulang.CommonRoleWhereSourceAllocation (parentTable)

def rootDecl : Declaration := ⟨1, 0, [.pair (.var 0) (.tick (.var 1))],
  [(2, [.pair (.var 1) (.var 0)]), (3, [.var 0])]⟩
def childDecl : Declaration := ⟨2, 1, [.pair (.var 41) (.var 42)],
  [(3, [.var 41]), (3, [.var 42])]⟩
def leafDecl : Declaration := ⟨3, 2, [.var 99], []⟩
def rootGoal : Goal := ⟨1, [(.pair (.var 7) (.tick (.var 9)),
  .pair (.var 7) (.tick (.var 10)))]⟩
def firstStep : Instruction := ⟨rootDecl, id, 0⟩
def secondStep (position : Nat) : Instruction := ⟨childDecl, fun n => n + 1000, position⟩
def observation (position : Nat) : Option (List Nat × List Nat × Nat) := do
  let cursor ← follow id ⟨rootGoal, []⟩ [firstStep, secondStep position]
  let answer ← prepareAt (parentTable rootGoal) id cursor.requests leafDecl cursor.goal (fun n => n + 2000)
  let payload ← answer
  pure (payload.owners.map Fin.val, payload.candidate.bindings.map Prod.fst,
    payload.candidate.state.requests.length)

-- Two actual descents, fresh local binder labels, one original root table.
example : observation 0 = some ([1, 3], [99], 5) := rfl
-- The same final local binder 99 now denotes different original sources.
example : observation 1 = some ([0, 0], [99], 5) := rfl
-- Missing child position ends the utility path, never a fabricated verdict.
example : (observation 2).isNone = true := rfl
-- Both endpoint identities survive even though each descendant table starts at 0.
example : (follow id ⟨rootGoal, []⟩ [firstStep, secondStep 0]).map
    (fun cursor => parentTable cursor.goal) = some [9,10] := rfl
example : (follow id ⟨rootGoal, []⟩ [firstStep, secondStep 1]).map
    (fun cursor => parentTable cursor.goal) = some [7,7] := rfl
-- Root capture and all generated child sources keep exact order and multiplicity.
example : ((prepareAt (parentTable rootGoal) id [] rootDecl rootGoal id).bind id).map
    (fun payload => payload.owners.map Fin.val) =
      some [0,0,1,3,1,0,3,0,0,0] := rfl
-- The original negative candidate outcome is preserved.
example : (prepareAt (parentTable rootGoal) id [] rootDecl {rootGoal with role := 99} id).map
    Option.isSome = some false := rfl
-- The original unsupported unbound template outcome is preserved.
example : prepareAt (parentTable rootGoal) id []
    {rootDecl with requirements := [(3, [.var 999])]} rootGoal id = none := rfl
-- Allocation really checks its supplied domain rather than hiding missing names.
example : prepareAt [] id [] rootDecl rootGoal id = none := rfl
-- Empty traversal is exactly the original cursor, including old requests.
example : (follow id ⟨rootGoal, []⟩ []).map (fun cursor => cursor.requests.length) = some 0 := rfl
```

## Publication, preservation and recovery

開始時にintegration/m1-finalを取得し、GitHub経由でstanding ordersとinboxを再読。I-4 ACTIVE、上限なし、I-11の25分上限を確認した。開始時のintegration/live work headはともに `0086e2dbad4344ecd31794cb44b36a2707f5b3f2`。cycle65はcompletedで対応報告があり、作業場clean、復旧不要。

開始心拍 `dea3205e5673da5518ac23ed0d6a3f198481fd81` を公開し、exact SHAをfetch/merge。通常のwork branch fetchでは古いremote tracking refが残っていたため、公開済みSHAを明示して取得し、最新の作業を失わないことを確かめた。integrationは取得済みでlocalの祖先。新しいworktree・cacheコピーは作っていない。

sourceは6成果パスとrunning心拍の計7パス。全blob SHAをlocal git hashと照合し、最新remote treeに重ね、non-force/expected-headの一回のref更新で公開した。書込の拒否・結果不明・承認待ちはない。

公開source commit: `fdf22e227994db7b55071c26878ec4ab1cc706a4`。
source tree: `57ed4720a7bf1c91e6b91119fc08bc1699e17d8c`。

公開後、live refと完全recursive treeを取得。全7変更pathのmode/SHA一致、対象外2161blobの保持、全2168blob、truncationなしを確認した。exact sourceをlocalへfetch/mergeし、6成果pathのremote差分が空であることも確認した。他のbranchには書いていない。

本報告とcompleted心拍を続けて公開し、最終treeを照合する。cycle全体は8変更path。最終SHAと照合結果は親へ返す。

## Yulang2 comparison and remaining B4 bridges

実装前にwork/dots-auditを取得し、x-oracleのX13〜X16、C3-PARENT/C3-PARENT-NEGを読んだ。spec 6.3の兄弟更新・安定後最終化を確認。実機の具体例を今回の一般source履歴定理の証明とはしない。新しいYulang2実行はしていない。新たな言語意味論の選択や質問ノートはない。

B4主定理の残り主要橋は**5本のまま**:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

今回閉じたのは最初の2橋の中の「実再capture履歴で元ambient source領域を保ち、capture/child endpointの正準ownerを元rootから計算する」部分。一般source registry、計算される有限goal領域、停止はまだ閉じていない。

次の候補:
1. caller入力のbindingSourceを、実local bindingの履歴から作る意味的demand名前空間へ接続し、異なるcallの衝突防止と意図した共有を証明する。endpoint ownerとcompound bindingの意味的sourceを混同しない。
2. ordinary更新からgraph再構築・inspectionの意味的十分性と、associated child feedbackを共有モデル・親再生成へ接続する。
3. 実driverを有限goal領域・Paterson/K2の停止・意味的飽和へ接続する。

## Time and limits

予定開始2026-11-10T03:57:19Z、締切04:22:19Z。最初の環境dateは03:58:44Z。開始心拍updatedは03:59:24Z、source心拍updatedは04:06:00Z（約8.7分）で、10分の区切りまでに公開を進めた。

開始時とsource公開後の空きは48G（全63G、使用13G）。一つの作業場と既存cacheを再利用。使用量枠は不明。I-11の部分目標が閉じたため、時間埋めの補題は追加しない。

## Exact source CI

source `fdf22e227994db7b55071c26878ec4ab1cc706a4` のCI:
- core: https://github.com/momota1029/yulang/actions/runs/42753755229
- proof: https://github.com/momota1029/yulang/actions/runs/42753755162

2026-11-10T04:07:42Z時点ではcore completed/success、proof in_progress。最終確認を追記する。

2026-11-10T04:09:44Zに再確認し、exact source commitの**core / proofともcompleted / success**を確認した。その後の変更は報告・心拍のみで、Lean sourceは変えていない。ローカル全体検証を実行したという意味ではない。

報告・完了心拍の準備は2026-11-10T04:09:44Z、予定開始から約12.4分。公開・最終tree照合を含めて終了する。
