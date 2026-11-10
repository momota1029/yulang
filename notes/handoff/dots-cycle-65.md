# Cycle65: actual where endpoint ownership and canonical graph allocation

## Result and exact boundary

**部分目標は閉じた。** 任意有限の実candidate returnから、全where子の両endpointに現れる全source occurrenceについて、元parent内の有限ownerを実際に計算し、既存のcanonical graph allocatorにつないだ。外からownerやsource名の等式を渡す必要はない。

新しい実行入口 `CommonRoleWhereSourceAllocation.prepare` は既存の `CommonRoleWhereSourceModels.run` の後に有限lookupを実行する。`prepare_conservative` は、owner payloadだけを消すと元の3通りの結果が厳密に戻ることを、任意の入力に対して証明する。lookupは新しい失敗を増やさず、ordinary stateも、子の順序・重複も変えない。正の実returnなら、元parentのモデルが存在しなくてもownerは計算できる。

`prepared_allocation` は、各実出力occurrenceの新rootが計算した旧ownerを保持したrootそのものであり、任意の旧graph・role・visible head列に対して、全snapshotが既存のreindexingと可換になることを証明する。unknown、capture payload、順序・重複、循環graphのK2を含む既存snapshot全体を保存する。固定例の結果ではない。

**境界:** source identityは元endpoint構文のambient名であり、宣言local binderの綴りでも、観測された型の一致でもない。異なるambient名を、別のsource registryや非単射slot mapが同一視する場合のalias推論までは行わない。parent tableは現在の元goalの全endpoint occurrenceから作る局所tableであり、全再帰履歴で一つのroot tableを維持したという主張ではない。

graphは任意の明示入力。ordinary stateからgraphを構築して意味的十分性を示す定理ではない。compound endpointを新しい未知source変数として割り当てず、その中に現れる元source名だけを扱う。子が新たにcaptureするlocal binderの登録、associated equalityの親への帰還、state依存の再生成、一般有限仕事領域・飽和、最終辞書分類は未接続。元のbindingSourceとambient slotsは既存runへの明示入力のまま。

既存linear structural head scannerの範囲をそのまま保ち、repeated head binderやjoin head、未束縛where名の扱いを拡張していない。言語全体の拒否範囲を決めず、辞書や子成功も主張しない。T1cの全外側入口、一般resolve_exact、X13〜X16の完成、M1三つ組は未達。

## Theorems and quantified claims

新規 `lean/Yulang/CommonRoleWhereSourceAllocation.lean` の15公開定理をAuditへ登録し、Yulangからimportした。既存Leanは接続・説明の追記のみ。

1. `representative_present`: 任意の有限tableと名前について、実first-occurrence lookupが有限ownerを返す iff 名前がtableに現れる。
2. `locate_exact`: 任意の有限tableと任意の名前列について、実owner列検索が成功する iff 全名前が元tableに現れる。空列、重複、存在しない名前を含む。
3. `locate_sources`: 任意のtable・名前列・実検索結果ownersについて、ownersへ元source名をmapした列は元の名前列と完全一致する。順序・重複を含む。
4. `representative_canonical`: 任意の実first-occurrence returnについて、そのownerのcanonical rootはowner自身。
5. `locate_canonical`: 任意の実検索結果ownersの全要素について、canonical rootはその要素自身。
6. `returned_included`: 任意のslots・旧需要・宣言・goal・bindingSource・既存runの正の結果について、全実where子のendpoint名は元parent table内にある。モデルの前提はない。
7. `returned_owners`: 同じ任意入力の正の実結果について、計算可能な有限ownersが存在し、実lookupがそれを返し、元名列と正準性の両方を満たす。
8. `ownerAt_source`: 任意の実lookup結果と子occurrence位置について、計算されたownerの元source名はその子occurrenceの名前と一致する。
9. `ownerAt_canonical`: 同じ任意位置について、計算されたownerはすでにcanonical。
10. `allocated_root`: 任意の実lookup結果と子位置について、実newRootはその計算した旧ownerをretainしたものと等しい。追加のalias等式は不要。
11. `allocated_snapshot`: 任意の実lookup結果・子位置・有限旧graph・role・visible head列について、allocation後のnewRootでの全inspectSnapshotは旧ownerのsnapshotをretainしたものと等しい。
12. `returned_allocation`: 任意の既存runの正の実結果に対し、計算可能な全ownersと全位置でのroot/snapshot保持をまとめて得る。graphは全称、モデルやchild成功は前提でない。
13. `prepare_conservative`: 任意のslots・旧需要・宣言・goal・bindingSourceについて、新しいprepareからowner payloadを忘れると元runの結果と完全一致する。外側none・内側none・正の結果をすべて含む。
14. `prepare_exact`: 任意の同入力とPrepared結果について、prepareがその結果を返す iff 元runがそのcandidateを返し、実lookupがそのownersを返す。ordinary stateと子はcandidate内でそのまま保存される。
15. `prepared_allocation`: 任意のprepareの正の実結果について、その実ownersが元名列を保存し、全子位置でroot保持、全graph・role・visible列で全snapshot保持を満たす。

これらはsource allocationの健全性・完全性・保守性を示す局所一般定理。B4全体の完成定理に読み替えない。

## Verification

検証済みlocal source commit: `002e8d5ec7bbcbcc6c99f95cfeb4c2ee17b70f2f`。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleWhereSourceAllocation` — exit 0。最終sourceの全文:

```text
✔ [305/305] Built Yulang.CommonRoleWhereSourceAllocation (1.3s)
Build completed successfully (305 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle65-audit.lean` — exit 0。15定理の公理監査と9実行回帰。全文:

```text
'Yulang.CommonRoleWhereSourceAllocation.representative_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.locate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.locate_sources' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.representative_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.locate_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.returned_included' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.returned_owners' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.ownerAt_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.ownerAt_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.allocated_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.allocated_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.returned_allocation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.prepare_conservative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.prepare_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleWhereSourceAllocation.prepared_allocation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

許容されたpropext / Classical.choice / Quot.soundのみ。実装のlookupは有限のfirst-occurrence検索であり、区間の中心を選ばない。

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。全文:

```text
verify-lean: . @ 002e8d5ec (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

4. `git diff --check` — exit 0。

focused buildは120秒上限つきbackground processと親shell waitで実行。最初の実装で名前の置換後の参照と、依存するlist indexのrewriteにelaboration errorがあった。明示的な型・congruenceで修正し、定理の型を弱めずに最終版を通した。

**全体lake build、全Audit、広域AxiomGate、全verifyはローカルでは実行していない。** 上のgateはdiff checks only。exact sourceのGitHub CI結果は後述する。

### Reproducible executable regressions

監査fileのimportと15本の公理表示の後に、次の9例を実行した。

```lean
open Yulang Yulang.CommonRoleWhereSourceAllocation
open Yulang.CommonRoleCaptureNormalization (Form)
open Yulang.CommonRoleStablePaterson (Declaration)
open Yulang.CommonRoleIntervalPaterson (Goal)
open Yulang.CommonRoleCanonicalSourceGrowth (newRoot)

def declaration : Declaration := ⟨1, 0, [.pair (.var 0) (.tick (.var 1))],
  [(2, [.join (.var 0) (.var 0)]), (3, [.pair (.var 1) (.var 0)]),
   (2, [.join (.var 0) (.var 0)])]⟩
def goal : Goal := ⟨1, [(.pair (.var 7) (.tick (.var 9)),
  .pair (.var 7) (.tick (.var 10)))]⟩

-- Repeated ambient endpoint identity is distinct from local binders 0 and 1.
example : parentTable goal = [7, 9, 7, 10] := rfl
-- Duplicate where children and endpoint occurrences retain their exact order.
example : ((prepare id [] declaration goal id).bind id).map
    (fun r => r.owners.map Fin.val) = some [0, 0, 1, 0, 3, 0, 0, 0] := rfl
-- Independently inspecting the candidate gives the same ordered source names.
example : ((prepare id [] declaration goal id).bind id).map
    (fun r => childTable r.candidate) = some [7, 7, 9, 7, 10, 7, 7, 7] := rfl
-- Equal names share the original first root, distinct names do not.
example : (newRoot [7,9,7,10] [7,7,9] ⟨0,by decide⟩).val = 0 ∧
    (newRoot [7,9,7,10] [7,7,9] ⟨1,by decide⟩).val = 0 ∧
    (newRoot [7,9,7,10] [7,7,9] ⟨2,by decide⟩).val = 1 := by decide
-- Standalone lookup rejects missing names and handles empty finite domains.
example : (locate [7,7,9] [7,99]).isNone = true := rfl
example : (locate [] []).map List.length = some 0 := rfl
-- The three original outcome categories are preserved by the new entry.
example : prepare id [] ({ declaration with requirements := [(2,[.var 99])] })
    goal id = none := rfl
example : (prepare id [] declaration {goal with role := 99} id).map Option.isSome =
    some false := rfl
-- Structural positive returns need not have a model or a dictionary.
example : (prepare id [] ⟨1,0,[.var 0],[(2,[.var 0])]⟩
    ⟨1,[(.int,.pair .int .int)]⟩ id).map Option.isSome = some true := rfl
```

## Publication, preservation and recovery

integration/m1-finalをfetchし、GitHubからstanding ordersとinboxを再読した。I-4 ACTIVE、上限なし、I-11の25分上限を確認。開始時のintegrationとlive work/dots-mainはともに`8f9cbabf35327dae12a1f19a2b28ab3e7e026e5c`。前回cycle64はcompletedと対応報告があり、作業場はclean。復旧対象はなかった。integrationは既存local mergeの祖先で、最新取得後もAlready up to dateを確認した。

開始心拍`c9f6d02dd3cbf506b1f4d9e4993898496ea19f5a`を公開し、exact SHAをfetch/mergeした。sourceは6成果パスとrunning心拍の計7パスを、個別blobとSHA-only treeで準備し、一回のnon-force/expected-head ref更新で公開した。全blobはlocal git hashと一致。最新remote treeをbaseにし、他の内容は保全した。書込の拒否、結果不明、承認待ちはなかった。ローカルから全内容を一度に読む準備処理だけ出力上限に当たり、短い読み取りへ分けて回復した。外部書込の再送はしていない。

公開source commit: `ff2933dcd8d0daaaa13209725b8fd1fd1b70d828`。
source tree: `c71dec4736a6b16552a52f761c7bb91779a4d022`。

公開直後、live refと完全recursive treeを取り戻した。7変更blobのpath/mode/SHA一致、対象外2158blobの保持、全2165blob、truncationなしを確認。exact source SHAをローカルへfetch/mergeし、6成果パスの差分が空であることも確認した。他ブランチには書き込んでいない。

本報告とcompleted心拍は続けて公開し、最終treeを照合する。cycle全体の対象は8パス。最終SHA・照合結果は確認後に親へ返す。

## Yulang2 comparison and remaining B4 bridges

実装前にwork/dots-auditをfetchし、x-oracleのX13〜X16、C3-PARENT / C3-PARENT-NEGを読んだ。有限source ownershipや任意graph保持の一般定理の実機証明とはしない。新しいYulang2実行はしていない。spec 6.3と既存interval/captureの規則を保ち、新しい意味論の選択・質問ノートはない。

B4主定理の残り主要橋は**5本のまま**:
`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound`。

今回閉じたのは最初の2橋の中の「実parent captureから全where endpointの元ownerを計算し、実canonical graph allocationへ渡す」部分。一般source registryや再帰driver全体の閉包ではない。

次の候補:
1. 実childの再capture時のlocal binder source登録を、今回のendpoint ownerと一つのroot source tableに結び、再帰履歴を通したalias/root保持を証明する。
2. ordinary更新からのgraph再構築・inspectionの意味的十分性と、associated child feedbackを親の共有モデル・再生成へ接続する。
3. そのdriverを有限仕事領域・Paterson/K2の停止・意味的飽和へ接続する。

## Time and limits

予定開始2026-11-10T03:27:19Z、締切03:52:19Z。最初の環境dateは03:26:35Zで予定より約44秒早く復元を開始した。開始心拍のstarted/updatedは予定基準の03:27:19Z/03:27:26Zを書いたが、直後の環境dateは03:27:12Zだった。この初期時刻の微小なずれを記録する。source心拍updatedは実測03:34:12Z、約7分時点で公開した。

開始時とsource公開後の空きは48G（全63G、使用13G）。一つの作業場と既存cacheを再利用し、worktreeやcacheコピーを増やしていない。使用量枠は不明。I-11の部分目標が閉じたため、時間埋めの補題は追加しない。

## Exact source CI

source `ff2933dcd8d0daaaa13209725b8fd1fd1b70d828` のCIを監視中。03:34 UTC台には両方in_progressを確認した。
- core: https://github.com/momota1029/yulang/actions/runs/42750358607
- proof: https://github.com/momota1029/yulang/actions/runs/42750358233

2026-11-10T03:37:06Zに再確認し、exact source commitの**core / proofともcompleted / success**を確認した。以降は報告と心拍のみでLean sourceは変えていない。ローカル全体検証を行ったという意味ではない。

報告・完了心拍の準備は2026-11-10T03:37:06Z、予定開始から約9.8分。公開・最終tree照合を含めて終了する。
