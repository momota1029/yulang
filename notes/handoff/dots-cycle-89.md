# dots cycle 89 — 実宣言から再帰的な where 仕事領域を計算する

## 結果と部分目標

**既存のfirst-order Roles断片について、実際のwhere宣言から全再帰childを有限に列挙し、独立な宣言経路とのiff、生成に対する閉包、成功・欠如・曖昧の正確な分類を閉じた。**

新規 `CommonRoleGeneratedWhereClosure` は383行、24公開定理。今回は式constructorを増やすのでなく、callerが渡すvisit列・fuel・child listを使わない、実宣言からの再帰的な仕事領域を取った。根の成功を仮定しなくてもclosureを計算し、欠如したchildや曖昧な兄弟を残す。Patersonの減少は各再帰呼出しで既存の宣言検査から導く。

これは**first-order断片の部分目標**。Commonの区間状態が変わる飽和、K2の一般driver、associated where注釈の生成、全B4の完成ではない。主要橋は5本のまま。

## 量化と独立性

- 任意の有限 `List Roles.Impl`、任意のroot/target `Roles.Goal` を量化する。固定したlist例だけのiffではない。goal変数は既存モデルどおりrigidで、groundだけに限定していない。
- `Unique` はregistryへの所属・独立 `Matches`・他のmatching宣言が同じであること。`Edge` は実際のwhere memberと**任意のhead-matching substitution**からchildを導く。`Reach` はこの独立edge上の有限経路であり、closureやresolverを読み返して定義していない。
- `children` は既存unique-head規則とmatchingSubstで実whereを生成する。0候補・多候補ならそのnodeを残し、それより下へ展開しない。唯一候補の全兄弟を列挙するため、先の兄弟が失敗しても後の曖昧な兄弟が消えない。
- `closure` の入力にWF証明があることは明記する。外側の `checkedClassify` は既存 `CheckedRoles.checkDatabase` でこれを計算するので、callerに停止証明を要求しない。無関係な不正宣言も既存checkerどおり拒否する。
- リストは根を先頭に、where順に深さ優先で並べ、重複を残す。membershipのiffはoccurrence間の一意性・再訪の共有・binder identityを証明しない。
- `registerOne` のNatは**rootのprovenance owner**。childの型をparentのordinary slotと同一視するmapではない。実childのendpoint allocation、stateへの登録、source graphの等式は今回まだ閉じていない。
- `runSource` は新しいclassifierを使うchecked source入口で、既存の入口と文字どおり同じBoolを返す。grouped source、roles、scalar head関数は依然入力。cycle88の式inference入口を差し替えたり、関連型等式のsource生成を新たに証明したりしていない。
- 3分類はfirst-orderモデルに対するもの。全言語の保留・選択・曖昧・拒否の4分類やdictionaryの観察同値ではない。途中のstate-dependent曖昧を最終エラーにする規則は足していない。

## 主要定理

全て `Yulang.CommonRoleGeneratedWhereClosure`。以下のregistry/goalsは任意で、WFが必要な箇所は明示する。

1. `unique_exact`: 任意registry/root/implで、実候補リストが単一implであることと独立Uniqueがiff。`missing_exact`: 実候補リストが空であることと全registry宣言が非matchであることがiff。
2. `children_exact`: 任意WF registry/root/childで、実children所属と独立Edgeがiff。`edge_decreases`: 任意WF registryと独立Edgeで、child引数サイズがrootより真に小さい。
3. `closure_complete`, `closure_sound`, `closure_exact`: 任意WF registry/root/targetで、計算された有限closure所属と独立Reachがiff。成功・model・有限visit列を仮定しない。
4. `reach_trans`: 任意の二つの接続可能なReachの推移性。`generated_closed`: 任意WF registry、closure memberからの任意Edgeで、そのchildも同じclosureに属する。
5. `edge_resolves`, `reach_resolves`: 任意WF registry、EdgeまたはReach、rootの独立Resolvesからchildの独立Resolvesを得る。成功前提を持つ転送定理であり、無条件のchild成功ではない。
6. `closure_resolves`: 任意WF registry/rootで、全closure memberの独立Resolvesとrootの独立Resolvesがiff。
7. `resolve_unique_closure`: 任意WF registry/rootで、既存resolver成功と全closure memberが独立Uniqueを持つことがiff。
8. `overlap_reach`: 任意WF registry/rootで、既存ReachesOverlapと、独立Reachの終点にHeadOverlapがあることがiff。`ambiguous_exact`: 既存resolver曖昧と、closure memberで異なる2宣言が独立matchすることがiff。
9. `noImpl_exact`: 任意WF registry/rootで、既存resolverのnoImplと、全closureにoverlapがなく、少なくとも1memberで独立Missingがあることがiff。
10. `classify_eq_resolve`: 任意WF registry/rootで、有限closureを調べる新classifierと既存resolverが等しい。曖昧優先も保持する。
11. `registered_exact`: 任意WF registry/head関数/元obligation/owner/goalで、登録pair所属と「ownerが元root receiverで、独立Reachがある」がiff。`registered_resolves`: 任意の成功した元obligationの登録memberに独立Resolvesがある。
12. `run_one_agrees`, `run_source_agrees`: 任意WF registryと任意source入力で、new entryと既存entryのBoolが一致。`run_source_exact`: 任意WF registry/roles/grouped source/head関数で、trueとValidSource＋全元clauseの独立Dischargesがiff。
13. `checked_agrees`, `checked_exact`: 任意registry/rootで、WFを内部計算するclassifierが既存CheckedRoles.resolveに一致し、成功とWF＋独立Resolvesがiff。こちらはWFの前提がない。

既存Lean定義・定理は変更していない。Yulang/Audit import、全24定理のAudit登録、README、台帳Z節、coverage表、設計ノートとINDEXを更新した。

## 検証

最終production sourceに対し、以下はexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleGeneratedWhereClosure --wfail
✔ [291/291] Built Yulang.CommonRoleGeneratedWhereClosure (1.3s)
Build completed successfully (291 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang89/boundary-check.lean
exit 0
```

境界検査は41 examples。深さ20の再帰、rigid変数、空registry、未使用でも不正な宣言、同一implの重複、異なるkeyのoverlap、失敗した兄弟の後にoverlap、兄弟逆順、where childの重複、巨大source owner、裸role、wrong arity/associated member、unsupported bool/unit、空source、一般定理の使用を検査した。元の期待値は変えていない。

24定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleGeneratedWhereClosure.unique_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.children_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.edge_decreases' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.closure_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.closure_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.closure_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.reach_trans' does not depend on any axioms
'Yulang.CommonRoleGeneratedWhereClosure.generated_closed' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.edge_resolves' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.reach_resolves' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.closure_resolves' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.resolve_unique_closure' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.missing_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.overlap_reach' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.ambiguous_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.noImpl_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.classify_eq_resolve' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.registered_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.run_one_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.registered_resolves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.run_source_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.run_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.checked_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGeneratedWhereClosure.checked_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=256; Main=93; Audit=256; ledger mentioned=129. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 43390d548 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。最初のdiff gateは未commit LeanのためFAILだったが、明示pathsでcommitして再実行しPASS。初期proofのIH適用、未import tactic、Bool補題名、dependent match、scratchのRoleDecl proof-field/HeadOverlap Decidableを修正し、最終検査を再実行した。作業ディレクトリ指定を誤った一回の編集はFileNotFoundで何も変えなかった。最初の単純なshell background起動はログを残さなかったため、実session付きの短時間focused buildに切り替えた。失敗した試行を成功に数えない。

ローカル全体lake build、全Audit、AxiomGate、全体verifyは指示に従って実行していない。上のgateはdiff-only。追加定理の公理はpropext/Classical.choice/Quot.soundの範囲で、reach_transは無公理。独立レビューは未実施であり、実施済みとは数えない。

## 公開sourceとCI

source commit: `699549dcd23ca99a1bdd67bdb0d88612ffa517fd`。

- Core CI: completed / success; https://github.com/momota1029/yulang/actions/runs/42857016222
- Lean inference kernel: completed / success; https://github.com/momota1029/yulang/actions/runs/42857016256

このexact-source SHAを指定して再取得した結果。最終report/heartbeat commitのCIとは区別する。source公開後にproduction Leanを変更していない。未完のCIをPASSとは扱わない。

source tree `114ba6bd62baa2784ed338b07784da61315939f8` は2,325 entries、非truncated。9変更pathsのblob SHA一致、全treeもlocal checkpoint `a2087f398`と一致。work refをAPIで再確認し、明示tracking ref付きgit fetch後にもtree差分は空だった。

## 仕様、実機と残りの橋

新定義前にspec 6.2/6.3、既存Roles/RoleConstraints/CheckedRolesを読んだ。audit branchの `notes/audit/x-oracle.md` も新定義前に直接読んだ。C3-PARENTの両兄弟順・generic成功とC3-PARENT-NEGのchild欠如が既存の照合素材。今回のclassifierをYulang2実機で新規実行してはいない。既存oracleを今回の実機runや完全性証明として数えない。

新規質問ノート0件。既存first-order carrierの規則を使い、未回答のCommon意味論やinvocation sharingを決めなかった。I-13台帳Z節は追加したが全モジュールの意味監査は未完、期限超過解消も主張しない。

B4主定理への主要橋は5本:
1. `source_boundary_adequate`: 実parser/宣言からgrouped clause・annotation・scope名を導く一般橋は残る。
2. `generated_work_closed`: first-order actual whereの有限closureは今回閉じた。state-dependent childをordinary/source領域へ正しく登録する一般橋は残る。
3. `saturate_terminates_and_closes`: first-order Paterson closureは今回停止・閉包を証明したが、状態の絞り込みと再生成を含むPaterson/K2 driverは残る。
4. `saturated_frontier_exact`: first-orderの3分類は正確。全言語の独立な未完成診断treeと4分類は残る。
5. `resolve_dictionary_order_sound`: root provenanceやBool一致はdictionaryの観察同値ではない。

次の候補は(1) `CommonRoleWhereSourceAllocation.prepare` のstate-dependent実生成childを有限work driverへ結ぶ、(2) source roleのscalar inferenceとclosure登録を同じ実行入口で接続する、(3) 実宣言の関連型where注釈を落とさないcarrierからgrouped sourceを作ること。意味論が未決の箇所は入力として隠さず既存質問を確認する。

## 復旧、時刻、資源

- 開始2026-11-10T16:27:56Z。integration/workのliveはe36fa53b0。standing orders/inboxのACTIVEと上限なしを再読した。cycle88 completed heartbeat/reportあり。前writer/buildはなく、既存workspaceにintegrationをmergeした。clone/cacheは増やしていない。
- 最初のheartbeat e89a7e46 は16:29:34Zに公開。本文のupdatedを誤って16:32:01Z、elapsedを4.1と記載したため、最初の本文時刻は不正確。次の4ee8a0f1は実UTCを直接取得して16:37:39Zに記録し、16:37:44Zに公開した。source checkpointは16:41:03頃。以後の時刻は実時計から記録する。
- 個別blob8件は全SHA確認済み。live treeをbaseにSHA-only treeを作り、local全tree一致後にwork/dots-mainだけをforce=false/expected-headで更新した。外部writeの拒否・不確定結果なし。一括content uploadは使っていない。
- source/doc8 paths、heartbeat、最終reportの合計10 paths。integration/main等には書いていない。最終report/heartbeatも同じ方法で公開して照合する。
- 空きは開始時・16:41時点とも48G/63G（使用13G）。使用量の枠は不明。ログは../cache/yulang89。

報告作成時刻: 2026-11-10T16:44:05Z。経過16.2分。指定終了期限16:52:19Z。時間を埋めるための補題は追加していない。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleGeneratedWhereClosure
open Yulang
open Roles Roles.Examples
open CommonRoleGeneratedWhereClosure
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle89BoundaryCheck

def nested := display (list (list int))
example : closure goodImpls goodImpls_wellFormed nested =
    [nested, display (list int), display int] := by decide +kernel
example : classify goodImpls goodImpls_wellFormed nested = .resolved := by decide +kernel
example : checkedClassify goodImpls nested = .answer .resolved := by decide +kernel
example : checkedClassify goodImpls (display (list str)) = .answer .noImpl := by decide +kernel
example : closure goodImpls goodImpls_wellFormed (display (list str)) =
    [display (list str), display str] := by decide +kernel
example : closure goodImpls goodImpls_wellFormed (display (.var 5)) =
    [display (.var 5)] := by decide +kernel
example : checkedClassify goodImpls (display (.var 5)) = .answer .noImpl := by decide +kernel
example : checkedClassify [badImpl] (display int) = .invalidDeclarations := by decide +kernel
example : checkedClassify (badImpl :: goodImpls) (display int) = .invalidDeclarations := by decide +kernel
example : checkedClassify [] (display int) = .answer .noImpl := by decide +kernel
example : checkedClassify (goodImpls ++ goodImpls) nested = .answer .resolved := by decide +kernel
example : closure overlappingImpls overlappingImpls_wellFormed (display (list int)) =
    [display (list int)] := by decide +kernel
example : checkedClassify overlappingImpls (display (list int)) = .answer .ambiguous := by decide +kernel
example : closure [listImpl, specificStrImpl] failingOverlap_wellFormed (display (list str)) =
    [display (list str)] := by decide +kernel
example : checkedClassify [listImpl, specificStrImpl] (display (list str)) =
    .answer .ambiguous := by decide +kernel

def parent : Impl := ⟨2, [list int], [display int, foo int], 101⟩
def fooA : Impl := ⟨1, [int], [], 102⟩
def fooB : Impl := ⟨1, [int], [], 103⟩
def mixed : List Impl := [parent, fooA, fooB]
def root : Goal := ⟨2, [list int]⟩
theorem mixedWF : WellFormed mixed :=
  (CheckedRoles.checkDatabase_exact mixed).mp (by decide +kernel)
example : closure mixed mixedWF root = [root, display int, foo int] := by decide +kernel
example : classify mixed mixedWF root = .ambiguous := by decide +kernel
example : checkedClassify mixed root = .answer .ambiguous := by decide +kernel
example : (display int) ∈ closure mixed mixedWF root := by decide +kernel
example : (foo int) ∈ closure mixed mixedWF root := by decide +kernel
example : Missing mixed (display int) := (missing_exact mixed _).mp (by decide +kernel)
example : HeadOverlap mixed (foo int) := by unfold HeadOverlap; decide +kernel
example : ∃ i ∈ mixed, ∃ j ∈ mixed, i ≠ j ∧ Matches i (foo int) ∧ Matches j (foo int) :=
  (head_overlap_iff mixed _).mp (by unfold HeadOverlap; decide +kernel)

def reversed : List Impl := [{parent with constraints := [foo int, display int]}, fooA, fooB]
theorem reversedWF : WellFormed reversed :=
  (CheckedRoles.checkDatabase_exact reversed).mp (by decide +kernel)
example : closure reversed reversedWF root = [root, foo int, display int] := by decide +kernel
example : classify reversed reversedWF root = .ambiguous := by decide +kernel

def repeated : List Impl := [{parent with constraints := [display int, display int]}, intImpl]
theorem repeatedWF : WellFormed repeated :=
  (CheckedRoles.checkDatabase_exact repeated).mp (by decide +kernel)
example : closure repeated repeatedWF root = [root, display int, display int] := by decide +kernel
example : classify repeated repeatedWF root = .resolved := by decide +kernel

def tower : Nat → Term
  | 0 => int
  | n + 1 => list (tower n)
example : (closure goodImpls goodImpls_wellFormed (display (tower 20))).length = 21 := by decide +kernel
example : checkedClassify goodImpls (display (tower 20)) = .answer .resolved := by decide +kernel

def roles : RoleDecls := fun _ => ⟨1, fun _ => none, by intro n rhs h; cases h⟩
def clause : CommonRoleAssociatedClauseExtraction.Clause :=
  ⟨1000000, display (list (.var 0)), []⟩
def obligation : CommonRoleSourceRoleObligations.Obligation :=
  ⟨1000000, ⟨display (list (.var 0)), by decide⟩⟩
example : registerOne goodImpls goodImpls_wellFormed (fun _ => .int) obligation =
    [(1000000, display (list int)), (1000000, display int)] := by decide +kernel
example : runOne goodImpls goodImpls_wellFormed (fun _ => .int) obligation = true := by decide +kernel
example : runOne goodImpls goodImpls_wellFormed (fun _ => .str) obligation = false := by decide +kernel
example : runOne goodImpls goodImpls_wellFormed (fun _ => .bool) obligation = false := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles [clause] (fun _ => .int) = true := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles [clause, clause] (fun _ => .int) = true := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles [clause] (fun _ => .str) = false := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles [clause] (fun _ => .unit) = false := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles [] (fun _ => .unit) = true := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles
    [{clause with goal := ⟨0, []⟩}] (fun _ => .int) = false := by decide +kernel
example : runSource goodImpls goodImpls_wellFormed roles
    [{clause with equations := [⟨9, 7⟩]}] (fun _ => .int) = false := by decide +kernel
example (impls : List Impl) (g : Goal) : checkedClassify impls g = .answer .resolved ↔
    WellFormed impls ∧ RoleConstraints.Resolves impls g := checked_exact impls g
end Cycle89BoundaryCheck
#print axioms Yulang.CommonRoleGeneratedWhereClosure.unique_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.children_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.edge_decreases
#print axioms Yulang.CommonRoleGeneratedWhereClosure.closure_complete
#print axioms Yulang.CommonRoleGeneratedWhereClosure.closure_sound
#print axioms Yulang.CommonRoleGeneratedWhereClosure.closure_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.reach_trans
#print axioms Yulang.CommonRoleGeneratedWhereClosure.generated_closed
#print axioms Yulang.CommonRoleGeneratedWhereClosure.edge_resolves
#print axioms Yulang.CommonRoleGeneratedWhereClosure.reach_resolves
#print axioms Yulang.CommonRoleGeneratedWhereClosure.closure_resolves
#print axioms Yulang.CommonRoleGeneratedWhereClosure.resolve_unique_closure
#print axioms Yulang.CommonRoleGeneratedWhereClosure.missing_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.overlap_reach
#print axioms Yulang.CommonRoleGeneratedWhereClosure.ambiguous_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.noImpl_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.classify_eq_resolve
#print axioms Yulang.CommonRoleGeneratedWhereClosure.registered_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.run_one_agrees
#print axioms Yulang.CommonRoleGeneratedWhereClosure.registered_resolves
#print axioms Yulang.CommonRoleGeneratedWhereClosure.run_source_agrees
#print axioms Yulang.CommonRoleGeneratedWhereClosure.run_source_exact
#print axioms Yulang.CommonRoleGeneratedWhereClosure.checked_agrees
#print axioms Yulang.CommonRoleGeneratedWhereClosure.checked_exact
```
