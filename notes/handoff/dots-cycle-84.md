# dots cycle 84 — 元 source 名の安全な付け替えと衝突の境界

## 結果と部分目標

**有限 source の receiver/output と named scalar 入力を任意の単射で付け替えても、独立な導出、source-name model の存在、再検査・再割当て・再飽和した外側 readiness が一致することを閉じた。**

新規 `CommonRoleNamedSourceRenaming` は167行、公開10定理とprivateな逆写像定義・補助証明。`run_source_rename` は成功実行、選択済み package、ordinary State、slot の写像、十分な fuel、選んだ model を前提にしない。core wf と associated awf、既存の有限断片の範囲、および source 名の写像が単射であることは明示した前提である。

開始時の第一案は Parent 宣言の where から source を生成する橋だった。調査した `Roles.Impl.constraints : List Goal` には、`CommonRoleAssociatedClauseExtraction.Clause` のreceiver/output source名と関連等式が入っていない。`Roles.AssocImpl.assoc` は宣言の関連型bodyであり、その where 注釈ではない。これらを単に射影して Parent/Left/Right の生成を達成したとすることはできないため、その実装は開始しなかった。境界を設計ノートへ残し、I-4 の source identity の独立した部分目標へ切り替えた。

**元の宣言生成の部分目標は未完。改めた「source identity の単射な名前変更に対する外側 exactness」は完了。** B4 の主要な橋は5本のまま。時間を埋めるだけの補題は追加していない。

## なぜ単射が必要か

`renameSource` は receiver と関連等式のoutputだけを変える。role ID、関連member ID、Goal内の局所binderは変えない。既存の同じsource名は同じ新名になり、単射なら別名が混ざらない。

境界検査で次の両方を確認した:
- 別々のreceiver名にstrとintを与えるsourceはreadiness=true。両名を0に潰すと矛盾した等式が一つの名へ入り、falseになる。
- 未知receiver7に対し無関係な入力99:strだけならfalse。両名を0に潰すと、その無関係な入力で解けてtrueになる。

したがって任意の名前変更が安全なのではない。単射という前提は実際の衝突を排除する。今回の定理は全Nat上の単射を十分条件とし、有限support上だけの最小条件やその実行可能checkerは作っていない。source invocationの共有・寿命を決めたものでもない。cycle70の既存の共有境界とcandidate guard問題は未解決のまま。

## 定理の量化範囲と効く側

以下は任意のenv/roles/source/input、source名、scalar head/result、該当clause/equationに対する一般定理。具体例だけの成立ではない。

1. `step_rename` — 任意の名前写像fについて、元clause/equationの独立Stepと、名前変更後のStepが同値。補助・関連等式の意味保存。
2. `valid_clause_rename` — 任意f/roles/clauseで妥当性が同値。補助・checkerの前提保存。
3. `valid_source_rename` — 任意f/roles/sourceでsource全体の妥当性が同値。補助。
4. `names_rename` — 任意f/source/nameについて、新source domainの所属と元domainの名前の像であることが同値。補助・source起源の完全性。
5. `derives_rename` — 任意fに沿って、元の独立導出を新しい名前へ運べる。健全性側の保存。逆向きは主張しない。
6. `derives_original` — 単射fに対し、新しい任意の独立導出は元の名前と導出を持つ。健全性側の反映・生成物の起源。
7. `derives_rename_exact` — 単射fで、新しいf(name)の独立導出と元nameの独立導出が同値。健全性・完全性。
8. `models_rename_exact` — 単射fで、新旧source-name Modelsが同値。健全性・完全性。wf/awfも実行成功も不要、valuationは存在結論の中で構成する。
9. `discharge_rename` — 任意f/impls/clause/scalarで、固定scalarに対する独立Dischargesが同値。補助。
10. `run_source_rename` — 任意env/rolesと明示したwf/awf、単射f、source/inputで、両方を再実行したBool readinessが等しい。健全性・完全性のexactnessから得る観察保存。全言語の主型性や辞書の観察同値ではない。

private `originalName` と `original_image` はmodel証明用の逆写像witness。実行版には使わない。既存の定理、Lean定義、spec、plan、lake設定は変更していない。

## 検証

最終sourceで以下は全てexit 0:

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleNamedSourceRenaming --wfail
✔ [293/293] Built Yulang.CommonRoleNamedSourceRenaming (1.0s)
Build completed successfully (293 jobs).

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang84/boundary-check.lean
exit 0
```

境界検査は23 examples。100のoffsetでの名前変更、Goal/member IDの保存、関連型伝播、未知receiver、矛盾、bool/unit、空source、scope外binder、不正な関連member、重複、任意source/inputへの一般定理の利用、衝突による結果の両方向の変化を検査した。

10定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleNamedSourceRenaming.step_rename' depends on axioms: [propext]
'Yulang.CommonRoleNamedSourceRenaming.valid_clause_rename' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.valid_source_rename' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.names_rename' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.derives_rename' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.derives_original' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.derives_rename_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.models_rename_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedSourceRenaming.discharge_rename' depends on axioms: [propext]
'Yulang.CommonRoleNamedSourceRenaming.run_source_rename' depends on axioms: [propext, Classical.choice, Quot.sound]

```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=251; Main=93; Audit=251; ledger mentioned=124. Mention counts are not audit completion counts.

```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0):

```text
verify-lean: . @ 832f26e3c (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```

`git diff --check`もexit 0。最初の実行は作業directoryとELAN_HOMEの組合せが誤っていてtoolchainを見つけられず、lean directoryの既存toolchainへ直した。最初のLean試行は帰納ケースのbinder名、古典的な逆像選択、簡約後の等式、membership変数の衝突を修正して再実行した。成功期待値を実装に合わせて変更していない。

公理はpropext / Classical.choice / Quot.soundのみ。全体lake build、全Audit、AxiomGate、全体verifyはローカルでは行っていない。

## 公開sourceのCI

公開source `5ee5288e98117d5d655964e9640feae44e26d252` のCore CIとLean inference kernelは、14:10 UTCの再取得でともにcompleted/success。

- Core CI: https://github.com/momota1029/yulang/actions/runs/42831101593
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42831101486

これはそのexact source commitのCI結果。ローカルで全体verifyを実行したという意味ではない。最終報告commitのCIとは区別する。

## Yulang2との照合

開始時にwork/dots-auditをfetchし、`notes/audit/x-oracle.md`のC3-PARENT（左右両順とgeneric成功）、C3-PARENT-NEG（missing child拒否）を再読した。spec/06-roles.md §6.3の関連等式・兄弟連言と合わせてsource境界の背景とした。

今回の数値source名の単射変更は証明interfaceの表現の変更であり、Yulang2実機の新しい言語挙動とは扱わない。新しい実機run、Rust parser検査、実sourceのalpha変換の意味保存は実行・証明していない。

## 受け入れ条件、残る橋、次の候補

I-4のsource identity、I-13のcaller入力の台帳を進めた。I-13はU節へ追記しinventoryを更新したが、全モジュール監査は未完で、cycle72の元期限超過を解消したとは書かない。新規質問ノート0件。既存Q1/Q2とcycle23/24は未決のまま。

主要橋は5本:
1. `source_boundary_adequate`。今回、既存finite sourceの安全な名前変更は閉じた。parser、式からの仮定、whereの関連等式を持つ宣言sourceからの生成は残る。
2. `generated_work_closed`。dynamic whereの生成と登録の全体は未完。
3. `saturate_terminates_and_closes`。一般Paterson/K2 driverへの停止・閉包の橋は残る。
4. `saturated_frontier_exact`。四方向の最終分類は未完。
5. `resolve_dictionary_order_sound`。Bool readinessの名前変更不変性は辞書の観察同値ではない。

次の候補:
- 元whereの関連等式を保存する権威あるsource carrierを確認し、receiver/output名を保つ宣言生成の独立判断を先に書く。
- 名前つきscalar仮定を確定済みの注釈/式から導くsource lowering。
- 必要なsource生成が具体化した段階で、単射性を有限support上で計算し、今回の全Nat上の前提を不要にする。

## 復旧、公開、資源、時刻

- 開始2026-11-10T13:57:54Z。`date -u`記録は13:58:23Z。live integration/workは両方34920e105。最新standing orders/inboxを取得しACTIVEと上限なしを確認した。
- 前cycle83はcompleted、対応reportあり。残存writer/build processなし。作業treeと公開integrationは一致していたため追加clone/cacheコピーなし。integrationをローカルへmergeし、祖先関係exit 0。
- 開始心拍341f85f0を公開。約10分の心拍とsourceを5ee5288eへ公開。8 source/doc pathsとheartbeat、計9 paths。すべてindividual blob → SHAだけのtree、live treeをbaseとして保全、parentをlive head、force=falseとexpected headで更新。
- 公開treeを再取得。2310 entries、非truncated、全変更pathのSHA一致。tree全体`fe3c2825b6bd5aeefdb3a6496ebd4aa4cb21c19e`がローカルと同じ。最初のgit fetchはFETCH_HEADのみだったため、explicit tracking ref付きで再取得し、全tree equalityと空diffを確認した。
- 最終reportとcompleted heartbeatも同じ保全方式で公開し再取得する。source/doc8 paths、report/heartbeatを合わせて成果物10 paths。integration/main/その他枝への書込みなし。
- 空き容量は開始時・14:09時点とも48G / 63G、使用13G。使用量の枠は不明。公開の拒否・承認待ち・不確定なwriteはない。

報告作成時刻: 2026-11-10T14:12:23Z。経過14.5分。閉じた部分目標、focused検証、source公開照合、exact-source CIが揃い、残りは最終reportの公開照合のみ。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleNamedSourceRenaming
open Yulang CommonRoleNamedSourceEntry CommonRoleNamedSourceRenaming
open CommonRoleAssociatedClauseExtraction (Clause Source)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle84BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed
def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def bare : Clause := ⟨7, goal, []⟩
def associated : Clause := ⟨3, goal, [⟨0, 7⟩]⟩
def src : Source := [associated, bare]
def input : Assumptions := [(3, .str)]
def shift (n : Nat) : Nat := n + 100
theorem shift_injective : Function.Injective shift := by intro a b h; simp [shift] at h; exact h

example : (renameClause shift associated).goal = goal := rfl
example : (renameClause shift associated).equations = [⟨0, 107⟩] := rfl
example : (renameClause shift associated).receiver = 103 := rfl
example : names (renameSource shift src) = [103, 107, 103, 107] := by decide
example : runSource env roles wf (renameSource shift src) (renameInput shift input) = true := by decide +kernel
example : runSource env roles wf (renameSource shift src) input = false := by decide +kernel
example : runSource env roles wf (renameSource shift src) (renameInput shift []) = false := by decide +kernel
example : runSource env roles wf (renameSource shift src) (renameInput shift [(3, .str), (7, .int)]) = false := by decide +kernel
example : runSource env roles wf (renameSource shift [bare]) (renameInput shift [(7, .bool)]) = false := by decide +kernel
example : runSource env roles wf (renameSource shift [bare]) (renameInput shift [(7, .unit)]) = false := by decide +kernel
example : runSource env roles wf (renameSource shift []) (renameInput shift [(7, .str), (7, .int)]) = true := by decide +kernel
example : runSource env roles wf
    (renameSource shift [{bare with goal := ⟨2, [.var 2, .app 0 []]⟩}])
    (renameInput shift [(7, .str)]) = false := by decide +kernel
example : runSource env roles wf
    (renameSource shift [{associated with equations := [⟨99, 7⟩]}])
    (renameInput shift input) = false := by decide +kernel
example : runSource env roles wf (renameSource shift [bare, associated, bare])
    (renameInput shift [(3, .str), (3, .str)]) = true := by decide +kernel

-- General theorem covers every source/input and recomputes both allocations.
example (source : Source) (assumptions : Assumptions) :
    runSource env roles wf (renameSource shift source) (renameInput shift assumptions) =
      runSource env roles wf source assumptions :=
  run_source_rename shift shift_injective env roles wf awf source assumptions
example (source : Source) (assumptions : Assumptions) (name : Nat) (head : Inference.Base) :
    Derives env roles (renameSource shift source) (renameInput shift assumptions) (shift name) head ↔
      Derives env roles source assumptions name head :=
  derives_rename_exact shift shift_injective env roles source assumptions name head
example (source : Source) (assumptions : Assumptions) :
    Models env roles (renameSource shift source) (renameInput shift assumptions) ↔
      Models env roles source assumptions :=
  models_rename_exact shift shift_injective env roles source assumptions

-- A collision merges independent scalar equations and changes readiness.
def separate : Source := [⟨3, goal, []⟩, bare]
def separateInput : Assumptions := [(3, .str), (7, .int)]
example : runSource env roles wf separate separateInput = true := by decide +kernel
example : runSource env roles wf (renameSource (fun _ => 0) separate)
    (renameInput (fun _ => 0) separateInput) = false := by decide +kernel
example : runSource env roles wf (renameSource (fun _ => 0) separate)
    (renameInput (fun _ => 0) separateInput) ≠ runSource env roles wf separate separateInput := by decide +kernel

-- Collisions can also manufacture readiness from an unrelated input name.
example : runSource env roles wf [bare] [(99, .str)] = false := by decide +kernel
example : runSource env roles wf (renameSource (fun _ => 0) [bare])
    (renameInput (fun _ => 0) [(99, .str)]) = true := by decide +kernel

-- No claim about arbitrary name maps is hidden inside exactness.
example : ¬ Function.Injective (fun _ : Nat => 0) := by
  intro h
  have impossible : (0 : Nat) = 1 := h rfl
  omega
end Cycle84BoundaryCheck
#print axioms Yulang.CommonRoleNamedSourceRenaming.step_rename
#print axioms Yulang.CommonRoleNamedSourceRenaming.valid_clause_rename
#print axioms Yulang.CommonRoleNamedSourceRenaming.valid_source_rename
#print axioms Yulang.CommonRoleNamedSourceRenaming.names_rename
#print axioms Yulang.CommonRoleNamedSourceRenaming.derives_rename
#print axioms Yulang.CommonRoleNamedSourceRenaming.derives_original
#print axioms Yulang.CommonRoleNamedSourceRenaming.derives_rename_exact
#print axioms Yulang.CommonRoleNamedSourceRenaming.models_rename_exact
#print axioms Yulang.CommonRoleNamedSourceRenaming.discharge_rename
#print axioms Yulang.CommonRoleNamedSourceRenaming.run_source_rename

```
