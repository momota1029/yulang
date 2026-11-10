# dots cycle 85 — 有限 source support の衝突検査と exactness

## 結果と部分目標

**source と input から有限な名前領域を計算し、その上での衝突を実行可能な検査で排除すれば、名前変更後の独立な導出、source model の存在、再検査・再割当て・再飽和した readiness が元と一致することを閉じた。**

cycle84 の `Function.Injective f` という全 Nat 上の前提を、実際に使用する有限領域の検査へ置き換えた。新規 `CommonRoleFiniteSourceRenaming` は187行、公開9定理。`renameChecked` は安全な source/input の組を返すか、衝突時に none を返す。`checked_readiness` は任意の env/roles/wf/awf/src/input/f と検査の成功に対して成り立つ。solver の成功、選ばれた package、普通の State、model、fuel、global injectivity の証明は入力にしない。

**この source identity の部分目標は完了。宣言生成は未完で、B4 の主要橋は5本のまま。** core/associated registry の wf/awf と既存の scalar/one-binder の有限断片は引き続き前提である。新たな言語意味論や invocation の共有規則は選んでいない。

## 検査する領域と境界

support は source の receiver/output 名と、全 input assumption の名前の連結。source だけで検査してはならない。receiver7 が未知で、無関係な input17:str だけを渡す場合、mod10 で両者を7へ潰すと false が true に変わる。その map は今回の検査で拒否される。

同じ名前の重複は衝突ではない。mod10 は全 Nat では非単射だが、source/input が3と7だけを使用するときは検査を通り、readiness を保つ。反射定理の query name も support 所属を要求する。support 外の17を query として持ち込めば7へ潰れうるため、無条件な反射にはしていない。

検査は十分条件であり、readiness Bool がたまたま一致するための必要条件ではない。source が空なら、input3:str と13:int が潰れても両方の readiness は true だが、保守的な検査は拒否する。none は表現変更の衝突であり、言語の rejected 診断ではない。

## 定理の量化範囲と効く側

各定理は固定した例だけでなく、任意の有限 src/input、名前写像f、指定の env/roles/name/head に対するもの。

1. `check_exact`: Bool検査=true と、計算したsupport上の任意のa,bについて f a=f b→a=b が同値。補助・検査の健全性/完全性。
2. `check_fails`: Bool検査=false と、support中の異なるa,bが同じ像を持つことが同値。補助・衝突の独立な証拠。
3. `derives_supported`: 任意の独立 Derives の結論名はsource/inputのsupportに属する。補助・source起源。
4. `derives_original`: 有限 CollisionFree を前提に、名前変更後の任意の導出は元の名前と独立導出を持つ。健全性側の反映。
5. `derives_exact`: 有限 CollisionFree とqueryのsupport所属を前提に、新旧の独立導出が同値。健全性/完全性。
6. `models_exact`: 有限 CollisionFree で新旧のsource Modelsが同値。健全性/完全性。valuationを存在量化の中で構成する。
7. `run_source_exact`: 有限 CollisionFree と明示的なwf/awfで、再計算した新旧readiness Boolが等しい。健全性/完全性から得る観察保存。
8. `rename_checked_exact`: 任意の出力source/inputについて、チェック付き名前変更の成功と、有限CollisionFreeおよび出力が名前変更結果であることが同値。補助・実行入口。
9. `checked_readiness`: その実行可能検査を通った任意の出力について、wf/awfの下で新旧readinessが等しい。健全性/完全性。外部の単射性証明を不要にした入口。

private `originalName`/`original_image` はsupport中の逆像を選ぶ証明用のwitness。実行版では使わない。全言語の主型性、辞書の観察同値、最終四方向分類を証明したものではない。

## 検証

最終sourceで次は全てexit 0:

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleFiniteSourceRenaming --wfail
✔ [294/294] Built Yulang.CommonRoleFiniteSourceRenaming (2.3s)
Build completed successfully (294 jobs).

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang85/boundary-check.lean
exit 0
```

境界検査は29 examples。非単射なmod10の受理、衝突の拒否、source外inputのcapture、重複、矛盾、空source、未知receiver、関連memberの不正、Goal/member IDの保存、supported queryの必要性と、任意入力に対する一般定理の利用を検査した。成功期待値の変更はしていない。

9定理のtrust=0公理出力全文:

```text
'Yulang.CommonRoleFiniteSourceRenaming.check_exact' depends on axioms: [propext]
'Yulang.CommonRoleFiniteSourceRenaming.check_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFiniteSourceRenaming.derives_supported' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFiniteSourceRenaming.derives_original' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFiniteSourceRenaming.derives_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFiniteSourceRenaming.models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFiniteSourceRenaming.run_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFiniteSourceRenaming.rename_checked_exact' depends on axioms: [propext]
'Yulang.CommonRoleFiniteSourceRenaming.checked_readiness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=252; Main=93; Audit=252; ledger mentioned=125. Mention counts are not audit completion counts.
```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0):

```text
verify-lean: . @ 71c711d51 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。最初のLean試行ではfalse検査の簡約、予約語を使った局所変数名、Option出力の簡約を修正した。境界検査では未対応のnamespace略記を完全名に直した。エラーのあった試行をPASSとは数えない。

公理はpropext / Classical.choice / Quot.soundのみ。全体lake build、全Audit、AxiomGate、全体verifyはローカルでは実行していない。diff gateのPASSはdiff-only。

## 公開sourceのCI

公開source `032d0e1c844b5b613590bae219ba4be112d974b4` のCore CIとLean inference kernelは14:37 UTCの再取得でcompleted/success。

- Core CI: https://github.com/momota1029/yulang/actions/runs/42835816637
- Lean inference kernel: https://github.com/momota1029/yulang/actions/runs/42835816855

これはexact source commitのCI結果で、最終report/heartbeat commitのCIとは区別する。source公開後にLeanコードは変更していない。

## Yulang2との照合

開始時にwork/dots-auditを取得し、x-oracleのC3-PARENT（左右両順とgeneric成功）とC3-PARENT-NEG（missing child拒否）を再読。spec/06-roles.md §6.3の関連等式と兄弟連言を背景として確認した。今回の有限数値名の検査は表現境界であり、新しい言語挙動とは扱わない。新規Yulang2実機run、Rust parser適合、宣言sourceのalpha変換の意味保存は未実行/未証明。

## 受け入れ条件と残りの橋

I-4のsource identityを進め、I-13のV節とinventoryを更新した。I-13の全モジュール監査は未完で、元のcycle72期限超過を解消したとは主張しない。新規質問ノート0件。既存Q1/Q2、cycle23/24は未決。

B4の主要橋は5本:
1. `source_boundary_adequate`: 今回は既存有限sourceの計算可能な安全な名前変更を閉じた。宣言/式からsourceとinputを抽出する橋は残る。
2. `generated_work_closed`: 動的where子の生成と登録は未完。
3. `saturate_terminates_and_closes`: 一般Paterson/K2 driverの停止と閉包は未完。
4. `saturated_frontier_exact`: 独立な最終四方向分類は未完。
5. `resolve_dictionary_order_sound`: 今回のBool保存は辞書の観察同値ではない。

次の候補:
- where関連等式のreceiver/output同一性を保持する権威ある宣言carrierを確認し、独立な抽出判断を作る。`Roles.Impl.constraints : List Goal`だけでは元の注釈を持たないというcycle84の境界は変わらない。
- 確定済みの注釈/式からnamed scalar inputを導くsource lowering。
- 実際のloweringが算出する名前mapを今回の有限checkerへ接続する。invocation共有の未決境界は決めない。

## 復旧、公開、資源、時刻

- 開始2026-11-10T14:27:52Z。live integration/workはともに0924f7cc。最新standing orders/inboxを取得してACTIVEと上限なしを確認した。
- 前cycle84はcompletedでreportあり。残存writer/buildなし。integrationを既存作業treeへmergeし、祖先関係と元のtreeを確認した。追加clone/cacheコピーなし。
- 開始心拍d5fbc195を公開。開始心拍のupdatedを実時刻より先に記した記録上の誤りは、中間source公開時に実測UTC時刻へ修正した。作業開始時刻はclockの値で一貫している。
- 約9分の中間公開032d0e1cで、8 source/doc pathsとheartbeatを原子的に公開した。個別blob upload → SHAのみのtree、live treeをbaseとして保全、live parentに対してforce=falseとexpected headでrefを更新。承認待ち、拒否、不確定なwriteはない。
- 公開treeは2313 entries、非truncated、変更9pathのSHAが全一致。tree全体68e0c4104feebe08fc2fa87d9e018990c8c03b2fはローカルHEADと一致し、再fetch後のgit diffも空。integration等への書込みなし。
- 最終report/heartbeatも同じ方法で公開し再取得する。成果物は合計10 paths。ローカル検証ログと境界検査は../cache/yulang85にあり、境界検査全文は本報告に含む。
- 空き容量は開始と14:37時点とも48G / 63G（使用13G）。使用量の枠は不明。

報告作成時刻: 2026-11-10T14:39:06Z。経過11.2分。閉じた部分目標、focused検証、source公開照合、exact-source CIは完了。残りは最終reportの公開照合。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleFiniteSourceRenaming
open Yulang CommonRoleNamedSourceEntry CommonRoleNamedSourceRenaming
open CommonRoleAssociatedClauseExtraction (Clause Source)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle85BoundaryCheck

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
def mod10 (n : Nat) : Nat := n % 10

-- A globally non-injective map passes on computed finite support.
example : ¬ Function.Injective mod10 := by
  intro h
  have impossible : (0 : Nat) = 10 := h (by decide)
  omega
example : CommonRoleFiniteSourceRenaming.check mod10 src input = true := by decide
example : CommonRoleFiniteSourceRenaming.renameChecked mod10 src input = some (renameSource mod10 src, renameInput mod10 input) := by decide
example : runSource env roles wf (renameSource mod10 src) (renameInput mod10 input) = true := by decide +kernel
example : CommonRoleFiniteSourceRenaming.check (fun _ => 0) src input = false := by decide
example : CommonRoleFiniteSourceRenaming.renameChecked (fun _ => 0) src input = none := by decide

-- Input-only names must be included; otherwise unrelated seeds can be captured.
example : CommonRoleFiniteSourceRenaming.check mod10 [bare] [(17, .str)] = false := by decide
example : runSource env roles wf [bare] [(17, .str)] = false := by decide +kernel
example : runSource env roles wf (renameSource mod10 [bare]) (renameInput mod10 [(17, .str)]) = true := by decide +kernel
example : CommonRoleFiniteSourceRenaming.renameChecked mod10 [bare] [(17, .str)] = none := by decide

-- Duplicates are identities, not collisions. Different live names are checked.
example : CommonRoleFiniteSourceRenaming.check mod10 [bare, bare] [(7, .str), (7, .str)] = true := by decide
example : CommonRoleFiniteSourceRenaming.check mod10 [bare] [(7, .str), (7, .int)] = true := by decide
example : runSource env roles wf (renameSource mod10 [bare])
    (renameInput mod10 [(7, .str), (7, .int)]) = false := by decide +kernel
example : CommonRoleFiniteSourceRenaming.check mod10 [⟨3, goal, []⟩, ⟨13, goal, []⟩] [] = false := by decide

-- The condition is sufficient, not necessary for equality of readiness Bools.
example : CommonRoleFiniteSourceRenaming.check mod10 [] [(3, .str), (13, .int)] = false := by decide
example : runSource env roles wf [] [(3, .str), (13, .int)] = true := by decide +kernel
example : runSource env roles wf (renameSource mod10 [])
    (renameInput mod10 [(3, .str), (13, .int)]) = true := by decide +kernel
example : CommonRoleFiniteSourceRenaming.check (fun _ => 0) [] [] = true := by decide
example : CommonRoleFiniteSourceRenaming.check mod10 src [] = true := by decide
example : runSource env roles wf (renameSource mod10 src) [] = false := by decide +kernel

-- Receiver/output identities change, but role/member IDs and Goal binders do not.
example : (renameClause mod10 associated).goal = goal := rfl
example : (renameClause mod10 associated).equations = [⟨0, 7⟩] := rfl
example : CommonRoleFiniteSourceRenaming.check mod10 [{associated with equations := [⟨99, 7⟩]}] input = true := by decide
example : runSource env roles wf (renameSource mod10 [{associated with equations := [⟨99, 7⟩]}])
    (renameInput mod10 input) = false := by decide +kernel

-- General statements: no preselected package, valuation, fuel or solver success.
example (source renamed : Source) (assumptions renamedInput : Assumptions)
    (f : Nat → Nat) (h : CommonRoleFiniteSourceRenaming.renameChecked f source assumptions = some (renamed, renamedInput)) :
    runSource env roles wf renamed renamedInput = runSource env roles wf source assumptions :=
  CommonRoleFiniteSourceRenaming.checked_readiness f source renamed assumptions renamedInput h env roles wf awf
example (source : Source) (assumptions : Assumptions) (f : Nat → Nat)
    (h : CommonRoleFiniteSourceRenaming.check f source assumptions = true) :
    Models env roles (renameSource f source) (renameInput f assumptions) ↔
      Models env roles source assumptions :=
  CommonRoleFiniteSourceRenaming.models_exact f ((CommonRoleFiniteSourceRenaming.check_exact f source assumptions).mp h) env roles
example (source : Source) (assumptions : Assumptions) (f : Nat → Nat)
    (h : CommonRoleFiniteSourceRenaming.check f source assumptions = true) (name : Nat)
    (member : name ∈ CommonRoleFiniteSourceRenaming.support source assumptions) (head : Inference.Base) :
    Derives env roles (renameSource f source) (renameInput f assumptions) (f name) head ↔
      Derives env roles source assumptions name head :=
  CommonRoleFiniteSourceRenaming.derives_exact f ((CommonRoleFiniteSourceRenaming.check_exact f source assumptions).mp h) env roles name member head

-- Unsupported query names may collide from outside; reflection is restricted.
example : ¬ Derives env roles [bare] [(7, .str)] 17 .str := by
  intro derived
  have absent : 17 ∉ CommonRoleFiniteSourceRenaming.support [bare] [(7, .str)] := by decide
  exact absent (CommonRoleFiniteSourceRenaming.derives_supported env roles [bare] [(7, .str)] 17 .str derived)
example : Derives env roles (renameSource mod10 [bare])
    (renameInput mod10 [(7, .str)]) (mod10 17) .str := by
  exact .initial (by decide)

end Cycle85BoundaryCheck
#print axioms Yulang.CommonRoleFiniteSourceRenaming.check_exact
#print axioms Yulang.CommonRoleFiniteSourceRenaming.check_fails
#print axioms Yulang.CommonRoleFiniteSourceRenaming.derives_supported
#print axioms Yulang.CommonRoleFiniteSourceRenaming.derives_original
#print axioms Yulang.CommonRoleFiniteSourceRenaming.derives_exact
#print axioms Yulang.CommonRoleFiniteSourceRenaming.models_exact
#print axioms Yulang.CommonRoleFiniteSourceRenaming.run_source_exact
#print axioms Yulang.CommonRoleFiniteSourceRenaming.rename_checked_exact
#print axioms Yulang.CommonRoleFiniteSourceRenaming.checked_readiness
```
