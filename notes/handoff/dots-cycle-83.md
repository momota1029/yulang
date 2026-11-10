# dots cycle 83 — named source から検査・割当て・飽和・全 role 検査まで

## 結果と部分目標

**有限な元 source と名前つき scalar 仮定の列を受け取り、source の妥当性検査、全 slot の割当て、初期 ordinary 等式、関連型の飽和、ordinary consistency、全 role 義務の検査を内側で計算する外側入口を閉じた。**

新規 `CommonRoleNamedSourceEntry` は 295 行、公開 14 定理と private な割当て補助 1 本。cycle82 の入口で caller が渡していた、検査済み `Package` とその table 長に依存する `State` を、今回の `runSource` は要求しない。`run_source_exact` の独立な側には Package、slot、ordinary State、実行版の solver/saturator がない。元 source の `ValidSource`、名前だけの `Models`、各元 clause の独立な receiver 導出と `Discharges` の連言である。

さらに `run_source_congr` は、元 clause と scalar 仮定の membership が等しければ readiness が一致することを証明した。任意の順序変更だけでなく重複の追加・除去を含み、両側の allocation と初期 state は別々に計算される。caller に state の再割当てやその正しさの証明を渡させない。

これは **明示的な名前つき scalar 等式だけを初期制約に持つ有限断片** の入口である。任意の初期 ordinary 制約や effect 制約を保存する入口は cycle82 のまま残し、弱めたり置き換えたりしていない。scalar 仮定を実際の式の型付けから導くことは未完。scope-resolved source、scope ≤ 1、int/str の role materialization、core WellFormed、AssocWellFormed は依然として明示した境界である。B4 の主要な橋は **5 本のまま**。

## 独立な意味と境界

`Derives env roles src input name head` の規則は、名前つき仮定の membership と、元 clause/equation の独立 `Step` だけ。初期 scalar の total map、実行済み graph、成功結果を使わない。`Models` は元 source に現れる名前について、導出される全 scalar を満たす一つの source-name type valuation の存在である。モデルを caller が選ぶ前提はない。

この断片では source に現れない名前の仮定は解釈の対象外。空 source に無関係な矛盾した仮定を渡しても readiness は true になる。これはインターフェースの明示した対象領域で、実言語で未使用の注釈を許すか、scope error とするかを決めたものではない。実 source annotation からこの境界への lowering は未証明。`names` の正確性は元 receiver と equation endpoint のみに対して証明した。

bool/unit は scalar evidence として保持するが既存 role encoder の範囲外。未知 receiver は一意な impl があるだけでは決まらない。false はこの readiness 検査が通らないという結果で、言語の rejected/pending/ambiguous へ勝手に分類しない。通常の scalar entailment、dynamic where、visibility、K2、最終診断は未達。

## 定理の量化範囲と役割

以下は固定例ではなく、任意の有限 source/package/input、任意の該当 slot/head/valuation に関する主張。wf/awf は実 resolver を使う定理で明記した前提。

1. `initial_facts_exact` — 任意の package/input/slot/head で、計算した初期 fact membership と、その slot の元の名前を持つ仮定 membership が同値。補助。
2. `initial_evidence_exact` — 同じ任意の入力で、生成した ordinary state の paired Evidence と named 仮定が同値。健全性・完全性。
3. `initial_models_exact` — 任意の package/input と全 occurrence valuation について、初期 ordinary atoms のモデルと全 named 仮定の等式が同値。健全性・完全性。
4. `table_names_exact` — checker が受理した任意の source/package について、任意の名前の table membership と元 source domain membership が同値。補助・生成の忠実性。
5. `receiver_present` — 同じ受理済み source の任意の clause に、同じ名前を持つ実 allocated receiver slot が存在する。補助。
6. `allocated_to_named` — 任意の package/input と cycle82 の元 source 導出から、割当てや State を持たない名前の独立導出を得る。健全性。
7. `named_to_allocated` — 任意の受理済み source/package/input と独立な名前の導出から、その名前を持つ全 slot で cycle82 の導出を得る。完全性。
8. `run_evidence_exact` — 任意の env/roles、wf/awf、受理済み source/package/input、slot/head について、実飽和の Evidence と元の名前だけの `Derives` が同値。健全性・完全性。
9. `models_exact` — 任意の受理済み source/package/input について、cycle82 の独立 allocated model と元 source-name `Models` が同値。健全性・完全性。実行結果も wf/awf もこの補題には不要。
10. `ready_exact` — 任意の env/roles、wf/awf と受理済み source/package/input について、生成 state の実 readiness と、独立 Models および全 clause の独立 discharge が同値。健全性・完全性。
11. `run_source_exact` — 任意の env/roles、wf/awf、未検査の有限 source/input について、外側実行の true と、source validity・独立 Models・全元 clause の derived receiver と discharge が同値。検査成功、Package、State、十分な fuel、成功実行は前提でない。健全性・完全性。この断片の主定理で、全言語の主型性ではない。
12. `derives_transport` — 任意の二つの source/input と membership の包含に沿い、全 name/head の独立導出を移せる。補助。
13. `names_member` — 任意の source/name について、元 domain にあることと元 clause receiver または equation output に現れることが同値。補助。
14. `run_source_congr` — 任意の env/roles、wf/awf、二つの source/input に対し、両 membership が同値なら外側 readiness が等しい。一般の順序・重複不変性。補助であり、全言語の辞書の観察同値ではない。

private `named_table_member` は既存 `NamedAssociatedGraph.table` が各元 equation の receiver/output をちょうど表すことを示す。

## 検証

次は最終 source で全て exit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleNamedSourceEntry --wfail
✔ [292/292] Built Yulang.CommonRoleNamedSourceEntry (1.3s)
Build completed successfully (292 jobs).

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang83/boundary-check.lean
exit 0
```

境界検査は **28 examples、5 named helpers**。source からの allocation、bare receiver、unknown receiver、関連式の結果による bare receiver の解決、矛盾した仮定、派生結果との矛盾、重複と逆順、bool/unit、辞書なし、不正 arity、scope 外の変数、不正な関連名、空 source、無関係な仮定を含む。独立 `Step` の declaration witness と named seed から `independentPropagation` を組み、逆方向の evidence 定理を通した。general congruence の具体利用も確認した。

14 定理の trust=0 公理出力全文:

```text
'Yulang.CommonRoleNamedSourceEntry.initial_facts_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.initial_evidence_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.initial_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.table_names_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.receiver_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.allocated_to_named' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.named_to_allocated' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.run_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.ready_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.run_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.derives_transport' depends on axioms: [propext]
'Yulang.CommonRoleNamedSourceEntry.names_member' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleNamedSourceEntry.run_source_congr' depends on axioms: [propext, Classical.choice, Quot.sound]

```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=250; Main=93; Audit=250; ledger mentioned=123. Mention counts are not audit completion counts.

```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0):

```text
verify-lean: . @ 543873505 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```

`git diff --check` も exit 0。最初の focused build で list membership の証明を修正した。境界検査の独立導出で head の明示が足りなかったため修正して再実行した。期待する true/false は変更していない。最初の diff gate は commit 前だったため uncommitted Lean を検出して FAIL、検証済み source を commit 後に上記 PASS を確認した。最初のバックグラウンド起動は実行されなかったため、timeout 付きの追跡可能な実行へ切り替えた。

公理は propext / Classical.choice / Quot.sound のみ。全体の lake build、全 Audit、AxiomGate、全体 verify はローカルで実行していない。監督役の全体検証が必要。

## Yulang2 との照合

`work/dots-audit` を fetch し、`notes/audit/x-oracle.md` の C3-PARENT（両順/generic 成功）と C3-PARENT-NEG（missing child 拒否）を新しい定義の前に再読した。where の連言と順序独立の背景として使った。今回の named scalar 入力、source checker、無関係な入力の境界を Yulang2 の実機で検証したとは主張しない。新しい実機実行、Rust parser、全言語の実装検査は行っていない。

## 受け入れ条件、残る橋、次の候補

I-4/I-7 の橋1にある実 source 境界を、受理済み Package と依存 State を caller から受けない有限入口へ進めた。I-4 の source identity と兄弟順序独立もこの断片で閉じた。一般 B4、完全な Parent/Left/Right の source inference、X13–X16 の外側完成、主型性の完成は主張しない。

主要橋は 5 本:
1. `source_boundary_adequate`。今回、有限 source と named scalar 仮定の外側 readiness が進んだ。実構文、式からの制約、visibility、一般 knownness への接続は残る。
2. `generated_work_closed`。dynamic where の生成と登録は未完。
3. `saturate_terminates_and_closes`。有限 graph の停止を一般 Paterson/K2 の driver へ持ち上げる橋が残る。
4. `saturated_frontier_exact`。四方向の最終分類は未完。
5. `resolve_dictionary_order_sound`。今回の Bool の順序不変性は全 where 辞書の観察同値ではない。

次の候補は (a) 実 source の確定済み scalar 注釈/式から named assumptions を導く忠実な lowering、(b) 一つの実 Parent declaration の where clauses をこの有限入口へ生成する橋、(c) 一般 ordinary 制約を source 名で受け取り今回の入口と統合する適切な scope。いずれも仕様が答えを持たない境界を勝手に決めない。

I-13 台帳 T 節へ全新規 caller 入力と内部で導出した入力を追記し inventory を更新。全モジュール監査はまだ未完で、cycle72 の期限超過を解消したとは書かない。既存 Q1/Q2 と cycle23/24 は未決、新規の意味論質問は 0 件。

## 復旧、公開、資源、時刻

- 開始は 2026-11-10T13:27:02Z。cache/start.txt は13:27:33Z。live integration `6498a62e`、work `e995611e` を確認し、最新版 standing orders/inbox を読み、ACTIVE・上限なしを確認した。前 cycle82 は completed で report も存在、前の writer はいなかった。
- 一つの clone と既存 cache を継続。integration merge の競合は前 cycle の report と heartbeat のみ。まず supervisor 版を優先して merge `1bde90dac`、その後既に work に公開されている cycle82 の正しい CI追記を復元した。新しい意味や未公開作業を消していない。Lean の競合はなかった。crash 復旧は不要。
- 設計 commit `0c7e4fccf`、検証済み source commit `543873505`。開始 heartbeat は `995faf3d`、10分 heartbeat は `2c5c4f04`（updated 13:37:17Z）。途中のローカル checkpoint は `71b80deb8`。
- 途中公開は `a5d5d03c46a638f3dab74f403167c54d22b3dc31`、tree `06b170b3be3276ec454fd05eb5df032ddaa2ddab`。8 個の source/doc blob を一つずつ作成し、各 SHA を local git blob と照合。SHA-only tree を live tree から作り、live head を親として expected-head/force=false で work/dots-main のみを更新した。
- 公開 recursive tree は2307 entries、非 truncated。全変更 path の SHA が一致し、全 tree SHA もローカルと一致。git で公開 head を取得し、ローカルとの差分が空であることを13:39:40Zに確認した。
- 13:41:58Z、上記 exact source commit の Core CI と Lean inference kernel がともに completed/success であることを確認した。Lean の proof job は build、全宣言 audit、source/value/regular/semantic record examples の各 step が success。Core CI: https://github.com/momota1029/yulang/actions/runs/42826542627 。Lean: https://github.com/momota1029/yulang/actions/runs/42826542548 。これは公開 source の CI 結果で、ローカルで全体 verify を実行したという意味ではない。
- 開始時と13:40時点の空きは48G / 全63G、使用13G。回復 worktree、追加 clone、コピーされた build cache は作っていない。使用量の枠は不明。
- final report と completed heartbeat は同じ保全方式で公開して再取得・照合する。source/doc 8 paths と report/heartbeat を合わせた今回の成果物は10 paths。integration/main/その他の枝への書込みはない。

報告作成時刻: 2026-11-10T13:42:35Z。開始から 15.6 分。部分目標と公開 source の CI まで完了し、残る作業は最終報告の公開照合のみ。

## 再実行用の境界検査全文

```lean
import Yulang.CommonRoleNamedSourceEntry
open Yulang CommonRoleNamedSourceEntry
open CommonRoleAssociatedClauseExtraction (Clause Source)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle83BoundaryCheck

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

example : names src = [3, 7, 3, 7] := by decide
example : runSource env roles wf src input = true := by decide +kernel
example : runSource env roles wf src [] = false := by decide +kernel
example : runSource env roles wf [bare] [] = false := by decide +kernel
example : runSource env roles wf [bare] [(7, .str)] = true := by decide +kernel
example : runSource env roles wf [bare] [(7, .int)] = true := by decide +kernel
example : runSource env roles wf [bare] [(7, .bool)] = false := by decide +kernel
example : runSource env roles wf [bare] [(7, .unit)] = false := by decide +kernel
example : runSource env roles wf [bare] [(7, .str), (7, .int)] = false := by decide +kernel
example : runSource env roles wf src [(3, .str), (7, .int)] = false := by decide +kernel
example : runSource env roles wf src [(3, .str), (7, .str)] = true := by decide +kernel
example : runSource env roles wf [bare, associated] input = true := by decide +kernel
example : runSource env roles wf [bare, bare, associated] input = true := by decide +kernel
example : runSource env roles wf [associated, associated, bare] input = true := by decide +kernel
example : runSource env roles wf src [(3, .str), (3, .str)] = true := by decide +kernel
example : runSource env roles wf [] [] = true := by decide +kernel
-- Assumptions outside the finite source domain are explicitly irrelevant.
example : runSource env roles wf [] [(99, .str), (99, .int)] = true := by decide +kernel
example : runSource env roles wf src [(3, .str), (99, .int), (99, .str)] = true := by decide +kernel
example : runSource env roles wf [bare] [(99, .str)] = false := by decide +kernel
-- Validation is computed, not given by a dependent-package caller.
example : runSource env roles wf [{bare with goal := ⟨2, [.var 0]⟩}] [(7, .str)] = false := by decide +kernel
example : runSource env roles wf [{bare with goal := ⟨2, [.var 2, .app 0 []]⟩}] [(7, .str)] = false := by decide +kernel
example : runSource env roles wf [{associated with equations := [⟨99, 7⟩]}] input = false := by decide +kernel
def missing : Clause := ⟨7, ⟨999, goal.args⟩, []⟩
example : runSource env roles wf [missing] [(7, .str)] = false := by decide +kernel

theorem independentStep : CommonRoleAssociatedClauseExtraction.Step env roles associated ⟨0, 7⟩ .str .str := by
  refine ⟨Roles.Examples.str, Roles.AssocExamples.index
    (Roles.AssocExamples.box Roles.Examples.str) Roles.Examples.int, rfl, rfl, ?_, ?_,
    Roles.Examples.str, ?_, rfl⟩
  · exact .cons (.app (.cons .hole .nil)) (.cons (.app .nil) .nil)
  · exact (RoleConstraints.resolve_exact _ wf _).mp Roles.AssocExamples.box_resolved
  · exact .explicit Roles.AssocExamples.boxImpl (fun _ => Roles.Examples.str)
      (by simp [env, Roles.AssocExamples.singletonEnv]) rfl rfl
      (by intro c h; cases h) (.var 0) rfl


-- The independent side starts from a named seed and a declaration witness.
theorem independentPropagation : Derives env roles src input 7 .str := by
  apply Derives.equation associated ⟨0, 7⟩ (head := .str) (by simp [src]) (by simp [associated])
  · exact .initial (by simp [input, associated])
  · exact independentStep

def p := CommonRoleSourceRoleObligations.build roles src (by decide)
theorem checked : CommonRoleSourceRoleObligations.check roles src = some p := by
  unfold CommonRoleSourceRoleObligations.check
  split
  · rfl
  · rename_i h; exact False.elim (h (by decide))
example : CommonRoleOrdinaryKnownness.Evidence
    (CommonRoleSourceStateDischarge.runState env roles wf p (initialState p input)).atoms
    (CommonRoleSourceStateDischarge.roleSlot p ⟨1, by decide⟩) .str :=
  (run_evidence_exact env roles wf awf src p checked input _ .str).mpr independentPropagation
example : Models env roles src input :=
  ((run_source_exact env roles wf awf src input).mp (by decide +kernel)).2.1
example : ∀ c ∈ src, ∃ head, Derives env roles src input c.receiver head ∧
    CommonRoleSourceRoleObligations.Discharges env.cores (fun _ => head) c :=
  ((run_source_exact env roles wf awf src input).mp (by decide +kernel)).2.2
example : runSource env roles wf src input = runSource env roles wf [bare, associated] input :=
  run_source_congr env roles wf awf src [bare, associated] input input
    (by intro c; simp [src, or_comm]) (by intro f; rfl)
example : runSource env roles wf src [(3, .str), (7, .str)] =
    runSource env roles wf src [(7, .str), (3, .str), (3, .str)] :=
  run_source_congr env roles wf awf src src _ _ (by intro c; rfl)
    (by intro f; simp [or_comm])
end Cycle83BoundaryCheck
#print axioms Yulang.CommonRoleNamedSourceEntry.initial_facts_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.initial_evidence_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.initial_models_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.table_names_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.receiver_present
#print axioms Yulang.CommonRoleNamedSourceEntry.allocated_to_named
#print axioms Yulang.CommonRoleNamedSourceEntry.named_to_allocated
#print axioms Yulang.CommonRoleNamedSourceEntry.run_evidence_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.models_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.ready_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.run_source_exact
#print axioms Yulang.CommonRoleNamedSourceEntry.derives_transport
#print axioms Yulang.CommonRoleNamedSourceEntry.names_member
#print axioms Yulang.CommonRoleNamedSourceEntry.run_source_congr

```
