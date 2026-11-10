# dots cycle 81 — bare role を失わない有限 source 境界

## 結果と部分目標

**関連型の等式が一つもない clause を含め、有限 source の全 role 義務を保持し、実行可能な検査・解決と独立な source 判断を双方向で結ぶ部分目標を閉じた。**

新しい `CommonRoleSourceRoleObligations` は 244 行、定理は 15 本。各 clause に一つの checked role obligation を残し、cycle80 の関連等式列も順序・重複を含めて完全に保持する。`runSource` は検査から role 実行までを計算し、主定理 `run_source_exact` は成功した checker や caller の validity 証明を前提にしない。where の兄弟の任意の並べ替えについて実行結果が同じであることも証明した。

これは既存の一つの placeholder と int/str の有限断片。`heads : Nat → Base` は明示的な入力のままで、source 式の推論から導いていない。関連等式の飽和状態が持つ evidence との対応も未証明。したがって、関連等式の伝播と role test を一体化した全 source の型付け、一般の B4、最終診断を完成としない。主要な B4 の橋は **5 本のまま**。

## 量化範囲と定理の側

`Source`、`Clause`、`Equation` は cycle80 の有限 carrier を再利用する。`RawObligation` は receiver 名と goal、`Obligation` は receiver 名と scope 検査済み Template。`Package` は全 clause の obligation 列と、既存の equation Program を持つ。

- `valid_equations`（補助）: 任意の total role registry と source について、全 clause の scope・arity・関連名が有効なら、既存の関連等式 projection の全行も有効。
- `erase_build`（補助）: 任意の registry、source とその validity 証明について、生成した obligation 列の erasure は source の receiver/goal 列と完全に等しい。空関連等式の clause、順序、重複も残る。
- `erase_injective`、`eraseList_injective`（補助）: 任意の checked obligation、または任意のその列について、erasure が等しければ元も等しい。
- `check_exact`（健全性・完全性）: 任意の registry、source、package について、check がその package を返すことと、role 列の正確な erasure、関連等式列の正確な erasure、全 source clause の validity の三つが同値。
- `check_accepts`、`check_fails`（健全性・完全性）: 任意の registry/source について、受理と全 clause の validity が同値。失敗と、無効な具体的 source clause が存在することが同値。
- `checked_equations`（補助）: 任意の成功検査について、その package の equation 部分は cycle80 の checker が返す program と等しい。既存の source derivation と飽和の定理を再利用できる証明を得るが、新しい role test との状態整合性は主張しない。
- `checked_count`、`checked_occurs`（補助／健全性・完全性）: 任意の成功検査について、obligation 数は source clause 数に等しい。任意の raw receiver/goal について、package 内に対応する obligation が存在することと、source に対応する clause が存在することが同値。
- `run_one_exact`（健全性・完全性）: 任意の impl 列とその WellFormed、任意の scalar head map、obligation と同じ erasure の source clause について、実行が true となることと、encode・独立 Fills・独立 Resolves による `Discharges` が同値。
- `run_roles_exact`（健全性・完全性）: 同じ impl/wf/head map、任意の registry/source と成功検査で返った package について、全 role 実行の成功と、元 source の全 clause の独立 discharge が同値。
- `missing_role_blocks`（健全性側）: 同じ前提のもと、source 内の一つの clause が独立に discharge できなければ、role test は false。関連等式が空でも義務を消して成功にしない。
- `run_source_exact`（健全性・完全性）: 任意の impl/wf/registry/source/head map について、public entry の true と、全 source clause の validity および全 clause の独立 discharge が同値。成功検査の前提は不要。
- `run_source_permutation`（補助）: 任意の同じ impl/wf/registry/head map と、任意の permutation 関係の二つの source 列について、public entry の Bool が等しい。

これらは上記の断片の健全性・完全性または補助定理であり、全言語の主型性の証明ではない。scope ≤ 1、int/str encoder、caller の head map は実装断片の境界で、仕様が新たに拒否すると決めた範囲ではない。

## 忠実性、受け入れ条件、未達

spec 6.1–6.2 の signature、6.3 の全 where 義務と兄弟の連言に従う。関連等式を持たない不正 arity の clause は cycle80 の空 projection では受理され得たが、新しい whole-clause checker では拒否される。これは失われていた検査の保持であり、bare role の辞書が存在すると勝手に仮定する変更ではない。

total registry は role 999 にも signature を返し得る。syntax check の受理は visibility や辞書の存在を示さない。bool/unit の head は既存の encoder の外側であり、receiver を使わない constant goal でもこの制限が残る。これを回帰で明記した。false はこの有限 test の結果で、pending/ambiguous/rejected の最終分類ではない。spec 6.3 の安定後の最終化へつないだとは主張しない。

I-4/I-7 の橋 1 にある有限 source の欠落を縮めたが、完全な `Parent (box 'a)` の外側の T1c 主張や X13–X16 の外側入口の完成ではない。I-13 には R 節として新しい入力を全列挙した。head map の将来の導出は安定状態からの evidence adapter が必要と記録した。台帳の全体監査は未完、cycle72 の期限超過も残る。新規質問は 0 件。既存 Q1/Q2 と cycle23/24 の意味論の判断を仮定として隠していない。

## 検証

実行した最終 source の検証はすべて exit 0。

```text
cd lean
ELAN_HOME=../../elan ../../elan/bin/lake build Yulang.CommonRoleSourceRoleObligations --wfail
✔ [290/290] Built Yulang.CommonRoleSourceRoleObligations (1.1s)
Build completed successfully (290 jobs).

ELAN_HOME=../../elan ../../elan/bin/lake env lean --trust=0 ../../cache/yulang81/boundary-check.lean
exit 0
```

境界検査は **40 examples と 5 named helpers**（wf、checked、discharge、emptyWf、missingIndependent）。空 source、bare clause、関連等式との混在、重複、逆順、途中の不正 arity、scope、関連名、role 999、辞書なし、実際の再帰 where 解決、欠けた子、overlap、bool/unit、constant goal の encoder 境界を確認した。独立 Fills/Resolves から作った witness を reverse bridge に通す例も含む。

15 定理の trust=0 公理出力全文:

```text
'Yulang.CommonRoleSourceRoleObligations.valid_equations' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.erase_build' depends on axioms: [propext]
'Yulang.CommonRoleSourceRoleObligations.erase_injective' depends on axioms: [propext]
'Yulang.CommonRoleSourceRoleObligations.eraseList_injective' depends on axioms: [propext]
'Yulang.CommonRoleSourceRoleObligations.check_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.check_accepts' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.check_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.checked_equations' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.checked_count' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.checked_occurs' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.run_one_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.run_roles_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.missing_role_blocks' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.run_source_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceRoleObligations.run_source_permutation' depends on axioms: [propext, Quot.sound]
```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=248; Main=93; Audit=248; ledger mentioned=121. Mention counts are not audit completion counts.
```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0):

```text
verify-lean: . @ bfc43f5f5 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

最初の diff gate は commit 前の lean/ 変更を検出して exit 1。source を commit した後、上記の通り再実行して通った。`git diff --check` も exit 0。公理は propext / Classical.choice / Quot.sound のみ。全体 build、全 Audit、AxiomGate、全体 verify は実行していない。監督役の検証が必要。

## Yulang2 との照合

開始時に `work/dots-audit` を fetch し、`x-oracle.md` の C3-PARENT（両順と generic 成功）および C3-PARENT-NEG（missing child 拒否）を読んだ。audit ref は `55574b6052ef1534fd0fc36d6d3617ebede59a0e`。これは conjunctive where の意味論の参考で、この新しい Lean carrier の直接の oracle ではない。新しい Yulang2 実機または Rust parser は実行していない。

## 復旧、公開、時刻、資源

- 開始記録は 2026-11-10T12:27:58Z。最新 inbox は ACTIVE、最大 cycle 数なし。開始時の live integration と work はともに `cc721e2dbf114d767e187bae7a0b39a83a2d08ab`。取得して統合し、その tree がローカルと同じことを確認した。
- 前回 cycle80 は recovered/completed 心拍と report があり、書き込みプロセスなし。今回新しい crash 記録は不要。既存の一つの clone と cache を継続し、worktree や build cache は増やしていない。
- 設計 commit `32c30af0e`、実装 commit `bfc43f5f5`。開始心拍を `139be211f63ea71ea0a4662b481e5a5964b7f9d5` に公開。10 分の checkpoint は 12:38:29Z 更新、12:39:03Z までに source と一緒に公開した。blob 公開のため時刻が約 1 分遅れたことを記録する。
- 途中公開 `7c3ef3dc5699ea347df19da0bdcc29b4a6dcc938` は 9 paths。GitHub から recursive tree `0109fded3df92db278a3dff161fe36e44d5e19bc`（2301 entries、非 truncated）を取得し、local tree SHA と一致、変更 9 paths の blob SHA も全て一致した。公開済みとローカル検証済みの tree 差分は空。
- 各 blob を個別に作り、SHA だけの tree を live base tree から作成。既存 head を親にして expected-head、force=false で更新した。書き込みは work/dots-main のみ。integration、main 等には書き込んでいない。
- 途中公開の exact-head CI は Core CI success、Lean inference kernel in_progress（run 42817565095）。全体 CI の成功は主張しない。最終 report 公開後の exact-head CI は別途確認する。
- 最終 report と completed 心拍を含め、integration からの公開差分は 10 paths になる。この記録の後に最終公開と tree 照合を行い、その実結果を親へ返す。
- 開始時と報告時の空きはともに 48G / 全63G、使用13G。使用量の枠は不明。外部書き込みの拒否や未確定の branch 更新はない。ローカル読み出しの JSON 出力が長すぎた際は ensure_ascii=False で読み直し、成功を確認した。これは公開 API の retry ではない。
- 報告作成: 2026-11-10T12:41:21Z、開始から 13.4 分。I-11 の 25 分上限内で部分目標を閉じ、残りは最終公開・照合。

## 残る B4 の橋と次候補

`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound` の **5 本が未完**。

1. `heads` を安定した source state の evidence から導き、role test と associated saturation の state を対応させる。bare receiver が equation table に無い場合も扱う。
2. finite source の外側にある registry・visibility・Rust AST からの構築を明示し、dynamic child に接続する。未決の identity 問題を勝手に決めない。
3. I-13 の未監査 module の入力台帳を継続する。

## 再現用境界検査

```lean
import Yulang.CommonRoleSourceRoleObligations
open Yulang CommonRoleSourceRoleObligations
open CommonRoleAssociatedClauseExtraction (Clause Source)
namespace Cycle81BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson

def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def bare : Clause := ⟨3, goal, []⟩
def associated : Clause := ⟨3, goal, [⟨0, 7⟩, ⟨0, 9⟩]⟩
def missing : Clause := ⟨7, ⟨999, goal.args⟩, []⟩
def src : Source := [bare, associated]
def heads : Nat → Inference.Base := fun _ => .str

def p : Package := build roles src (by decide)
theorem checked : check roles src = some p := by
  unfold check
  split
  · rfl
  · rename_i h
    exact False.elim (h (by decide))

example : p.obligations.length = 2 := checked_count roles src p checked
example : p.equations.length = 2 := by decide
example : (p.obligations.map erase) = src.map raw := ((check_exact roles src p).mp checked).1
example : (check roles []).isSome = true := by decide +kernel
example : (check roles [bare]).isSome = true := by decide +kernel
example : (check roles [bare, bare]).isSome = true := by decide +kernel
example : (check roles [associated, bare]).isSome = true := by decide +kernel
example : (build roles [bare, bare] (by decide)).obligations.length = 2 := by decide
example : (build roles [bare] (by decide)).equations.length = 0 := by decide
example : (check roles [missing]).isSome = true := by decide +kernel
example : (build roles [bare, missing, associated] (by decide)).obligations.length = 3 := by decide
example : (build roles [bare, missing, associated] (by decide)).equations.length = 2 := by decide
example : (check roles [{bare with goal := ⟨2, [.var 0]⟩}]).isNone = true := by decide +kernel
example : (check roles [{bare with goal := ⟨2, [.var 1, Roles.Examples.int]⟩}]).isNone = true := by decide +kernel
example : (check roles [bare, {bare with goal := ⟨2, [.var 0]⟩}, associated]).isNone = true := by decide +kernel
example : (check roles [{associated with equations := [⟨99, 7⟩]}]).isNone = true := by decide +kernel
example : CommonRoleAssociatedClauseExtraction.check roles src = some p.equations :=
  checked_equations roles src p checked

-- The old equation-only projection accepts this empty projection; the full
-- clause boundary correctly refuses an invalid signature without erasing it.
example : (CommonRoleAssociatedClauseExtraction.check roles
    [{bare with goal := ⟨2, [.var 0]⟩}]).isSome = true := by decide +kernel

example : runSource env.cores wf roles [] heads = true := by decide +kernel
example : runSource env.cores wf roles [bare] heads = true := by decide +kernel
example : runSource env.cores wf roles src heads = true := by decide +kernel
example : runSource env.cores wf roles [associated, bare] heads = true := by decide +kernel
example : runSource env.cores wf roles [bare, bare] heads = true := by decide +kernel
example : runSource env.cores wf roles [missing] heads = false := by decide +kernel
example : runSource env.cores wf roles [bare, missing, associated] heads = false := by decide +kernel
example : runSource env.cores wf roles [associated, missing, bare] heads = false := by decide +kernel
example : runSource env.cores wf roles [{bare with goal := ⟨2, [.var 0]⟩}] heads = false := by decide +kernel

-- Independent structural witness, followed by the reverse executable bridge.
theorem discharge : Discharges env.cores heads bare := by
  refine ⟨Roles.Examples.str, Roles.AssocExamples.index
    (Roles.AssocExamples.box Roles.Examples.str) Roles.Examples.int, rfl, rfl, ?_, ?_⟩
  · exact .cons (.app (.cons .hole .nil)) (.cons (.app .nil) .nil)
  · exact (RoleConstraints.resolve_exact _ wf _).mp Roles.AssocExamples.box_resolved
example : runSource env.cores wf roles [bare] heads = true :=
  (run_source_exact env.cores wf roles [bare] heads).mpr
    ⟨by decide, by intro c h; simpa using (show Discharges env.cores heads c from by
      simpa only [List.mem_singleton.mp h] using discharge)⟩

theorem emptyWf : Roles.WellFormed [] := by simp [Roles.WellFormed]
theorem missingIndependent : ¬ Discharges [] heads bare := by
  rintro ⟨_, g, _, _, _, resolves⟩
  exact RoleConstraints.empty_resolver_has_no_evidence g resolves
example : runSource [] emptyWf roles [bare] heads = false := by decide +kernel
example : ¬ runSource [] emptyWf roles [bare] heads = true := by
  intro h
  exact missingIndependent (((run_source_exact [] emptyWf roles [bare] heads).mp h).2 bare (by simp))

example : runSource env.cores wf roles [bare] (fun _ => .bool) = false := by decide +kernel
example : runSource env.cores wf roles [bare] (fun _ => .unit) = false := by decide +kernel
example : runSource env.cores wf roles [bare, associated] heads =
    runSource env.cores wf roles [associated, bare] heads :=
  run_source_permutation env.cores wf roles _ _ (List.Perm.swap _ _ []) heads
example : runRoles [] emptyWf heads p = false := by
  apply missing_role_blocks [] emptyWf roles src p checked heads bare (by simp [src])
  exact missingIndependent

-- Real recursive where resolution is still required by a bare source clause.
def unaryDecl : Roles.RoleDecl where
  arity := 1
  assoc := fun _ => none
  defaultsScoped := by intro _ _ h; contradiction
def unaryRoles : Roles.RoleDecls := fun _ => unaryDecl
def recursive : Clause := ⟨3, Roles.Examples.display
  (Roles.Examples.list (Roles.Examples.list (.var 0))), []⟩
example : runSource Roles.Examples.goodImpls Roles.Examples.goodImpls_wellFormed
    unaryRoles [recursive] (fun _ => .int) = true := by decide +kernel
example : runSource Roles.Examples.goodImpls Roles.Examples.goodImpls_wellFormed
    unaryRoles [recursive] heads = false := by decide +kernel
example : (build unaryRoles [recursive] (by decide)).equations = [] := rfl
example : runSource Roles.Examples.overlappingImpls Roles.Examples.overlappingImpls_wellFormed
    unaryRoles [⟨3, Roles.Examples.display (Roles.Examples.list (.var 0)), []⟩]
    (fun _ => .int) = false := by decide +kernel

-- Even a constant goal is inside the explicit int/str scalar materialization
-- interface; a bool source head is not silently given new meaning.
def constant : Clause := ⟨3, Roles.Examples.display Roles.Examples.int, []⟩
example : runSource Roles.Examples.goodImpls Roles.Examples.goodImpls_wellFormed
    unaryRoles [constant] (fun _ => .str) = true := by decide +kernel
example : runSource Roles.Examples.goodImpls Roles.Examples.goodImpls_wellFormed
    unaryRoles [constant] (fun _ => .bool) = false := by decide +kernel
end Cycle81BoundaryCheck
#print axioms Yulang.CommonRoleSourceRoleObligations.valid_equations
#print axioms Yulang.CommonRoleSourceRoleObligations.erase_build
#print axioms Yulang.CommonRoleSourceRoleObligations.erase_injective
#print axioms Yulang.CommonRoleSourceRoleObligations.eraseList_injective
#print axioms Yulang.CommonRoleSourceRoleObligations.check_exact
#print axioms Yulang.CommonRoleSourceRoleObligations.check_accepts
#print axioms Yulang.CommonRoleSourceRoleObligations.check_fails
#print axioms Yulang.CommonRoleSourceRoleObligations.checked_equations
#print axioms Yulang.CommonRoleSourceRoleObligations.checked_count
#print axioms Yulang.CommonRoleSourceRoleObligations.checked_occurs
#print axioms Yulang.CommonRoleSourceRoleObligations.run_one_exact
#print axioms Yulang.CommonRoleSourceRoleObligations.run_roles_exact
#print axioms Yulang.CommonRoleSourceRoleObligations.missing_role_blocks
#print axioms Yulang.CommonRoleSourceRoleObligations.run_source_exact
#print axioms Yulang.CommonRoleSourceRoleObligations.run_source_permutation
```
