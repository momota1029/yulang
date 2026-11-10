# dots cycle 79 — finite raw associated program の検査と厳密な保存

## 結果と部分目標

**有限の raw associated 義務列から、scope・宣言 arity・関連名を検査して構造 program を生成する境界を閉じた。**
`CommonRoleCheckedAssociatedPrograms`（178行）は proof field の無い `RawOccurrence` と
有限 `RawProgram` を受け、検査成功 iff 全行が有効かつ生成 program の erasure が入力列と等しいことを証明した。
失敗 iff 無効な入力行が存在する。行・順序・receiver/output 名・関連名・goal を落としたり変更したりしない。
重複行や source 名の共有もそのまま残す。

[ソース公開 f2e5857e](https://github.com/momota1029/yulang/commit/f2e5857e49469fa77d6bf55f220623bae08d9bcd)
の tree `2444f7d0b0eca458b4fd7b49cce93f99d50ab38b` は local 検証 commit
`792adaa4dd420fbe72ffc5e84a51ce0b0ec6602b` と完全一致する。recursive tree の全2294 entriesと
全9変更 pathの blob SHA を再取得して照合した。最終報告・心拍は記録のみで Lean source を変えない。

生成された各 goal が検査済みの arity と関連名を保つことも示した。
model/solver 接続の2定理は cycle78 の独立導出と exactness を再利用し、入力列の厳密な保存を添える。
**新しい raw-source 宣言的意味論や parser adequacy を証明したわけではない。**
全言語の主型性、動的 where、一般 interval knownness、最終四分類と辞書順は未完。
B4 の主要橋は5本のまま。新しい言語意味論の選択0、既存定理の変更0、新規質問0。

## 量化範囲と定理の側

共通入力は任意 `roles : Roles.RoleDecls`、任意有限 `raw : RawProgram`。
RawOccurrence は scope 解決済み receiver/output 名、関連名、任意の `Roles.Goal` を持つ。
`Valid` は placeholder scope bound ≤1、引数個数 = 既存 role 宣言の arity、関連名の宣言 membership。
registry は既存の total 関数であり、role 可視性の検査とは異なる。

- `erase_ofValid`（補助）: 任意 raw 行とその有効性証拠から構築した行を消去すると元の行。
- `erase_injective`, `eraseProgram_injective`（補助）: 任意の2行/2 programについて、erasure が同じなら元も同じ。
- `erase_build`（補助）: 任意有限 raw と全行の有効性証拠について、構築された program の erasure は raw。
- `check_exact`（健全性・完全性）: 任意 roles/raw/生成 program p について、check raw = some p iff eraseProgram p = raw かつ全行有効。
- `check_accepts`（健全性・完全性）: 任意 roles/raw について検査が受理 iff 全入力行が有効。
- `check_fails`（健全性・完全性）: 任意 roles/raw について検査が none iff 無効な入力行が存在。
- `checked_length`（補助）: 任意成功検査の生成 program は入力列と同じ長さ。
- `checked_rows`（健全性）: 任意成功検査と生成 program の任意 member 行について、消去した行は有効。
- `materialized_declared`（健全性）: 任意成功検査、member 行、head、独立 Materializes の結果 goal について、生成 goal は宣言 arity と関連名 membership を保つ。
- `checked_source_exact`（健全性・完全性の既存接続）: 任意 env/roles、明示 core wf/associated awf、検査済み有限 program、任意旧 state と全 assignment v に対し、raw の保存・有効性に加え、返却 model iff 元 model と source valuation への factorization および全独立 Derives の scalar 等式。
- `checked_solver_exact`（健全性・完全性の既存 solver 接続）: 同じ wf/awf と任意旧 state に対し、raw の保存と、実 solver の consistent=true iff 上の model と valuation が存在すること。

最後の2つは新しい意味論ではなく cycle78 の契約の接続。resolution の成功・model の存在・
完成 frontier・燃料・caller が選ぶ valuation は検査の前提でない。`build` が使う有効性証拠は
`check` が計算する。`check` 自体には caller が Template の scope 証拠を渡さない。

## 実装断片と設計境界

検査する arity/関連名は既存 RoleDecl/AssocComplete/AssocDeclared と spec6.1–6.3 に従う。
一つの placeholder と既存 int/str materialization は cycle78 の実装断片の境界。
この checker の失敗を言語の新しい拒否規則にしない。

total registry では role999 にも signature が与えられるため、role999 は検査を通り得る。
一方、対応 dictionary の無い goal の `assocOf` は none。この差を回帰で固定し、
構文検査の成功を dictionary の存在や ordinary model の整合性と取り違えない。
実 parser、scope 名の導出、可視性、registry の wf/awf の source 検査、finite occurrence 列の
網羅性、動的生成は外側に残る。Q1/Q2 と cycle23/24 の既存質問は未決のまま。

設計を Lean 試作前に `notes/design/2026-11-10-cycle79-checked-associated-programs.md` に保存し commit した。
台帳 P 節へ新規入力と12定理の依存を記録した。
inventory は CommonRole246、Main到達93、Audit到達246、台帳言及119。
**言及数は全入力監査済み数ではない。I-13 は部分達成、cycle72 期限超過も残る。**

## 検証

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleCheckedAssociatedPrograms
✔ [288/288] Built Yulang.CommonRoleCheckedAssociatedPrograms (1.1s)
Build completed successfully (288 jobs).
exit 0

ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang79/boundary-check.lean
exit 0
```

scratch は20 example と4 named theorem（既存 wf/awf の2 alias、checked、propagated）。
検査した境界: 空列、2行の共有名伝播、scope外変数、wrong arity、未宣言関連名、
途中の無効行、重複・逆順、定数 goal、nested/repeated placeholder、default付き宣言、
total registry と実 dictionary availability の差。
実有限飽和を回し、raw の検査成功から得た2行 program が source名9へ str を伝播することを確認した。
12新規定理の trust=0 公理出力全文:

```text
'Yulang.CommonRoleCheckedAssociatedPrograms.erase_ofValid' does not depend on any axioms
'Yulang.CommonRoleCheckedAssociatedPrograms.erase_injective' depends on axioms: [propext]
'Yulang.CommonRoleCheckedAssociatedPrograms.eraseProgram_injective' depends on axioms: [propext]
'Yulang.CommonRoleCheckedAssociatedPrograms.erase_build' depends on axioms: [propext]
'Yulang.CommonRoleCheckedAssociatedPrograms.check_exact' depends on axioms: [propext]
'Yulang.CommonRoleCheckedAssociatedPrograms.check_accepts' depends on axioms: [propext]
'Yulang.CommonRoleCheckedAssociatedPrograms.check_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCheckedAssociatedPrograms.checked_length' depends on axioms: [propext]
'Yulang.CommonRoleCheckedAssociatedPrograms.checked_rows' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedAssociatedPrograms.materialized_declared' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCheckedAssociatedPrograms.checked_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCheckedAssociatedPrograms.checked_solver_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

inventory check の全文（exit 0）:

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=246; Main=93; Audit=246; ledger mentioned=119. Mention counts are not audit completion counts.
```

`git diff --check` と staged diff check は exit 0。
公開後、最新 integration/m1-final は cycle78復旧完了0dcf50c03まで進んだため、
明示refspecで最新integration/workをfetchした。同一treeの実公開branchをcheckoutし、
最新integrationを祖先とする公開source自身でdiff gateを再実行した。
`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` 全文（exit 0）:

```text
verify-lean: . @ f2e5857e4 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全体 lake build、全 Audit/AxiomGate、build付きverify-leanは指示どおり local 未実行。
ソース f2e5857e の remote CI は、11:14:51 UTCの確認でCore CIとLean inference kernelの両方がcompleted/success。
- [Core CI](https://github.com/momota1029/yulang/actions/runs/42805568591)
- [Lean inference kernel](https://github.com/momota1029/yulang/actions/runs/42805568456)
後続記録commitのCIとは区別する。

## Yulang2 との照合

cycle78復旧時に最新 `work/dots-audit` 55574b6052ef1534fd0fc36d6d3617ebede59a0e の
x-oracle を読み、C3-PARENT（左右両順/generic function の (11,22)）と missing-child 拒否を確認した。
この素材と spec6.1–6.3/既存 RoleDecl を参照したが、今回の純粋な checker の直接 oracle とはしない。
新しい実機実行・parser実行・raw sourceからこのprogramへのadequacy確認はしていない。

## 復旧、時刻、公開、資源

- この起床の開始10:57:19 UTC、期限11:22:19 UTC。最初は cycle78 writer が active のため書き込まず停止。
  親が前 writer を中断した後、10:57:34から復旧。11:04:32にcycle78のsource/報告/completed心拍を公開・照合して閉じた。
- cycle78のsource ac2cbd47 はCore/Lean両CI successを確認。元の期限と中間心拍の逸脱は
  cycle78報告とcrash記録に残した。cycle79の新規証明と復旧成果を混同しない。
- 復旧後に live integration ff5d5783、standing orders、inbox ACTIVEを確認。STOPではない。
  回復済みtreeを持つ一つの作業場とbuild cacheを継続。破壊的操作やcache複製なし。
- cycle79開始心拍77027420は復旧後、8.9分時点の11:06:11更新。次の心拍70840cbbは
  11:08 UTCで、10分基準の11:07:19より遅れた。時刻基準を完全遵守したとはしない。
- source9 pathを一つのtree/commitにまとめ、20分時点より前に公開・全tree/blob照合を完了。
  API更新は work/dots-main のみ、expected-head指定・force=false。今回のsource公開に拒否や不明結果は無し。
- 初回Lean試作は識別子に予約語を使って構文エラー。名称だけ直して再実行し通過。
  その後solver接続追加後もfocused buildと全scratchを再実行した。期待値は変更していない。
- source公開後は最新remote commitを別のlocal branchでcheckoutした。同じtreeで、元local履歴は保持。
  最新integration0dcf50c03は公開sourceの祖先。integration branchへ書き込みはしていない。
- 空きは開始/終了とも48G（全63G、使用13G）。使用量枠は不明。
- 最終報告を含むcycle79の変更は10 path。cycle78の復旧記録は別cycleの成果。

## 残る B4 橋と次候補

`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、
`saturated_frontier_exact`、`resolve_dictionary_order_sound` の5本が未完。
今回閉じたのは橋1内部の raw structural program の検査と厳密なデータ保存。

1. scope解決済みwhere/associated構文からRawProgramを生成し、occurrenceの出自と網羅性を示す。
2. total signature関数の外側の可視性、名前解決、registry well-formedness生成を具体化する。
3. I-13未監査moduleの入力台帳を続ける。新しい意味論をcaller入力に隠さない。

## 再現用境界検査

```lean
import Yulang.CommonRoleCheckedAssociatedPrograms
open Yulang
open CommonRoleCheckedAssociatedPrograms
open CommonRoleSettledConstraints (State)
namespace Cycle79BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed

def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int

def a : RawOccurrence := ⟨3, 7, 0, goal⟩
def b : RawOccurrence := ⟨7, 9, 0, goal⟩
def raw : RawProgram := [a, b]
def template : CommonRoleStructuralAssociatedTemplates.Template := ⟨goal, by decide⟩
def compiled : CommonRoleStructuralAssociatedTemplates.Program :=
  [⟨3, 7, 0, template⟩, ⟨7, 9, 0, template⟩]

theorem checked : check roles raw = some compiled := by
  apply (check_exact roles raw compiled).mpr
  constructor
  · rfl
  · decide +kernel

example : (check roles raw).isSome = true := by decide +kernel
example : eraseProgram compiled = raw := ((check_exact ..).mp checked).1
example : compiled.length = raw.length := checked_length _ _ _ checked
example : (check roles []).isSome = true := by decide +kernel
example : check roles [] = some [] := by apply (check_exact ..).mpr; exact ⟨rfl, by simp [ValidProgram]⟩

-- Scope, arity, and associated names are checked independently.
def escaped : RawOccurrence := { a with goal := ⟨2, [.var 1, Roles.Examples.int]⟩ }
def wrongArity : RawOccurrence := { a with goal := ⟨2, [.var 0]⟩ }
def absentName : RawOccurrence := { a with name := 99 }
example : (check roles [escaped]).isNone = true := by decide +kernel
example : (check roles [wrongArity]).isNone = true := by decide +kernel
example : (check roles [absentName]).isNone = true := by decide +kernel
example : (check roles [a, wrongArity, b]).isNone = true := by decide +kernel
example : ∃ r ∈ [a, wrongArity, b], ¬ Valid roles r := by
  apply (check_fails roles _).mp
  decide +kernel

-- Order, duplicate rows, aliases, and empty-placeholder syntax are preserved.
example : (check roles [a, a, b]).isSome = true := by decide +kernel
example : (check roles [b, a]).isSome = true := by decide +kernel
example : eraseProgram (compiled.reverse) = raw.reverse := rfl
example : (check roles [{a with goal := ⟨2, [Roles.Examples.int, Roles.Examples.int]⟩}]).isSome = true := by decide +kernel
example : (check roles [{a with goal := ⟨2, [.app 8 [.var 0, .app 9 [.var 0]], Roles.Examples.int]⟩}]).isSome = true := by decide +kernel
example : (check Roles.AssocExamples.defaultRoles raw).isSome = true := by decide +kernel

-- A total role registry is not a source visibility checker.
example : (check roles [{a with goal := ⟨999, [.var 0, Roles.Examples.int]⟩}]).isSome = true := by decide +kernel

def first : Fin (CommonRoleStructuralAssociatedTemplates.compile compiled).length := ⟨0, by decide⟩
def second : Fin (CommonRoleStructuralAssociatedTemplates.compile compiled).length := ⟨1, by decide⟩
def receiver := CommonRoleNamedAssociatedSourceModels.receiver
  (CommonRoleStructuralAssociatedTemplates.compile compiled) first
def output := CommonRoleNamedAssociatedSourceModels.output
  (CommonRoleStructuralAssociatedTemplates.compile compiled) second
def initial : State (CommonRoleStructuralAssociatedTemplates.table compiled).length :=
  CommonRoleCandidateStateFrontier.extend State.empty receiver .str

-- Real saturation uses the fully checked raw two-row program.
theorem propagated : CommonRoleOrdinaryKnownness.Evidence
    (CommonRoleStructuralAssociatedTemplates.run env roles wf compiled initial).atoms output .str := by
  apply (CommonRoleFiniteAssociatedStable.run_evidence env roles wf
    (CommonRoleNamedAssociatedSourceModels.source (CommonRoleStructuralAssociatedTemplates.compile compiled))
    (CommonRoleNamedAssociatedSourceModels.prepared (CommonRoleStructuralAssociatedTemplates.compile compiled) initial)
    output .str).mpr
  apply (CommonRoleFiniteAssociatedClosure.saturate_exact env roles wf _ _ (output, .str)).mp
  decide +kernel
example : CommonRoleStructuralAssociatedTemplates.Derives env roles compiled initial 9 .str :=
  (CommonRoleStructuralAssociatedTemplates.run_evidence_exact env roles wf awf compiled initial output .str).mp propagated

-- Checked syntax need not have an available dictionary.
def unresolved : RawOccurrence := {a with goal := ⟨999, [.var 0, Roles.Examples.int]⟩}
example : (check roles [unresolved]).isSome = true := by decide +kernel
example : Roles.assocOf env roles wf ⟨999, [Roles.Examples.str, Roles.Examples.int]⟩ 0 = none := by decide +kernel

end Cycle79BoundaryCheck
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.erase_ofValid
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.erase_injective
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.eraseProgram_injective
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.erase_build
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.check_exact
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.check_accepts
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.check_fails
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.checked_length
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.checked_rows
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.materialized_declared
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.checked_source_exact
#print axioms Yulang.CommonRoleCheckedAssociatedPrograms.checked_solver_exact
```

完了記録準備: 2026-11-10T11:14:50Z、起床開始から17.5分。復旧後の残り時間で一つの部分目標を閉じた。
