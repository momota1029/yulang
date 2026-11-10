# dots cycle 82 — source の飽和状態から全 role 義務を検査する

## 結果と部分目標

**全 role receiver と関連等式の端点を一緒に割り当て、実際の関連型飽和と ordinary solver の後で、その状態から得た証拠だけを使って全 role 義務を検査する有限 source 境界を閉じた。**

`CommonRoleSourceStateDischarge` は 415 行、19 定理。cycle81 の caller 入力 `heads : Nat → Base` はこの入口にはない。bare clause にも本物の receiver slot があり、関連等式の結果がその slot へ source identity を通して流れる。空の等式や偽の辞書を追加しない。

主定理 `ready_declarative_exact` の右辺は、初期 ordinary 制約・source 同一性・元 source clause の独立な導出からなる `SourceModels` と、各 clause の独立な role discharge の連言である。右辺には実行された saturator や solver の結果がない。caller が選ぶ head map、成功した実行、十分な fuel、あらかじめ選んだモデルも前提ではない。

ただし、**成功した有限 source checker の package、初期 State、core WellFormed、AssocWellFormed は明示的な前提**。初期 State は計算した table 長で型付けされるため、未検査の構文を無条件に処理する外側の入口まで完成とはしない。scope ≤1、int/str materialization、有限な source clause の断片であり、Rust AST・visibility・動的 where 生成・一般の区間 knownness・最終診断は未完。B4 の主要な橋は **5 本のまま**。

## データ、独立判断、量化範囲

全定理の環境や source は固定例ではなく任意。以下の健全性・完全性は、この有限断片についての主張である。

- `role_source`、`equation_source`: 任意の package と適切な Fin 位置について、role prefix またはずらした equation suffix の source 名が元と等しい。
- `slot_count`: 任意の package で、joint table の長さは role 数 + 2 × equation 数。bare clause の slot も数える。
- `equation_identity`: 任意の package と二つの equation 位置で、ずらした後の名前の同一性と、元の名前の同一性が同値。
- `run_evidence_exact`: 任意の env/roles、core wf と associated awf、package、初期 State、slot、Base について、実飽和が出す paired Evidence と独立な宣言 graph 導出 `Derives` が同値。成功や整合性を仮定しない。
- `run_models_exact`: 同じ任意の入力と任意の occurrence valuation について、出力 ordinary 制約を満たすことと、旧制約・source type の同一性・全独立 graph fact を満たすことが同値。effect 行は保存し、同一視しない。
- `run_one_exact`: 同じ環境と任意の role 位置、同じ erasure の source clause について、計算した evidence による role test の true と、導出された head とその source clause の独立 discharge が同値。
- `derives_same_receiver`: 任意の二つの role 位置で receiver 名が等しければ、任意の head の独立 graph 導出が同値。bare の位置にも適用できる。
- `ready_source_exact`: 任意の checker 受理済み source/package と初期 State、wf/awf について、readiness が true であることと、出力のモデル存在・全 source clause の独立な `Supported` が同値。
- `occurrence_origin`、`occurrence_present`: 任意の package で、joint graph の各 equation edge は元 checked equation に由来し、全 checked equation が graph にある。receiver/output の同一性と独立な associated step の双方向対応を同時に示す。
- `prepared_evidence`: 任意の初期 State、slot、head で、source 同一性の追加は初期 paired scalar Evidence を増やさない。
- `allocated_to_source`: 任意の受理済み source/package、初期 State、slot/head の独立 graph 導出から、元 source clause に対する `SourceDerives` を得る。
- `source_to_allocated`: 同じ入力で、任意の source 名/head の `SourceDerives` から、その名前を持つ**全ての** joint slot の独立 graph 導出を得る。
- `run_source_evidence_exact`: 任意の受理済み source/package、State、wf/awf、slot/head で、実飽和の Evidence と元 source の `SourceDerives` が同値。
- `ready_original_source_exact`: 同じ入力で、実 readiness と、出力のモデル存在および各元 clause に source-derived head と独立 discharge が存在することが同値。package の位置を渡す条件は右辺から除いた。
- `source_models_exact`: 同じ任意の入力で、実出力のモデル存在と独立 `SourceModels` が同値。
- `ready_declarative_exact`: 上記二つを結び、実 readiness と、独立 `SourceModels` および全元 clause の source-derived head と独立 discharge の存在を双方向で結ぶ。
- `ready_has_models`: 任意の package/State と core wf について、ready が true なら出力はモデルを持つ。ここでは associated awf は不要。矛盾した scalar evidence から role を認証しない。

`SourceDerives` の初期 rule は元 State の Evidence、再帰 rule は元 source の clause/equation と structural Fills・Resolves・AssocDerives を読む。実行版の graph や resolver 結果を独立判断に埋め込んでいない。

## 忠実性、受け入れ条件、未達

spec6.3 の関連等式、共有された型変数、全 where 義務の連言、兄弟の安定後の判定に向かう接続である。回帰では関連式が得た str が、それまで未知だった bare receiver へ流れて role test を通す。source の順序を逆にした具体例も通る。ただし、任意の順序変更に伴う初期 State の再割当てについての一般の同値定理は、この module では追加していない。

この Bool は readiness の検査であり、false を言語の rejected/pending/ambiguous の分類にしない。初期 evidence がないと、一意の impl から receiver を決めない。bool/unit は既存 encoder の外側であり、unused receiver の constant template についても cycle81 の境界を維持する。total registry の受理は visibility や dictionary existence を意味しない。

I-4/I-7 の橋1にある state と role の接続を進めた。完全な Parent/Left/Right の外側入口、X13–X16、一般 B4、主型性の完成は主張しない。I-13 台帳 S 節に全新規入力・導出される入力を追記した。全 module の入力監査は依然として未完、cycle72 の期限超過は解消していない。既存 Q1/Q2 と cycle23/24 を決着させず、新規の意味論質問は 0 件。

## 検証

最終 source の以下は全て exit 0。

```text
cd lean
ELAN_HOME=../../elan ../../elan/bin/lake build Yulang.CommonRoleSourceStateDischarge --wfail
✔ [291/291] Built Yulang.CommonRoleSourceStateDischarge (2.3s)
Build completed successfully (291 jobs).

ELAN_HOME=../../elan ../../elan/bin/lake env lean --trust=0 ../../cache/yulang82/boundary-check.lean
exit 0
```

境界検査は **27 examples、6 named helpers**。bare receiver の独立な割当て、未知からの非推論、associated output から bare receiver への伝播、重複された receiver の共有、同名位置の矛盾、bool/unit、辞書なし、不正 signature、空 source、逆順の具体例を含む。`independentStep` は explicit な associated declaration witness を組み、`independentPropagation` は初期 seed と source equation の rule で証明してから、逆方向の実 evidence 定理に通した。

19 定理の trust=0 公理出力全文:

```text
'Yulang.CommonRoleSourceStateDischarge.role_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.equation_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.slot_count' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.equation_identity' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.run_evidence_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.run_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.run_one_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.derives_same_receiver' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.ready_source_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.occurrence_origin' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.occurrence_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.prepared_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.allocated_to_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.source_to_allocated' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.run_source_evidence_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.ready_original_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.source_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.ready_declarative_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceStateDischarge.ready_has_models' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python3 tools/boundary-input-inventory.py --check` (exit 0):

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=249; Main=93; Audit=249; ledger mentioned=122. Mention counts are not audit completion counts.
```

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build` (exit 0):

```text
verify-lean: . @ 4a2e6c10d (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` も exit 0。途中の Lean elaboration エラーは修正し、最終 source で focused build と境界検査を再実行した。最初の境界検査は module 未生成で失敗し、続く Evidence の直接 decidability は既存 candidates の exactness 経由へ直した。期待値は変えていない。公理は propext / Classical.choice / Quot.sound のみ。全体 build、全 Audit、AxiomGate、全体 verify は実行していない。監督役の検証が必要。

## Yulang2 との照合

`work/dots-audit` を取得し、`notes/audit/x-oracle.md` の C3-PARENT（両順/generic 成功）と C3-PARENT-NEG（missing child 拒否）を再確認した。audit ref は `55574b6052ef1534fd0fc36d6d3617ebede59a0e`。これは where の連言の意味の参考で、この新しい Lean carrier を直接検証する oracle ではない。新しい Yulang2 実機、Rust parser、全言語の実装は実行していない。最初の二つの参照先を誤って探した後、tree 一覧にある正しい audit path を読んだ。

## 復旧、公開、時刻、資源

- 最初の開始記録は 2026-11-10T12:57:28Z。cache の start ファイルは 12:57:57Z に作成。live integration/work はともに `8732e4860005f123119bf8ace5de9ff7276ce702`。最新の standing orders と inbox を読み、ACTIVE、上限なしを確認した。integration をローカルへ merge し、前 cycle の completed 心拍と report を確認。前の writer はなかった。
- 最初の fetch は origin/work の refspec を更新しておらず、古い cycle80 の追跡 ref を表示した。明示した refspec と GitHub の live head を再取得し、cycle81 completed を確認してから開始した。古い表示を crash と誤判定していない。新規 crash 報告は不要。
- 一つの clone と既存 Lean cache を継続した。回復 worktree や build cache は増やしていない。開始時と報告時の空きはともに 48G / 全63G、使用13G。使用量の枠は不明。
- 設計 commit `388b69779`、検証済み source commit `4a2e6c10d`。開始心拍は `b2b4f2285db0c21a172deb58e163bca81db3d2ee`。開始心拍の updated は誤って未来の13:00:20Zを記載した。started は正しく、10分心拍で実測時刻へ訂正し、ここにも残す。
- 10分心拍の updated は13:07:36Z、公開 commit は `196c5f438ed309e9e6181c688a0bc117b1df7ffe`。約10分時点で焦点検証が終わり、source の個別 blob 公開を開始した。
- 途中公開は `2659eca8ed5c01a5eff6cadd1e5fa902ee8a15de`、tree は `45ff6682fa2d09b2e96d7afa42253b246329cada`。GitHub の recursive tree を取得し、2304 entries、非 truncated。変更9 paths の blob SHA が全一致し、**全 tree SHA も検証済みローカル tree と一致**。git で公開 head を取得し、local との差分が空であることも確認した。
- 個別 blob を作り、SHA だけの tree を live base tree から作成。既存 head を親とし expected-head、force=false で ref を更新した。書き込みは work/dots-main のみ。integration、main 等には書いていない。
- 大きい local JSON の一括読み取りは出力の途中切れで parse に失敗した。外部書き込みではない。各 file を4万文字ずつ読み、元の content に戻した上で個別 blob を作成し、local git blob SHA と照合した。公開 blob の不確かな再送や拒否された操作の迂回はない。
- 途中公開の exact-head CI は Core CI success、Lean inference kernel は in_progress（run 42822304733）。全体 CI の成功はまだ主張しない。最終 report head の CI は別途確認する。
- report と completed 心拍を含めた公開差分は10 paths。この記録後にその2 pathsを公開し、再度 tree/content を照合する。最終結果を親へ返す。
- 報告作成時刻: 2026-11-10T13:15:09Z、開始から 17.7 分。13:22:19 UTC の期限内で、残りは最終公開・照合。25分上限内。

## 公開後の確認（2026-11-10T13:16:49Z）

初回の最終報告 head `6498a62e3f332e16e25f6cf7a666687724b7f3b9` を取得し、tree `5c2a521d1412a41ed0812dc2ade8121b1a692304` の全2305 entriesと変更10 pathsを照合した。ローカル検証済みtreeと完全一致し、報告の本文も GitHub から取り戻して一致した。

検証済み source checkpoint `2659eca8ed5c01a5eff6cadd1e5fa902ee8a15de` の **Core CI と Lean inference kernel は両方 success** になった。Lean run は [42822304733](https://github.com/momota1029/yulang/actions/runs/42822304733)。これはその exact source commit の CI 結果であり、未実施のローカル全体検証や supervisor の統合確認を実施済みに置き換えない。この追記は報告と心拍だけの変更。初回報告 head の Core CI は確認時に in_progress だった。

## B4 に残る橋と次の候補

`source_boundary_adequate`、`generated_work_closed`、`saturate_terminates_and_closes`、`saturated_frontier_exact`、`resolve_dictionary_order_sound` の **5 本**が未完。今回の有限 state-backed readiness は、その内部の狭い断片。

1. source checker から得た dependent package/table と、source 式からの初期 ordinary State 構築を結び、成功 checker と既存 State を外側から渡さない入口へ進める。Rust AST・registry visibility は未達と明記する。
2. 計算した有限 source table を dynamic where 子生成の閉包へ結ぶ。既存の identity/未拘束変数の判断を勝手に補わない。
3. I-13 の未監査 module の入力台帳を継続する。新しい入力を隠して一般 B4 と扱わない。

## 再現用境界検査

```lean
import Yulang.CommonRoleSourceStateDischarge
open Yulang CommonRoleSourceStateDischarge
open CommonRoleAssociatedClauseExtraction (Clause Source)
open CommonRoleSettledConstraints (State)
open CommonRoleCandidateStateFrontier (extend)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Cycle82BoundaryCheck

def roles := Roles.AssocExamples.requiredRoles
def env := Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl
theorem wf : Roles.WellFormed env.cores := Roles.AssocExamples.box_paterson
theorem awf : Roles.AssocWellFormed env roles := Roles.AssocExamples.box_assoc_wellFormed
def goal : Roles.Goal := Roles.AssocExamples.index
  (Roles.AssocExamples.box (.var 0)) Roles.Examples.int
def bare : Clause := ⟨7, goal, []⟩
def associated : Clause := ⟨3, goal, [⟨0, 7⟩]⟩
def src : Source := [associated, bare]
def p := CommonRoleSourceRoleObligations.build roles src (by decide)
theorem checked : CommonRoleSourceRoleObligations.check roles src = some p := by
  unfold CommonRoleSourceRoleObligations.check
  split
  · rfl
  · rename_i h; exact False.elim (h (by decide))
def initial : State (table p).length := extend State.empty (roleSlot p ⟨0, by decide⟩) .str

example : table p = [3, 7, 3, 7] := by decide
example : (occurrences p).length = 1 := by decide
example : (table p).length = 4 := slot_count p
example : ready env roles wf p State.empty = false := by decide +kernel
example : ready env roles wf p initial = true := by decide +kernel
example : runOne env.cores wf p initial ⟨1, by decide⟩ = false := by decide +kernel
example : runOne env.cores wf p (runState env roles wf p initial) ⟨1, by decide⟩ = true := by decide +kernel
example : CommonRoleOrdinaryKnownness.detect
    (runState env roles wf p initial).atoms (roleSlot p ⟨1, by decide⟩) = some .str := by decide +kernel
example : CommonRoleSourceRoleObligations.runSource env.cores wf roles src (fun _ => .str) = true := by decide +kernel

-- Reverse direction starts with source-level associated derivations, not a head map.
theorem propagated : SourceDerives env roles src p initial 7 .str := by
  apply (run_source_evidence_exact env roles wf awf src p checked initial
    (roleSlot p ⟨1, by decide⟩) .str).mp
  apply (CommonRoleOrdinaryKnownness.candidates_exact _ _ _).mp
  decide +kernel
example : ∀ c ∈ src, ∃ head, SourceDerives env roles src p initial c.receiver head ∧
    CommonRoleSourceRoleObligations.Discharges env.cores (fun _ => head) c :=
  ((ready_original_source_exact env roles wf awf src p checked initial).mp (by decide +kernel)).2

theorem independentStep : CommonRoleAssociatedClauseExtraction.Step env roles associated ⟨0, 7⟩ .str .str := by
  refine ⟨Roles.Examples.str, Roles.AssocExamples.index
    (Roles.AssocExamples.box Roles.Examples.str) Roles.Examples.int, rfl, rfl, ?_, ?_,
    Roles.Examples.str, ?_, rfl⟩
  · exact .cons (.app (.cons .hole .nil)) (.cons (.app .nil) .nil)
  · exact (RoleConstraints.resolve_exact _ wf _).mp Roles.AssocExamples.box_resolved
  · exact .explicit Roles.AssocExamples.boxImpl (fun _ => Roles.Examples.str)
      (by simp [env, Roles.AssocExamples.singletonEnv]) rfl rfl
      (by intro c h; cases h) (.var 0) rfl

theorem independentPropagation : SourceDerives env roles src p initial 7 .str := by
  apply SourceDerives.equation associated ⟨0, 7⟩ (by simp [src]) (by simp [associated])
  · have init : SourceDerives env roles src p initial
        (CommonRoleSourceIdentity.source (table p) (roleSlot p ⟨0, by decide⟩)) .str :=
      .initial _ (by simp [initial, extend, CommonRoleCandidateStateFrontier.equality,
        CommonRoleOrdinaryKnownness.Evidence])
    exact init
  · exact independentStep
example : CommonRoleOrdinaryKnownness.Evidence (runState env roles wf p initial).atoms
    (roleSlot p ⟨1, by decide⟩) .str :=
  (run_source_evidence_exact env roles wf awf src p checked initial _ .str).mpr independentPropagation

-- Bare receivers exist even with no equation endpoints.
def bareP := CommonRoleSourceRoleObligations.build roles [bare] (by decide)
example : table bareP = [7] := by decide
example : occurrences bareP = [] := rfl
example : ready env roles wf bareP State.empty = false := by decide +kernel
example : ready env roles wf bareP (extend State.empty (roleSlot bareP ⟨0, by decide⟩) .str) = true := by decide +kernel
example : ready env roles wf bareP (extend State.empty (roleSlot bareP ⟨0, by decide⟩) .bool) = false := by decide +kernel
example : ready env roles wf bareP (extend State.empty (roleSlot bareP ⟨0, by decide⟩) .unit) = false := by decide +kernel
example : ready env roles wf bareP (extend
    (extend State.empty (roleSlot bareP ⟨0, by decide⟩) .str)
    (roleSlot bareP ⟨0, by decide⟩) .int) = false := by decide +kernel

-- Duplicate occurrences share evidence rather than requiring two initial pairs.
def duplicates := CommonRoleSourceRoleObligations.build roles [bare, bare] (by decide)
example : table duplicates = [7, 7] := by decide
example : ready env roles wf duplicates
    (extend State.empty (roleSlot duplicates ⟨0, by decide⟩) .str) = true := by decide +kernel
example : ready env roles wf duplicates
    (extend (extend State.empty (roleSlot duplicates ⟨0, by decide⟩) .str)
      (roleSlot duplicates ⟨1, by decide⟩) .int) = false := by decide +kernel

-- Empty sources succeed only when the ordinary state is consistent.
def emptyP := CommonRoleSourceRoleObligations.build roles [] (by decide)
example : table emptyP = [] := rfl
example : ready env roles wf emptyP State.empty = true := by decide +kernel

-- Missing dictionaries and invalid sources are never erased by empty equations.
def missing : Clause := ⟨7, ⟨999, goal.args⟩, []⟩
def missingP := CommonRoleSourceRoleObligations.build roles [missing] (by decide)
example : ready env roles wf missingP
    (extend State.empty (roleSlot missingP ⟨0, by decide⟩) .str) = false := by decide +kernel
example : (CommonRoleSourceRoleObligations.check roles
    [{bare with goal := ⟨2, [.var 0]⟩}]).isNone = true := by decide +kernel

-- A reversed source still propagates from the same source name.
def reversed := CommonRoleSourceRoleObligations.build roles [bare, associated] (by decide)
example : table reversed = [7, 3, 3, 7] := by decide
example : ready env roles wf reversed
    (extend State.empty (roleSlot reversed ⟨1, by decide⟩) .str) = true := by decide +kernel
end Cycle82BoundaryCheck
#print axioms Yulang.CommonRoleSourceStateDischarge.role_source
#print axioms Yulang.CommonRoleSourceStateDischarge.equation_source
#print axioms Yulang.CommonRoleSourceStateDischarge.slot_count
#print axioms Yulang.CommonRoleSourceStateDischarge.equation_identity
#print axioms Yulang.CommonRoleSourceStateDischarge.run_evidence_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.run_models_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.run_one_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.derives_same_receiver
#print axioms Yulang.CommonRoleSourceStateDischarge.ready_source_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.occurrence_origin
#print axioms Yulang.CommonRoleSourceStateDischarge.occurrence_present
#print axioms Yulang.CommonRoleSourceStateDischarge.prepared_evidence
#print axioms Yulang.CommonRoleSourceStateDischarge.allocated_to_source
#print axioms Yulang.CommonRoleSourceStateDischarge.source_to_allocated
#print axioms Yulang.CommonRoleSourceStateDischarge.run_source_evidence_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.ready_original_source_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.source_models_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.ready_declarative_exact
#print axioms Yulang.CommonRoleSourceStateDischarge.ready_has_models
```
