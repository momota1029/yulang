# dots cycle 96 — 実 materialization と診断 tree の有限進捗

## 結果と部分目標

**元 Goal の変数出現回数から、実 ordinary 状態に従って materialized Goal が変化する回数の上限を証明した。さらに、実 public run の完全な診断 Tree が変化すると同じ尺度が厳密に減ることを証明した。** 新規 `CommonRoleMaterializationProgress` は229行、14公開定理。

任意の長さの状態列、任意の Form 構造、上下両端点、任意の共有・slot alias を扱う。隣接状態間で atom が包含され、後の状態にモデルがあるという二前提を明記した。上限は caller の fuel や rank ではなく元 Goal から計算する。

これは I-4 優先3の停止性へ向けた補助部分である。飽和 driver、実 solver が生成する列との対応、一般 source identity は閉じていない。**T1c 全体、外側 resolve_exact、X13〜X16、B4 の5橋はいずれも未完成。** 不変状態の後にも新証拠が来れば変化するので、この尺度の plateau を停止条件にはしていない。

## 定理、量化と前提

全て `Yulang.CommonRoleMaterializationProgress`。全14定理の区分は **補助（進捗・停止性の成分）**。健全性・完全性・主型性のどれかを単独で完成したとの主張はない。

1. `materialize_le`: 任意 n、atoms、slots、Form について、実 materialization 後の変数出現回数は元以下。整合性の前提なし。
2. `materialize_equal_of_count`: 同じ任意入力で、前後の出現回数が同じなら Form の構文そのものが同じ。
3. `arguments_le`: 任意長の上下端点列について、両端点を含む総出現回数は増えない。
4. `arguments_equal_of_count`: 任意端点列で総出現回数が同じなら materialization 後の列そのものが元の列と同じ。
5. `goal_le`: 任意 Goal・状態・slots で、materialized Goal の potential は元 Goal 以下。
6. `goal_equal_of_count`: 同じ任意入力で potential が同じなら Goal 全体が同じ。
7. `goal_fusion`: 任意 before/after atoms、全 before atom が after に属する前提、after の任意モデル、同じ任意 slots と元 Goal に対し、before の materialization を after で再実行した Goal は元を after で materialize した Goal と等しい。
8. `extension_le`: 任意 before/after、包含と後モデルの存在を表す Extension、同じ slots と元 Goal で、after の potential は before 以下。
9. `extension_strict`: 同じ任意入力と Extension に加え、前後の materialized Goal が異なるなら potential は厳密に減る。
10. `changes_with_remaining`: 任意 initial atoms と任意有限状態列が Chain（隣接 Extension）なら、実 Goal の隣接変化数 + 最後の potential ≤ 最初の materialized Goal の potential。
11. `changes_bounded`: 同じ任意 Chain の実変化数 ≤ 元 Goal だけから計算した potential。列の長さは上限に現れない。
12. `run_tree_equal`: 任意 registry、slots、Sources、before/after atoms、別々の任意 oldBefore/oldAfter、同じ元 Goal で、materialized Goal が等しければ実 public run の Option Tree 射影が等しい。宣言検査成功・モデルの前提なし。
13. `run_tree_strict`: 上記の任意入力で Extension があり、実 Option Tree 射影が異なれば同じ source potential が厳密に減る。
14. `run_tree_plateau`: 同じ任意入力と Extension で potential が等しければ全 Option Tree 射影が等しい。後続状態での不変性は結論ではない。

## 入力境界と未達

- この断片は cycle95 と同じ明示 paired int 証拠の detector を使う。一般の semantic entailment、str/bool/unit の materialization ではない。他の型を仕様上拒否する決定ではなく、既存実装断片の制限であり module/docstring に明記した。
- 原子列の順序・重複を固定せず membership inclusion を使う。consistent な再順序や同じ証拠の重複は許す。後モデルは数学的前提で、計算にモデルや証明を渡さない。
- 原 Goal と slots は固定。変数は occurrence を数えるため、同名反復や slot alias で上限が緩くなるが壊れない。最小の上限や計算量は主張しない。
- 有限 trace は theorem の対象として caller から渡す。実 solver の生成 trace や飽和実行の adequacy ではない。変化しない ordinary 更新、同じ Goal の反復、停止時刻、全実行時間、graph 内部頂点数には上限を与えない。
- `Chain initial []` は True であり、空列の初期整合性は不要。非空なら後モデルと包含から初期も満たされる。初期矛盾を使って厳密変化を作る抜け道ではない。
- 比較する実 Tree は未完了の子、outside/rejects、順序・重複まで全て含む。Option None の宣言拒否も型上含む。old demands が異なっても Tree 部分は同じだが graph、graph のモデル、source 観察が同じとは主張しない。
- invocation Sources の Goal 依存キー、候補 guard、元 source 制約への対応は未解決のまま。新意味論判断0件、新質問0件。既存 invocation-sharing 質問を勝手に解決していない。

## 検証

最終 production source に以下を実行し、全て exit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleMaterializationProgress --wfail
✔ [312/312] Built Yulang.CommonRoleMaterializationProgress (1.2s)
Build completed successfully (312 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang96/boundary-check.lean
exit 0, no diagnostics
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang96/axioms.lean
'Yulang.CommonRoleMaterializationProgress.materialize_le' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.materialize_equal_of_count' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.arguments_le' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.arguments_equal_of_count' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.goal_le' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.goal_equal_of_count' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.goal_fusion' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.extension_le' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.extension_strict' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.changes_with_remaining' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.changes_bounded' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.run_tree_equal' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.run_tree_strict' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleMaterializationProgress.run_tree_plateau' depends on axioms: [propext, Quot.sound]
```

26 executable guards と5 kernel examples、補助モデル証明を検査した。空 Goal、零変数、空状態列、不変状態の反復、遅れて到着する証拠、2 slot のちょうど2回の変化、既に一部/全てが int の初期状態、nested pair/join/tick、同名反復、異名 slot alias、片方向証拠、str/bool/unit、複数引数を含む。

- 整合状態でも atom 包含なしでは、1変数の Goal が5回変化する負例を確認した。
- atom 包含があっても、後状態が paired str ++ paired int という矛盾状態なら、1変数の Goal が2回変化する負例を確認した。
- 5番目の kernel example は実 run を使い、任意 registry/Sources と異なる oldBefore/oldAfter を許して、証拠重複後の全 Tree の同一性を確認した。
- 期待値は実装へ合わせて変更していない。実行 guard は普遍的定理とは別に数えている。

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=263; Main=93; Audit=263; ledger mentioned=136. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 777fb2b47 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` exit 0。指示どおり全ローカル build、全 Audit/AxiomGate は実行していない。verify は diff-only の PASS。14定理の公理は全て propext / Quot.sound のみ。

独立 read-only reviewer が最終 module を `lake env lean --trust=0` で確認し exit 0。量化、空 Chain、任意の共有、Tree と graph の区別、plateau の境界に問題なしとの結果。reviewer の提案を受けて、異なる old demands の kernel example を追加した。

途中で fusion 証明の未展開の definition と未導入 tactic `by_contra` により build が失敗し、定義の展開と decidable な場合分けへ直した。試験ファイルの elaboration/syntax も直し、最後に全焦点検査を通した。古い olean への一時的 audit 失敗後にも、最終14定理を全て再監査した。結論や期待値の弱化なし。

## Yulang2 との照合

取得済み `work/dots-audit` の `notes/audit/x-oracle.md` X13〜X16 と関連 role/type 比較を読んだ。X13 は shared box の局所表示、X14 は深さ2、X15 は同頭の局所区間、X16 は異頭の union/intersection の近似であり、任意 interval state や飽和 trace を外側から直接観測した保証ではない。これを今回の一般進捗定理の実機検証とは呼ばない。新しい Yulang2 実機実行なし。spec 6.3 の ordinary 制約による絞り込み・遅延判断という方向に従い、unique impl を証拠にはしていない。

## 公開と復旧

source commit: `d0ea71eab81163a6f900a45282f30826d4e724aa`。
source tree: `5c44ffefda6a840154ec65ae345206bd99d8f8e3`。
local source checkpoint: `777fb2b47`、心拍込み `03ad748f2`。

9変更 path を個別 blob として公開し、全返却 SHA が local hash-object と一致。live work tree を base に SHA-only tree を作り、全 tree SHA が local write-tree と一致した。非 force・expected-head 更新後に ref と非 truncated recursive tree（2346 entries）を再取得し、全9変更 blob を照合した。他 path は保持し、production Lean は source 公開後に変更していない。

startup heartbeat `357abcc9`、source 公開 `d0ea71ea`、verified-source heartbeat `6bd4de17`。source 公開は開始12.2分、確認済み heartbeat は12.5分。最初の heartbeat の updated 値は手入力で実際の UTC より先になっていたため、source 以後は date から取得した実時刻へ修正した。

開始は2026-11-10T19:57:13Z、指定期限20:22:19Z。live integration/work は開始時ともに `38635a95`。standing orders/inbox を取得して再読し ACTIVE と上限なしを確認した。前 cycle95 は completed と報告あり、前 writer/Lean process もなし。通常再開で crash recovery ではない。fetch の既存設定が integration のみを更新していたため、work の追跡 ref も明示取得して live branch と一致させた。integration を通常 merge し、既存 workspace/cache を再利用した。

開始/報告準備時の空きは47G（63G中13G使用）。新 clone、cache コピーなし。使用量の枠は不明。ログは `../cache/yulang96`。報告と completed heartbeat を最終公開し、ref/tree/blob を照合する。報告を含む今回の変更は10 path。

## B4に残る5橋と次の候補

1. `source_boundary_adequate`: parser/declからscope、annotation、source occurrence/invocationの導出。
2. `generated_work_closed`: 固定 template・明示 int evidence から一般 state 依存生成仕事へ。
3. `saturate_terminates_and_closes`: 今回の変化回数成分と Paterson child closure を結び、ordinary の不変更新も扱う実 driver の停止と閉包。
4. `saturated_frontier_exact`: 安定後の独立4分類と実飽和の対応。
5. `resolve_dictionary_order_sound`: 正準 source obligation 順の dictionary 観察同値。

次候補は (a) `run_tree_strict` と cycle95 `run_computed_bound` を使う生成仕事 scheduler の具体的境界設計、(b) source invocation の再訪時の意味保存、(c) int 以外を含む一般 interval materialization の provenance。未定義の scheduler/fairness/source identity を仮定へ隠して停止完成とはしない。

## 再実行可能な回帰

```lean
import Yulang.CommonRoleMaterializationProgress
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleMaterializationProgress
open CommonRoleStateMaterializedFrontier (materialize materializeGoal)
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (Atom All)
namespace Cycle96BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

def slots : Nat → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt n (by decide)⟩
def eqn (i : Fin 2) (b : Inference.Base) := CommonRoleCandidateStateFrontier.equality i b
def one := eqn 0 .int
def both := one ++ eqn 1 .int
def scalarGoal : Goal := ⟨0,[(.var 0,.var 1)]⟩
def nestedGoal : Goal := ⟨0,[(.pair (.var 0) (.tick (.join (.var 2) (.var 1))),.var 0)]⟩
def assignment : Fin 2 → Comp Common.model := fun _ => (.base .int,fun _ => False)

theorem eqn_models (i : Fin 2) : All Common.model assignment (eqn i .int) := by
  simp [All, eqn, CommonRoleCandidateStateFrontier.equality, Atom.Holds,
    TyTerm.eval, assignment, Common.model, Common.subtype_refl]

theorem one_models : All Common.model assignment one := eqn_models 0
theorem both_models : All Common.model assignment both :=
  (PresenceNormalForm.all_append ..).mpr ⟨one_models,eqn_models 1⟩

theorem positive_chain : Chain ([] : List (Atom (Fin 2))) [[],one,one,both,both] := by
  refine ⟨⟨?_,assignment,PresenceNormalForm.all_nil Common.model assignment⟩,⟨⟨?_,assignment,one_models⟩,
    ⟨⟨?_,assignment,one_models⟩,⟨⟨?_,assignment,both_models⟩,⟨⟨?_,assignment,both_models⟩, trivial⟩⟩⟩⟩⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; exact h
  · intro atom h; exact List.mem_append_left _ h
  · intro _ h; exact h

#guard potential scalarGoal = 2
#guard changes slots scalarGoal [] [[],one,one,both,both] = 2
#guard potential (materializeGoal both slots scalarGoal) = 0
#guard changes slots scalarGoal one [one,both,both] = 1
#guard changes slots scalarGoal both [both,both,both] = 0
#guard changes slots scalarGoal [] [] = 0
#guard (finalState ([] : List (Atom (Fin 2))) [[],one,one,both,both]).length = 4
-- Repeated source names and different names that alias one slot resolve together.
#guard potential nestedGoal = 4
#guard potential (materializeGoal one slots nestedGoal) = 1
#guard changes slots nestedGoal [] [one,both] = 2
#guard potential (materializeGoal both slots nestedGoal) = 0
-- A plateau does not imply later stability; late changes still count.
#guard changes slots scalarGoal [] [[],[],[],[],[],one] = 1
#guard changes slots scalarGoal [] [eqn 1 .str] = 0
#guard changes slots scalarGoal [] [[.tyLe (.var 0) (.base .int)]] = 0
#guard changes slots scalarGoal [] [eqn 0 .bool] = 0
#guard changes slots scalarGoal [] [eqn 0 .unit] = 0
-- No original variables means no changes, even across arbitrary inconsistent states.
#guard potential ⟨7,[(.pair .int (.tick .int),.join .int .int)]⟩ = 0
#guard changes slots ⟨7,[(.pair .int (.tick .int),.join .int .int)]⟩ []
  [one,eqn 0 .str ++ one,[],both] = 0
#guard changes slots ⟨7,[]⟩ [] [one,[],both] = 0
-- Reordering and duplicate evidence are harmless for consistent evidence.
#guard materializeGoal (eqn 1 .int ++ one ++ one) slots scalarGoal =
  materializeGoal both slots scalarGoal
-- Without inclusion, even consistent states can repeatedly undo materialization.
#guard changes slots ⟨0,[(.var 0,.int)]⟩ [] [one,[],one,[],one] = 5
#guard potential ⟨0,[(.var 0,.int)]⟩ = 1
-- With inclusion but without consistency, new first-evidence can undo it too.
#guard materializeGoal (eqn 0 .str ++ one) slots ⟨0,[(.var 0,.int)]⟩ =
  (⟨0,[(.var 0,.int)]⟩ : Goal)
#guard changes slots ⟨0,[(.var 0,.int)]⟩ [] [one,eqn 0 .str ++ one] = 2
-- All constructors and empty/multiple arguments preserve their unchanged syntax.
#guard materialize [] slots (.pair (.join (.var 0) (.var 1)) (.tick (.var 2))) =
  .pair (.join (.var 0) (.var 1)) (.tick (.var 2))
#guard potential ⟨3,[(.var 0,.int),(.var 1,.tick (.var 0))]⟩ = 3

example : changes slots scalarGoal [] [[],one,one,both,both] +
    potential (materializeGoal both slots scalarGoal) ≤ potential scalarGoal := by
  simpa [finalState, scalarGoal, potential, argumentCount, materializeGoal,
    CommonRoleStateMaterializedFrontier.arguments, materialize, remaining,
    CommonRoleOrdinaryKnownness.detect, CommonRoleOrdinaryKnownness.candidates,
    CommonRoleOrdinaryKnownness.upper] using changes_with_remaining slots scalarGoal []
    [[],one,one,both,both] positive_chain

example : changes slots nestedGoal [] [[],one,one,both,both] ≤ potential nestedGoal :=
  changes_bounded slots nestedGoal [] [[],one,one,both,both] positive_chain

-- Strict progress does not require injective slots, unique names or unique impls.
example (before after : List (Atom (Fin 2))) (extension : Extension before after)
    (changed : materializeGoal after slots nestedGoal ≠ materializeGoal before slots nestedGoal) :
    potential (materializeGoal after slots nestedGoal) < potential (materializeGoal before slots nestedGoal) :=
  extension_strict before after extension slots nestedGoal changed

-- Model witness is a theorem premise only, not part of the actual counter.
example (states : List (List (Atom (Fin 2)))) (chain : Chain both states) :
    changes slots scalarGoal both states = 0 := by
  have bound := changes_with_remaining slots scalarGoal both states chain
  have zero : potential (materializeGoal both slots scalarGoal) = 0 := by decide +kernel
  omega
-- Complete actual public tree equality permits distinct old demand lists.
example (registry : List CommonRoleStablePaterson.Declaration)
    (sources : CommonRoleGuardedIntervalPlans.Sources)
    (oldBefore oldAfter : CommonRoleGuardedIntervalPlans.Plan (Fin 2)) :
    (CommonRoleStateMaterializedFrontier.run registry slots sources one oldBefore scalarGoal).map Prod.fst =
      (CommonRoleStateMaterializedFrontier.run registry slots sources (one ++ one) oldAfter scalarGoal).map Prod.fst := by
  apply run_tree_plateau
  · exact ⟨(fun _ h => List.mem_append_left _ h), assignment,
      (PresenceNormalForm.all_append ..).mpr ⟨one_models,one_models⟩⟩
  · decide +kernel

end Cycle96BoundaryCheck
```

報告準備時刻: 2026-11-10T20:11:38.225460+00:00、経過 14.4分。

## Exact-source CI と最終公開準備（2026-11-10T20:12:19.192635+00:00）

source `d0ea71eab81163a6f900a45282f30826d4e724aa` の Core CI と Lean inference
kernel は両方 completed/success。Lean proof job の全 build、全宣言 Audit、
source/value/regular/semantic record examples の各 step も success を確認した。
remote CI の結果でありローカル全体検証と区別する。production Lean の後続変更なし。

- Core: https://github.com/momota1029/yulang/actions/runs/42892457223
- Lean: https://github.com/momota1029/yulang/actions/runs/42892457126

経過15.1分で今回の部分目標・焦点検証・source 公開・exact-source CI確認が完了。
指定期限20:22:19 UTCまでに報告とcompleted heartbeatを公開し、最終ref/tree/blobを照合して終了する。
