import Yulang.CommonRoleSettledRootClassification

/-!
# Settled断片の可視impl順序独立

同じ宣言を並べ替えたchecked registryについて、一需要のfrontierだけでなく、
全子の順序と未完成の診断を保った完全なtreeが一致する。
where列の並べ替えや一般sourceの正準義務順は別の未接続境界。
-/
namespace Yulang.CommonRoleSettledVisibleOrder
open CommonRoleSettledSyntax
open CommonRoleSettledConstraints (State)
open CommonRoleSettledFrontier
open CommonRoleOutermostResolver (Tree Child)

/-- scanは実trialのfilterMapであり、見えている宣言以外を加えない。 -/
theorem scan_filterMap (state : State n) (role : Nat) (t : Ty) (visible : List Declaration) :
    scan state role t visible = visible.filterMap (trial state role t) := by
  induction visible with
  | nil => rfl
  | cons first rest ih =>
      cases found : trial state role t first <;> simp [scan, found, ih]

theorem scan_permutation (state : State n) (role : Nat) (t : Ty)
    (reordered : first.Perm last) : (scan state role t first).Perm (scan state role t last) := by
  rw [scan_filterMap, scan_filterMap]
  exact reordered.filterMap _

/-- 候補順を替えてもK2の優先、未解決、候補数、唯一候補のpayloadが変わらない。 -/
theorem summarize_permutation (q : Request n) (first last : List Trial)
    (reordered : first.Perm last) : summarize q first = summarize q last := by
  have blocked : Trial.blocked ∈ first ↔ Trial.blocked ∈ last := reordered.mem_iff
  have deferred : Trial.deferred ∈ first ↔ Trial.deferred ∈ last := reordered.mem_iff
  have selected : (hits first).Perm (hits last) := reordered.filterMap _
  unfold summarize
  by_cases hb : Trial.blocked ∈ first
  · simp [hb, blocked.mp hb]
  · have hb' : Trial.blocked ∉ last := fun h => hb (blocked.mpr h)
    simp only [hb, hb', ↓reduceIte]
    by_cases hd : Trial.deferred ∈ first
    · simp [hd, deferred.mp hd]
    · have hd' : Trial.deferred ∉ last := fun h => hd (deferred.mpr h)
      simp only [hd, hd', ↓reduceIte]
      cases left : hits first with
      | nil =>
          have right : hits last = [] := List.perm_nil.mp (left ▸ selected.symm)
          simp [right]
      | cons entry rest =>
          cases rest with
          | nil =>
              have right : hits last = [entry] := List.perm_singleton.mp (left ▸ selected.symm)
              simp [right]
          | cons other tail =>
              have length := selected.length_eq
              rw [left] at length
              cases right : hits last with
              | nil => simp [right] at length
              | cons entry' rest' =>
                  cases rest' with
                  | nil => simp [right] at length
                  | cons other' tail' => rfl

/-- 一需要の全frontierが一致し、唯一候補の全where子列も一致する。 -/
theorem frontier_permutation (first last : List Declaration) (reordered : first.Perm last)
    (q : Request n) : frontier first q = frontier last q := by
  cases lower : q.lower with
  | none => simp [frontier, lower]
  | some t =>
      simp only [frontier, lower]
      rw [summarize_permutation q _ _ (scan_permutation q.state q.role t reordered)]

/-- 独立局所判断のiff。実行結果による再定義ではなく、既存exactnessを介した移送。 -/
theorem local_permutation (first last : List Declaration) (reordered : first.Perm last)
    (q : Request n) (outcome : CommonRoleOutermostResolver.Frontier (Request n)) :
    Local first q outcome ↔ Local last q outcome := by
  change (protocol first).Local q outcome ↔ (protocol last).Local q outcome
  rw [← frontier_exact first q outcome, ← frontier_exact last q outcome]
  change frontier first q = outcome ↔ frontier last q = outcome
  rw [frontier_permutation first last reordered q]

/-- 補助: 左側の宣言検査から得た下降だけで両treeを比較する。 -/
theorem resolve_permutation (first last : Registry)
    (reordered : first.declarations.Perm last.declarations) (q : Request n) :
    CommonRoleSettledResolver.resolve first q = CommonRoleSettledResolver.resolve last q := by
  induction (CommonRoleSettledResolver.accessible first q) with
  | intro q previous ih =>
      rw [CommonRoleSettledResolver.resolve_eq, CommonRoleSettledResolver.resolve_eq,
        ← frontier_permutation first.declarations last.declarations reordered q]
      split <;> try rfl
      rename_i key children selected
      congr 1
      apply List.map_congr_left
      intro child member
      exact ih child ⟨key, children, (frontier_exact first.declarations q _).mp selected, member⟩

/-- 元の四方向projectionも同じ。子failureを新しい仕様として認める主張ではない。 -/
theorem legacy_classification_permutation (first last : Registry)
    (reordered : first.declarations.Perm last.declarations) (q : Request n) :
    CommonRoleSettledResolver.classify first q = CommonRoleSettledResolver.classify last q := by
  unfold CommonRoleSettledResolver.classify
  rw [resolve_permutation first last reordered q]

/-- 拒否理由そのものも可視順に依存しない。 -/
theorem rejection_permutation (first last : Registry)
    (reordered : first.declarations.Perm last.declarations) (q : Request n) :
    CommonRoleSettledRootClassification.Rejection first.declarations q ↔
      CommonRoleSettledRootClassification.Rejection last.declarations q := by
  rw [← CommonRoleSettledRootClassification.rejected_exact first q,
    ← CommonRoleSettledRootClassification.rejected_exact last q,
    resolve_permutation first last reordered q]

end Yulang.CommonRoleSettledVisibleOrder
