import Yulang.GeneralDeclarativeCurrentHistory343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16800
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWithheldReceipt343
open GeneralDeclarativeCurrentWorld343 (now grows added new_constraints)
open GeneralDeclarativeCurrentOrigins343 (support no_promotion)
open GeneralDeclarativeFrameShape343 (b0 b1 edges retained_constraints exact_intervals)
open GeneralDeclarativeFrameRank343 (old_below)
open GeneralDeclarativeInitialModels343 (first_capture second_capture)
open GeneralDeclarativePlacement343 (view symbolic fresh_lower)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (child fresh)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open PresenceNormalForm (Atom)

/-- A counterfactual with the same full ordinary state and raw artifact,
but no completed-output authority. Initial authored support is not
withheld. This does not change actual run eligibility. -/
def withheld : Supported now (fun _ => False) :=
  ⟨(support grows).derivesFrom,(support grows).ordinary⟩

theorem only_source (row : Equation) (seen : row ∈ (restriction withheld).equations) :
    row = publicRow := by
  obtain ⟨origin,input,existsNow⟩ := (backed_iff withheld row).mp seen
  cases existsNow with
  | source => exact no_promotion grows input
  | completed never => exact False.elim never

theorem below0 {s : State} :
    0 < (GeneralDeclarativeAggregate324.span s kept typePoint []).lower :=
  old_below List.mem_cons_self s

theorem above0 {s : State} :
    0 < (GeneralDeclarativeAggregate324.span s kept typePoint []).upper := by
  have lo : 0 < (GeneralDeclarativeAggregate324.span s kept typePoint []).lower := below0
  change 0 < (GeneralDeclarativeAggregate324.span s kept typePoint []).lower + 1
  omega

theorem lower_source : symbolic.lower ≠ 0 := by
  have large := fresh_lower (show 0 ∈ kept from List.mem_cons_self)
  omega

theorem center_source : symbolic.center ≠ 0 := by
  have large : 0 < fresh kept := fresh_lower (show 0 ∈ kept from List.mem_cons_self)
  change fresh kept+1 ≠ 0
  omega

theorem upper_source : symbolic.upper ≠ 0 := by
  have large : 0 < fresh kept := fresh_lower (show 0 ∈ kept from List.mem_cons_self)
  change fresh kept+2 ≠ 0
  omega

private theorem group_no_zero (cap : Capture) (low : cap.lower ≠ 0) (high : cap.upper ≠ 0)
    {a b : Nat} (listed : Atom.tyLe (.var a) (.var b) ∈ edges cap) : a ≠ 0 ∧ b ≠ 0 := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with row|row|row|row|row|row|row|row <;> cases row <;> simp [low,high]

theorem terms_no_zero {a b : Nat} (listed : Atom.tyLe (.var a) (.var b) ∈ now.normal.ordinary) :
    a ≠ 0 ∧ b ≠ 0 := by
  rw [new_constraints,retained_constraints,List.mem_append,List.mem_append] at listed
  rcases listed with (base|last)|leaf
  · apply group_no_zero b0 ?_ ?_ base
    · change (GeneralDeclarativeLogicalChild343.capture kept 0).lower ≠ 0
      rw [first_capture]
      exact Nat.ne_of_gt below0
    · change (GeneralDeclarativeLogicalChild343.capture kept 0).upper ≠ 0
      rw [first_capture]
      exact Nat.ne_of_gt above0
  · apply group_no_zero b1 ?_ ?_ last
    · change (GeneralDeclarativeLogicalChild343.capture kept 1).lower ≠ 0
      rw [second_capture]
      exact Nat.ne_of_gt below0
    · change (GeneralDeclarativeLogicalChild343.capture kept 1).upper ≠ 0
      rw [second_capture]
      exact Nat.ne_of_gt above0
  · exact group_no_zero added (Nat.ne_of_gt below0) (Nat.ne_of_gt above0) leaf

theorem bound_isolated {a b : Nat} (checked : Bound now.normal a b) :
    (a = 0 ↔ b = 0) := by
  induction checked with
  | refl _ => rfl
  | trans _ _ start tail => exact start.trans tail
  | constraint current =>
    obtain ⟨aa,bb⟩ := terms_no_zero current
    exact ⟨fun h => False.elim (aa h),fun h => False.elim (bb h)⟩
  | interval current =>
    change (_,_) ∈ view.normal.intervals at current
    rw [exact_intervals] at current
    rcases List.mem_cons.mp current with early|late
    · cases early
      exact ⟨fun h => False.elim (lower_source h),fun h => False.elim (center_source h)⟩
    · cases List.mem_singleton.mp late
      exact ⟨fun h => False.elim (center_source h),fun h => False.elim (upper_source h)⟩

theorem isolated {a b : Nat} (link : Alias (restriction withheld) a b) :
    (a = 0 ↔ b = 0) := by
  induction link with
  | bounds low _ => exact bound_isolated low
  | trans _ _ start tail => exact start.trans tail
  | forward listed => cases congrArg Equation.right (only_source _ listed)
  | backward listed => cases congrArg Equation.right (only_source _ listed)

theorem not_anchored (row : Equation) (seen : row ∈ (restriction withheld).equations) :
    ¬ Alias (restriction withheld) symbolic.lower row.left := by
  intro linked
  have separated := isolated linked
  have is0 : row.left = 0 := congrArg Equation.left (only_source row seen)
  exact lower_source (separated.mpr is0)

theorem not_ready :
    ¬ GeneralDeclarativeTaggedElection340.Ready withheld (child kept) := by
  intro state
  obtain known|read := state symbolic List.mem_cons_self
  · obtain ⟨_,row,listed,linked,_⟩ := known
    exact not_anchored row listed linked
  · obtain ⟨_,_,_,⟨_,linked,listed⟩,_⟩ := read
    exact not_anchored _ listed linked

theorem cannot_use_truth_to_select (key : Nat) (children) :
    ¬ Rule withheld [] sourceRegistry interpretation waiting (child kept) (.selected key children) := by
  intro selected
  cases selected with
  | whole candidate => exact not_ready candidate.elected.ready

end Yulang.GeneralDeclarativeWithheldReceipt343
