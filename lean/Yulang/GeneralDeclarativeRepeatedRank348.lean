import Yulang.GeneralDeclarativeRepeatedLayout348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 36000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeRepeatedRank348
open GeneralDeclarativeRepeatedLayout348 (first second logical e0 e1 e2 duplicateEdges ordinary intervals written)
open GeneralDeclarativeRepeatedPlacement348 (keep placedView links)
open GeneralDeclarativeReplayStage348 (capture phase tied exact_capture exact_phase)
open GeneralDeclarativeReplayCompile348 (protect)
open GeneralDeclarativeLogicalChild343 (jobs)
open GeneralDeclarativeVersionedRootShape342 (typePoint)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeNewNames321 (before_after)
open GeneralDeclarativeAggregate324 (span ready aligned)
open GeneralDeclarativeFreshTerms324 (protectedNames)
open GeneralDeclarativeFootprint321 (stateNames atomSources)
open GeneralDeclarativeTaggedElection340 (Ranked)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeBounds319 (Bound)
open GeneralWhereVersionCase317 (lower upper)
open GeneralMixedCompoundChildEquality307 (mid)
open PresenceNormalForm (Atom)

noncomputable abbrev lowNames := [2,first.lower,first.upper,second.lower,second.upper]
noncomputable def level (n : Nat) : Nat := if n ∈ lowNames then 0 else 1

theorem low {n : Nat} (h : n ∈ lowNames) : level n = 0 := by simp [level,h]
theorem high {n : Nat} (h : n ∉ lowNames) : level n = 1 := by simp [level,h]
theorem two : level 2 = 0 := low List.mem_cons_self
theorem lowFirst : level first.lower = 0 := low (List.mem_cons_of_mem _ List.mem_cons_self)
theorem highFirst : level first.upper = 0 := low (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem lowSecond : level second.lower = 0 := low (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
theorem highSecond : level second.upper = 0 := low (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem keep_lt {n : Nat} (h : n ∈ keep) (state : State) :
    n < (span state keep typePoint [typePoint]).lower := by
  unfold span GeneralDeclarativeFreshTerms324.first
  apply before_after
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ h)))

theorem from_keep {n : Nat} (h : n ∈ keep) (notTwo : n ≠ 2) : level n = 1 := by
  apply high
  intro seen
  have a := keep_lt h tied
  rw [← exact_capture keep] at a
  change n < first.lower at a
  have b := keep_lt h (ready tied keep typePoint [typePoint])
  change n < second.lower at b
  have hi0 : first.upper = first.lower + 1 := by
    change (capture keep 0).upper = (capture keep 0).lower + 1
    rw [exact_capture]
    rfl
  have hi1 : second.upper = second.lower + 1 := rfl
  simp only [lowNames,List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with here|here|here|here|here <;> omega

theorem root : level 0 = 1 := from_keep List.mem_cons_self (by decide)

theorem raw_levels : level lower = 1 ∧ level mid = 1 ∧ level upper = 1 := by
  have lo : 4 < lower := GeneralNominalIdentities.source_above_seed _ _
  have middle : 4 < mid := GeneralNominalIdentities.source_above_seed _ _
  have hi : 4 < upper := GeneralNominalIdentities.source_above_seed _ _
  refine ⟨from_keep ?_ (by omega),from_keep ?_ (by omega),from_keep ?_ (by omega)⟩ <;> unfold keep <;>
    apply List.mem_append_left _
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem phase_edges : (phase keep).normal.ordinary = duplicateEdges first ++ duplicateEdges second := rfl

private theorem present_phase {n : Nat} (h : n ∈ lowNames) : n ∈ stateNames (phase keep) := by
  unfold stateNames
  apply List.mem_append_left _
  apply List.mem_append_left _
  rw [phase_edges,List.flatMap_append]
  simp only [lowNames,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.tyLe (.var 2) (.var 2),List.mem_cons_self,List.mem_cons_self⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.tyLe (.var first.lower) (.union (.var 2) (.var 2)),by simp [duplicateEdges],List.mem_cons_self⟩)
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨.tyLe (.var first.upper) (.inter (.var 2) (.var 2)),by simp [duplicateEdges],List.mem_cons_self⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.tyLe (.var second.lower) (.union (.var 2) (.var 2)),by simp [duplicateEdges],List.mem_cons_self⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.tyLe (.var second.upper) (.inter (.var 2) (.var 2)),by simp [duplicateEdges],List.mem_cons_self⟩)

noncomputable abbrev fresh := GeneralDeclarativeFreshWhere325.seed (phase keep) (protect keep) (capture keep) jobs

theorem phase_lt {n : Nat} (h : n ∈ lowNames) : n < fresh := by
  unfold fresh GeneralDeclarativeFreshWhere325.seed
  apply before_after
  exact List.mem_append_left _ (List.mem_append_left _ (present_phase h))

theorem logical_levels :
    level logical.lower = 1 ∧ level logical.center = 1 ∧ level logical.upper = 1 := by
  refine ⟨high ?_,high ?_,high ?_⟩ <;> intro h
  · have l := phase_lt h
    change fresh < fresh at l
    omega
  · have l := phase_lt h
    change fresh+1 < fresh at l
    omega
  · have l := phase_lt h
    change fresh+2 < fresh at l
    omega

private theorem edge {a b : Nat} (c : Capture) (l : level c.lower = 0) (u : level c.upper = 0)
    (h : Atom.tyLe (.var a) (.var b) ∈ duplicateEdges c) : level a ≤ level b := by
  simp only [duplicateEdges,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with x|x|x|x|x|x|x|x|x|x <;> cases x <;> simp only [two,l,u,Nat.le_refl]

theorem bounded {a b : Nat} (h : Bound placedView.normal a b) : level a ≤ level b := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | trans _ _ x y => exact Nat.le_trans x y
  | constraint row =>
    rw [ordinary,List.mem_append] at row
    exact row.elim (edge first lowFirst highFirst) (edge second lowSecond highSecond)
  | interval there =>
    rw [intervals] at there
    rcases List.mem_cons.mp there with x|y
    · cases x
      simp only [logical_levels.1,logical_levels.2.1,Nat.le_refl]
    · cases List.mem_singleton.mp y
      simp only [logical_levels.2.1,logical_levels.2.2,Nat.le_refl]

theorem flat {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ placedView.equations) : level a = level b := by
  rw [written] at h
  simp only [links,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with x|x|x|x|x|x|x|x <;> cases x
  · exact raw_levels.1.trans logical_levels.1.symm
  · exact raw_levels.2.1.trans logical_levels.2.1.symm
  · exact raw_levels.2.2.trans logical_levels.2.2.symm

theorem compound (row : Equation) (h : row ∈ placedView.equations) (n : Nat)
    (used : n ∈ names row.right) (notVar : ∀ b,row.right ≠ .variable b) : level n < level row.left := by
  rw [written] at h
  simp only [links,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have t : n ∈ [2,2] := used
    have q := (List.mem_cons.mp t).elim id List.mem_singleton.mp
    subst n
    change level 2 < level 0
    rw [two,root]
    decide
  · have q : n = first.lower := List.mem_singleton.mp used
    subst n
    change level first.lower < level logical.lower
    rw [lowFirst,logical_levels.1]
    decide
  · have q : n = 2 := List.mem_singleton.mp used
    subst n
    change level 2 < level logical.center
    rw [two,logical_levels.2.1]
    decide
  · have q : n = first.upper := List.mem_singleton.mp used
    subst n
    change level first.upper < level logical.upper
    rw [highFirst,logical_levels.2.2]
    decide
  · change n ∈ [] at used
    cases used
  · exact False.elim (notVar _ rfl)
  · exact False.elim (notVar _ rfl)
  · exact False.elim (notVar _ rfl)

theorem ranked : Ranked placedView level := ⟨bounded,flat,compound⟩

end Yulang.GeneralDeclarativeRepeatedRank348
