import Yulang.GeneralDeclarativeI65I74OrderedProjectionCut464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias alias_mono)
open GeneralDeclarativeEntailment320 (appendFacts)

theorem original_raw_cycle_is_monotone_under_literal_rows
    {s t : State} (same : s.normal = t.normal) (inc : s.equations ⊆ t.equations)
    {a : Nat} (cycle : AliasCycle s (observed s) a) : AliasCycle t (observed t) a := by
  have step {v w} (ok : Descends (structural s) v w) : Descends (structural t) v w := by
    obtain ⟨h,⟨b,alias,term,atRow,packed⟩,child⟩ := ok
    exact ⟨h,⟨b,alias_mono same inc alias,term,inc atRow,packed⟩,child⟩
  have walk {v w} (ok : Path (structural s) v w) : Path (structural t) v w := by
    induction ok with
    | refl => exact .refl _
    | next one _ ih => exact .next (step one) ih
  obtain ⟨child,last,first,after,link⟩ := cycle
  exact ⟨child,last,step first,walk after,alias_mono same inc link⟩

theorem unfolding_full_named_batch_is_exact_ordered_target
    {s t : State} {es : List Equation} (h : OrderedSafeAppends s es t) :
    t = appendFacts s es := by
  obtain ⟨normal,rows⟩ := literal_row_order_and_ordinary_constraints_are_exact h
  cases t; cases s
  simp_all [appendFacts]

/-- A closed criterion for a supplied batch. Ordinal order is retained in the
output, but the existence of a finite safety replay can be characterized
using the final named snapshot. No independent check against only the
initial snapshot is being asserted. -/
theorem whole_named_batch_safety_iff_every_touched_final_root_is_safe
    (s : State) (es : List Equation) :
    OrderedSafeAppends s es (appendFacts s es) ↔
      (∀ e ∈ es, ∃ h, shapeOf e.right = some h) ∧
      (∀ e ∈ es, ¬AliasCycle (appendFacts s es) (observed (appendFacts s es)) e.left) := by
  constructor
  · intro run
    have statement {s t : State} {es : List Equation} (h : OrderedSafeAppends s es t) :
        (∀ e ∈ es, ∃ h, shapeOf e.right = some h) ∧
        (∀ e ∈ es, ¬AliasCycle t (observed t) e.left) := by
      induction h with
      | done => simp
      | @thenRow form s r es t shape safe noReturn after ih =>
        refine ⟨?_,?_⟩
        · intro e member
          rcases List.mem_cons.mp member with eq|later
          · exact eq.symm ▸ ⟨form,shape⟩
          · exact ih.1 e later
        · intro e member
          rcases List.mem_cons.mp member with eq|later
          · subst e
            have unchanged := accepted_batch_preserves_every_exact_original_k2 (.thenRow shape safe noReturn after) r.left
            exact fun newCycle => safe (unchanged.mp newCycle)
          · exact ih.2 e later
    exact statement run
  · induction es generalizing s with
    | nil =>
      intro _
      have e : appendFacts s [] = s := by cases s; simp [appendFacts]
      rw [e]
      exact .done
    | cons first rest ih =>
      rintro ⟨allShapes,allSafe⟩
      obtain ⟨form,shape⟩ := allShapes first List.mem_cons_self
      have finalSafe := allSafe first List.mem_cons_self
      have addFinal : (extendedRows s first).equations ⊆ (appendFacts s (first::rest)).equations := by
        intro row member
        change row ∈ s.equations ++ [first] at member
        change row ∈ s.equations ++ first::rest
        rcases List.mem_append.mp member with before|later
        · exact List.mem_append_left _ before
        · have eq := List.mem_singleton.mp later
          subst row
          exact List.mem_append_right _ List.mem_cons_self
      have afterFirst : ¬AliasCycle (extendedRows s first) (observed (extendedRows s first)) first.left :=
        fun h => finalSafe (original_raw_cycle_is_monotone_under_literal_rows
          (s := extendedRows s first) (t := appendFacts s (first::rest)) rfl addFinal h)
      have exactOne := (physical_new_row_root_cycle_exactly_old_or_old_return_from_child
        (s := s) (site := first.left) (term := first.right) shape)
      have noRoot : ¬AliasCycle s (observed s) first.left := fun old => by
        apply afterFirst
        have same : (⟨first.left,first.right⟩ : Equation) = first := by cases first; rfl
        rw [← same]
        exact exactOne.mpr (.inl old)
      have nonreturns : ∀ child ∈ form.children, ∀ a, Alias s a first.left →
          ¬Path (structural s) child a := by
        intro child belongs a alias path
        apply afterFirst
        have same : (⟨first.left,first.right⟩ : Equation) = first := by cases first; rfl
        rw [← same]
        exact exactOne.mpr (.inr ⟨child,belongs,a,alias,path⟩)
      have combined : appendFacts (extendedRows s first) rest = appendFacts s (first::rest) := by
        cases s
        simp [appendFacts,extendedRows,List.append_assoc]
      refine .thenRow shape noRoot nonreturns ?_
      rw [← combined]
      apply ih _
      refine ⟨fun e member => allShapes e (List.mem_cons_of_mem _ member),?_⟩
      intro e member
      rw [combined]
      exact allSafe e (List.mem_cons_of_mem _ member)

/-- A permutation changes the physical ordinals, not which supplied row
sets are certifiable in this cut. No report/display choice is made. -/
theorem certified_batch_feasibility_is_invariant_under_literal_permutation
    (s : State) {xs ys : List Equation} (order : xs.Perm ys) :
    (∃ w, w.map CheckedAppendData.row = xs ∧
      readOrderedAppends s w = some (appendFacts s xs)) ↔
    (∃ w, w.map CheckedAppendData.row = ys ∧
      readOrderedAppends s w = some (appendFacts s ys)) := by
  rw [← ordered_append_exact_independent_guard,←ordered_append_exact_independent_guard,
    whole_named_batch_safety_iff_every_touched_final_root_is_safe,
    whole_named_batch_safety_iff_every_touched_final_root_is_safe]
  have rows (e : Equation) : e ∈ (appendFacts s xs).equations ↔ e ∈ (appendFacts s ys).equations := by
    dsimp [appendFacts]
    simp only [List.mem_append,order.mem_iff]
  have sameCycle (i : Nat) :
      AliasCycle (appendFacts s xs) (observed (appendFacts s xs)) i ↔
      AliasCycle (appendFacts s ys) (observed (appendFacts s ys)) i :=
    ⟨original_raw_cycle_is_monotone_under_literal_rows (s := appendFacts s xs)
        (t := appendFacts s ys) rfl (fun e h => (rows e).mp h),
      original_raw_cycle_is_monotone_under_literal_rows (s := appendFacts s ys)
        (t := appendFacts s xs) rfl (fun e h => (rows e).mpr h)⟩
  constructor
  · rintro ⟨shape,safe⟩
    exact ⟨fun e h => shape e (order.mem_iff.mpr h),
      fun e h yes => safe e (order.mem_iff.mpr h) ((sameCycle _).mpr yes)⟩
  · rintro ⟨shape,safe⟩
    exact ⟨fun e h => shape e (order.mem_iff.mp h),
      fun e h yes => safe e (order.mem_iff.mp h) ((sameCycle _).mp yes)⟩

end Yulang.GeneralDeclarativeK2Graph321.AddAtOneSource
