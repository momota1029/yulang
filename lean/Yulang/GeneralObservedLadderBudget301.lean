import Yulang.GeneralObservedLadderScopedB4301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderBudget301
open GeneralObservedLadderInitial301 (initial)
open GeneralObservedLadderAdvance301 (run phase_step)
open GeneralObservedLadderEvidence301 (final dictionary)
open GeneralObservedLadderExact301 (only_step phases_distinct halted)
open GeneralObservedLadderScopedB4301 (compiled_at_terminal)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open CommonRoleOutermostResolver (Dictionary)

abbrev RawStep := (boundary roles).Step registry displayRoot

/-- An explicit length index for the raw path relation; unlike reader
fuel, it charges every actual source-boundary transition, not dictionary nodes. -/
inductive Counted : Nat → State roles → State roles → Prop
  | refl (s : State roles) : Counted 0 s s
  | tail : Counted count start mid → RawStep mid last → Counted (count+1) start last

theorem erase {l : Nat} {before after : State roles} (path : Counted l before after) :
    B4Target.Steps RawStep before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih step

theorem count_path (n start : Nat) (startBound : start ≤ n+1) {count : Nat} {s : State roles}
    (path : Counted count (run n start startBound).state s) :
    ∃ fit : start+count ≤ n+1, s = (run n (start+count) fit).state := by
  have gen {l} {a b : State roles} (track : Counted l a b) (beginAt : a = (run n start startBound).state) :
      ∃ fit : start+l ≤ n+1, b = (run n (start+l) fit).state := by
    induction track with
    | refl => exact ⟨by omega,beginAt⟩
    | tail _ step ih =>
      obtain ⟨fit,rfl⟩ := ih beginAt
      obtain ⟨go,ends⟩ := only_step n _ fit _ step
      exact ⟨by omega,ends⟩
  exact gen path rfl

theorem path_exists (n start len : Nat) (fit : start+len ≤ n+1) :
    Counted len (run n start (by omega)).state (run n (start+len) fit).state := by
  induction len with
  | zero => exact .refl _
  | succ len ih =>
    exact .tail (ih (by omega)) (phase_step n (start+len) (by omega))

theorem exact_count (n start stop len : Nat) (left : start ≤ n+1) (right : stop ≤ n+1) :
    Counted len (run n start left).state (run n stop right).state ↔ stop = start+len := by
  constructor
  · intro path
    obtain ⟨fit,eq⟩ := count_path n start left path
    exact phases_distinct n stop (start+len) right fit eq
  · rintro rfl
    exact path_exists n start len right

theorem completion (n k : Nat) (cap : k ≤ n+1) :
    Counted (n+1-k) (run n k cap).state (final n).state ∧
    (∀ last, ¬ RawStep (final n).state last) ∧
    GeneralGeneratedDictionaryRun299.run
      (GeneralObservedLadderJournalCompiler301.table (final n).state) (n+2) 0 =
      some (dictionary (n+1)) := by
  refine ⟨(exact_count n k (n+1) (n+1-k) cap (Nat.le_refl _)).mpr (by omega),halted n,?_⟩
  rw [GeneralObservedLadderJournalCompiler301.exact_final]
  exact GeneralObservedLadderReadback301.computed n

theorem remaining_exact (n start count : Nat) (cap : start ≤ n+1) (s : State roles)
    (path : Counted count (run n start cap).state s)
    (noMore : ∀ next, ¬ RawStep s next) : count = n+1-start := by
  obtain ⟨bound,rfl⟩ := count_path n start cap path
  by_cases before : start+count ≤ n
  · exact False.elim (noMore _ (phase_step n _ before))
  · omega

theorem exact_initial_budget (n count : Nat) (s : State roles)
    (path : Counted count (initial n) s)
    (noMore : ∀ next, ¬ RawStep s next) :
    count = n+1 ∧ s = (final n).state := by
  have time := remaining_exact n 0 count (by omega) s path noMore
  have countEq : count = n+1 := by simpa using time
  exact ⟨countEq,GeneralObservedLadderScopedB4301.closure_of_any_terminal n s (erase path) noMore⟩

end Yulang.GeneralObservedLadderBudget301
