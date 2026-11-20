import Yulang.GeneralRebaseRevisitedTrace298

namespace Yulang.GeneralRebaseFiniteSublists298

def choices : List α → List (List α)
 | [] => [[]]
 | a :: as => choices as ++ (choices as).map (a :: ·)

theorem choices_exact (xs ys : List α) : ys ∈ choices xs ↔ ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [choices]
  | cons a xs ih =>
    constructor
    · intro known
      rcases List.mem_append.mp known with left|right
      · exact (.cons a ((ih ys).mp left))
      · obtain ⟨zs,seen,rfl⟩ := List.mem_map.mp right
        exact .cons_cons a ((ih zs).mp seen)
    · intro sub
      cases sub with
      | cons a contained => exact List.mem_append_left _ ((ih _).mpr contained)
      | cons_cons a contained => exact List.mem_append_right _ (List.mem_map_of_mem ((ih _).mpr contained))

theorem choices_count (xs : List α) : (choices xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [choices,List.length_append,List.length_map,List.length_cons,ih,Nat.pow_succ,Nat.mul_two]

theorem samples_sourced (holds : Q → A → Prop) (qs : List Q) (a : A)
    (listed : a ∈ GeneralRebaseFiniteWitnessTable297.samples holds qs) :
    ∃ q ∈ qs, holds q a := by
  classical
  induction qs with
  | nil => cases listed
  | cons q qs ih =>
    by_cases found : ∃ b, holds q b
    · simp only [GeneralRebaseFiniteWitnessTable297.samples,dite_eq_left found] at listed
      rcases List.mem_cons.mp listed with rfl|tail
      · exact ⟨q,List.mem_cons_self ..,Classical.choose_spec found⟩
      · obtain ⟨item,mem,p⟩ := ih tail
        exact ⟨item,List.mem_cons_of_mem _ mem,p⟩
    · simp only [GeneralRebaseFiniteWitnessTable297.samples,dite_eq_right found] at listed
      obtain ⟨item,mem,p⟩ := ih listed
      exact ⟨item,List.mem_cons_of_mem _ mem,p⟩

end Yulang.GeneralRebaseFiniteSublists298
