import Yulang.GeneralRebaseSignedModels297

namespace Yulang.GeneralRebaseFiniteWitnessTable297

/-- One materialized assignment for each inhabited question, with no global
bound on the assignment carrier. No ability to find that witness is assumed. -/
noncomputable def samples (holds : Q → A → Prop) : List Q → List A
  | [] => []
  | q :: qs => by
    classical
    exact if yes : ∃ a, holds q a then Classical.choose yes :: samples holds qs else samples holds qs

def Covers (holds : Q → A → Prop) (questions : List Q) (xs : List A) : Prop :=
  ∀ q ∈ questions, (∃ a, holds q a) → ∃ a ∈ xs, holds q a

theorem length_le (holds : Q → A → Prop) (questions : List Q) :
    (samples holds questions).length ≤ questions.length := by
  classical
  induction questions with
  | nil => exact Nat.le_refl 0
  | cons q rest ih =>
    by_cases h : ∃ a, holds q a
    · simp only [samples,dite_eq_left h,List.length_cons,Nat.add_le_add_iff_right]
      exact ih
    · simp only [samples,dite_eq_right h,List.length_cons]
      exact Nat.le_trans ih (Nat.le_succ _)

theorem covers (holds : Q → A → Prop) (questions : List Q) :
    Covers holds questions (samples holds questions) := by
  classical
  induction questions with
  | nil => intro q member; cases member
  | cons first rest ih =>
    intro q listed inhabited
    rcases List.mem_cons.mp listed with rfl | inside
    · exact ⟨Classical.choose inhabited,
      (by simp [samples,inhabited]),Classical.choose_spec inhabited⟩
    · obtain ⟨a,used,valid⟩ := ih q inside inhabited
      refine ⟨a,?_,valid⟩
      by_cases yes : ∃ a, holds first a
      · exact by simpa [samples,yes] using (List.mem_cons_of_mem (Classical.choose yes) used)
      · simpa [samples,yes] using used

def hit (xs : List A) (check : Q → A → Bool) (q : Q) : Bool := xs.any (check q)

theorem hit_true (holds : Q → A → Prop) (xs : List A) (check : Q → A → Bool) (q : Q)
    (reflect : ∀ a ∈ xs, check q a = true ↔ holds q a) :
    hit xs check q = true ↔ ∃ a ∈ xs, holds q a := by
  unfold hit
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a,listed,yes⟩
    exact ⟨a,listed,(reflect a listed).mp yes⟩
  · rintro ⟨a,listed,yes⟩
    exact ⟨a,listed,(reflect a listed).mpr yes⟩

theorem hit_exact (holds : Q → A → Prop) (questions : List Q) (xs : List A)
    (cover : Covers holds questions xs) (check : Q → A → Bool) (q : Q) (listed : q ∈ questions)
    (reflect : ∀ a ∈ xs, check q a = true ↔ holds q a) :
    hit xs check q = true ↔ ∃ a, holds q a :=
  (hit_true holds xs check q reflect).trans ⟨fun ⟨a,_,h⟩ => ⟨a,h⟩,cover q listed⟩

theorem hit_false (holds : Q → A → Prop) (questions : List Q) (xs : List A)
    (cover : Covers holds questions xs) (check : Q → A → Bool) (q : Q) (listed : q ∈ questions)
    (reflect : ∀ a ∈ xs, check q a = true ↔ holds q a) :
    hit xs check q = false ↔ ¬ ∃ a, holds q a := by
  exact Bool.eq_false_iff.trans (not_congr (hit_exact holds questions xs cover check q listed reflect))

end Yulang.GeneralRebaseFiniteWitnessTable297
