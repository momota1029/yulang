import Yulang.GeneralMixedControlRank306

namespace Yulang.GeneralFiniteBisimRefinement306
variable {α : Type}

def Strong (edges : α → List α) (rel : α → α → Prop) : Prop :=
  ∀ x y, rel x y →
    (∀ a ∈ edges x, ∃ b ∈ edges y, rel a b) ∧
    (∀ b ∈ edges y, ∃ a ∈ edges x, rel a b)

def refine (edges : α → List α) (old : α → α → Bool) (x y : α) : Bool :=
  (edges x).all (fun a => (edges y).any (old a)) &&
  (edges y).all (fun b => (edges x).any (fun a => old a b))

def rounds (edges : α → List α) : Nat → α → α → Bool
  | 0 => fun _ _ => true
  | n+1 => refine edges (rounds edges n)

theorem retains {edges : α → List α} {rel : α → α → Prop}
    (bisim : Strong edges rel) (n : Nat) (x y : α) (h : rel x y) :
    rounds edges n x y = true := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    refine Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr ?_,List.all_eq_true.mpr ?_⟩
    · intro a member
      obtain ⟨b,listed,related⟩ := (bisim x y h).1 a member
      exact List.any_eq_true.mpr ⟨b,listed,ih a b related⟩
    · intro b member
      obtain ⟨a,listed,related⟩ := (bisim x y h).2 b member
      exact List.any_eq_true.mpr ⟨a,listed,ih a b related⟩

/-- Each finite-depth approximation is coarser than the next. This alone
does not turn a depth-limited result into a stable arbitrary quotient. -/
theorem descends (edges : α → List α) (n : Nat) (x y : α)
    (next : rounds edges (n+1) x y = true) : rounds edges n x y = true := by
  induction n generalizing x y with
  | zero => rfl
  | succ k ih =>
    obtain ⟨forth,back⟩ := Bool.and_eq_true_iff.mp next
    refine Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr ?_,List.all_eq_true.mpr ?_⟩
    · intro a member
      obtain ⟨b,listed,rel⟩ := List.any_eq_true.mp (List.all_eq_true.mp forth a member)
      exact List.any_eq_true.mpr ⟨b,listed,ih a b rel⟩
    · intro b member
      obtain ⟨a,listed,rel⟩ := List.any_eq_true.mp (List.all_eq_true.mp back b member)
      exact List.any_eq_true.mpr ⟨a,listed,ih a b rel⟩

end Yulang.GeneralFiniteBisimRefinement306
