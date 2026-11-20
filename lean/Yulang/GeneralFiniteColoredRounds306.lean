import Yulang.GeneralFiniteBisimRefinement306

namespace Yulang.GeneralFiniteColoredRounds306
open GeneralFiniteBisimRefinement306 (refine)
variable {α β : Type} [DecidableEq β]

def paint (observe : α → β) (x y : α) : Bool := decide (observe x = observe y)

def rounds (edges : α → List α) (observe : α → β) : Nat → α → α → Bool
  | 0 => paint observe
  | n+1 => fun x y => paint observe x y && refine edges (rounds edges observe n) x y

def Closed (edges : α → List α) (nodes : List α) : Prop :=
  ∀ s ∈ nodes, ∀ t ∈ edges s, t ∈ nodes

def On (edges : α → List α) (observe : α → β) (nodes : List α) (rel : α → α → Prop) : Prop :=
  ∀ x ∈ nodes, ∀ y ∈ nodes, rel x y →
    observe x = observe y ∧
      (∀ a ∈ edges x, ∃ b ∈ edges y, rel a b) ∧
      (∀ b ∈ edges y, ∃ a ∈ edges x, rel a b)

theorem expand {edges : α → List α} {observe : α → β} {n : Nat} {x y : α} :
    rounds edges observe (n+1) x y = true ↔
    observe x = observe y ∧
      (∀ a ∈ edges x, ∃ b ∈ edges y, rounds edges observe n a b = true) ∧
      (∀ b ∈ edges y, ∃ a ∈ edges x, rounds edges observe n a b = true) := by
  simp only [rounds,refine,paint,Bool.and_eq_true_iff,decide_eq_true_eq,List.all_eq_true,List.any_eq_true]

theorem shade {edges : α → List α} {observe : α → β} {n : Nat} {x y : α}
    (h : rounds edges observe n x y = true) : observe x = observe y := by
  cases n
  · exact of_decide_eq_true h
  · exact (expand.mp h).1

theorem monotone {edges : α → List α} {observe : α → β} (n : Nat) (x y : α)
    (next : rounds edges observe (n+1) x y = true) : rounds edges observe n x y = true := by
  induction n generalizing x y with
  | zero => exact decide_eq_true (shade next)
  | succ n ih =>
    obtain ⟨color,forward,back⟩ := expand.mp next
    refine expand.mpr ⟨color,?_,?_⟩
    · intro a member
      obtain ⟨b,listed,h⟩ := forward a member
      exact ⟨b,listed,ih a b h⟩
    · intro b member
      obtain ⟨a,listed,h⟩ := back b member
      exact ⟨a,listed,ih a b h⟩

theorem upper {edges : α → List α} {observe : α → β} {nodes : List α} {rel : α → α → Prop}
    (closure : Closed edges nodes) (bisim : On edges observe nodes rel)
    (n : Nat) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes) (h : rel x y) :
    rounds edges observe n x y = true := by
  induction n generalizing x y with
  | zero => exact decide_eq_true (bisim x xm y ym h).1
  | succ n ih =>
    obtain ⟨color,forward,back⟩ := bisim x xm y ym h
    refine expand.mpr ⟨color,?_,?_⟩
    · intro a member
      obtain ⟨b,listed,linked⟩ := forward a member
      exact ⟨b,listed,ih (closure x xm a member) (closure y ym b listed) linked⟩
    · intro b member
      obtain ⟨a,listed,linked⟩ := back b member
      exact ⟨a,listed,ih (closure x xm a listed) (closure y ym b member) linked⟩

def Stationary (edges : α → List α) (observe : α → β) (nodes : List α) (n : Nat) : Prop :=
  ∀ x ∈ nodes, ∀ y ∈ nodes, rounds edges observe (n+1) x y = rounds edges observe n x y

theorem stable_sound {edges : α → List α} {observe : α → β} {nodes : List α} {n : Nat}
    (fixed : Stationary edges observe nodes n) :
    On edges observe nodes (fun x y => rounds edges observe n x y = true) := by
  intro x xm y ym yes
  have next : rounds edges observe (n+1) x y = true := (fixed x xm y ym).symm ▸ yes
  exact expand.mp next

theorem stable_propagates {edges : α → List α} {observe : α → β} {nodes : List α} {n : Nat}
    (closure : Closed edges nodes) (fixed : Stationary edges observe nodes n) :
    Stationary edges observe nodes (n+1) := by
  intro x xm y ym
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact monotone (n+1) x y
  · intro h
    have R := stable_sound fixed
    have kept := upper closure R (n+2) xm ym
    exact kept (fixed x xm y ym ▸ h)

end Yulang.GeneralFiniteColoredRounds306
