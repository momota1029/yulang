import Yulang.GeneralFiniteColoredRounds306

namespace Yulang.GeneralFiniteColoredScore306
open GeneralFiniteColoredRounds306 (rounds Stationary monotone)
variable {α β : Type} [DecidableEq β]

def pairs (nodes : List α) : List (α × α) :=
  nodes.flatMap (fun x => nodes.map (fun y => (x,y)))

theorem mem_pairs (nodes : List α) (x y : α) :
    (x,y) ∈ pairs nodes ↔ x ∈ nodes ∧ y ∈ nodes := by
  simp only [pairs,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨a,am,b,bm,eq⟩
    cases eq
    exact ⟨am,bm⟩
  · rintro ⟨xm,ym⟩
    exact ⟨x,xm,y,ym,rfl⟩

def score (edges : α → List α) (observe : α → β) (nodes : List α) (n : Nat) : Nat :=
  (pairs nodes).countP (fun p => rounds edges observe n p.1 p.2)

theorem drop_count {γ : Type} {xs : List γ} {p q : γ → Bool}
    (mono : ∀ x ∈ xs, p x = true → q x = true)
    (lost : ∃ x ∈ xs, q x = true ∧ p x = false) :
    xs.countP p < xs.countP q := by
  induction xs with
  | nil => obtain ⟨_,member,_⟩ := lost; cases member
  | cons a rest ih =>
    obtain ⟨x,member,yes,no⟩ := lost
    have monoRest : ∀ z ∈ rest, p z = true → q z = true :=
      fun z h => mono z (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp member with rfl|inside
    · have le := List.countP_mono_left (l := rest) monoRest
      simp only [List.countP_cons,no,yes,ite_false,ite_true,Bool.false_eq_true,Nat.add_zero]
      omega
    · have less := ih monoRest ⟨x,inside,yes,no⟩
      have point := mono a (List.mem_cons_self ..)
      simp only [List.countP_cons]
      cases hp : p a <;> cases hq : q a <;> simp [hp,hq] at point ⊢ <;> omega

theorem strictly_drops {edges : α → List α} {observe : α → β} {nodes : List α} {n : Nat}
    (bad : ¬Stationary edges observe nodes n) : score edges observe nodes (n+1) < score edges observe nodes n := by
  apply drop_count (fun p _ => monotone n p.1 p.2)
  apply Classical.byContradiction
  intro none
  apply bad
  intro x xm y ym
  cases before : rounds edges observe n x y <;> cases after : rounds edges observe (n+1) x y
  · rfl
  · exact (Bool.false_ne_true (before.symm.trans (monotone n x y after))).elim
  · exact (none ⟨(x,y),(mem_pairs nodes x y).mpr ⟨xm,ym⟩,before,after⟩).elim
  · rfl

def fixedCheck (edges : α → List α) (observe : α → β) (nodes : List α) (n : Nat) : Bool :=
  (pairs nodes).all fun p => rounds edges observe (n+1) p.1 p.2 == rounds edges observe n p.1 p.2

theorem fixed_exact {edges : α → List α} {observe : α → β} {nodes : List α} {n : Nat} :
    fixedCheck edges observe nodes n = true ↔ Stationary edges observe nodes n := by
  unfold fixedCheck Stationary
  rw [List.all_eq_true]
  constructor
  · intro h x xm y ym
    exact eq_of_beq (h (x,y) ((mem_pairs nodes x y).mpr ⟨xm,ym⟩))
  · rintro h ⟨x,y⟩ member
    obtain ⟨xm,ym⟩ := (mem_pairs nodes x y).mp member
    exact beq_iff_eq.mpr (h x xm y ym)

end Yulang.GeneralFiniteColoredScore306
