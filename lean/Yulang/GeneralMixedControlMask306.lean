import Yulang.GeneralMixedControlAtoms306

namespace Yulang.GeneralMixedControlMask306
open GeneralNominalState (Known)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralNominalVersionedJournal232 (State)
open GeneralDictionaryOutputDepth252 (roles)

@[ext] structure Mask where
  zero : Bool
  one : Bool
  deriving DecidableEq, Repr

def get (m : Mask) (i : Fin 2) : Bool := if i.val = 0 then m.zero else m.one

def bits (f : Fin 2 → Bool) : Mask := ⟨f 0,f 1⟩

theorem get_bits (f : Fin 2 → Bool) (i : Fin 2) : get (bits f) i = f i := by
  have each : i = 0 ∨ i = 1 := by
    have small : i.val = 0 ∨ i.val = 1 := by omega
    exact small.imp Fin.ext Fin.ext
  rcases each with rfl|rfl <;> rfl

def seen (s : GeneralNominalState.State) (n : Nat) : Bool :=
  (List.ofFn fun i : Fin s.base.slots =>
    decide (s.base.source i = n) &&
      (decide (s.view.graph i ≠ .unresolved) || (s.nominals i).isSome)).any id

theorem seen_exact (s : GeneralNominalState.State) (n : Nat) : seen s n = true ↔ Known s n := by
  constructor
  · intro yes
    obtain ⟨b,listed,hit⟩ := List.any_eq_true.mp yes
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp listed
    have test : (decide (s.base.source i = n) &&
        (decide (s.view.graph i ≠ .unresolved) || (s.nominals i).isSome)) = true :=
      eq.trans hit
    obtain ⟨source,disj⟩ := Bool.and_eq_true_iff.mp test
    refine ⟨i,of_decide_eq_true source,?_⟩
    cases Bool.or_eq_true_iff.mp disj with
    | inl head => exact Or.inl (of_decide_eq_true head)
    | inr nominal =>
      cases eqn : s.nominals i with
      | none => simp [eqn] at nominal
      | some d => exact Or.inr ⟨d,rfl⟩
  · rintro ⟨i,source,head|⟨d,nominal⟩⟩
    · exact List.any_eq_true.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
        Bool.and_eq_true_iff.mpr ⟨decide_eq_true source,
          Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true head))⟩⟩
    · exact List.any_eq_true.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
        Bool.and_eq_true_iff.mpr ⟨decide_eq_true source,
          Bool.or_eq_true_iff.mpr (Or.inr (by simp [nominal]))⟩⟩

def project (s : State roles) : Mask := bits fun i => seen (snapshot s) i.val

theorem bit (s : State roles) (i : Fin 2) : get (project s) i = true ↔ Known (snapshot s) i.val := by
  unfold project
  rw [get_bits,seen_exact]

theorem missing (s : State roles) (i : Fin 2) : get (project s) i = false ↔ ¬ Known (snapshot s) i.val := by
  rw [← bit]
  cases get (project s) i <;> simp

def monotone (x y : Mask) : Bool := (!x.zero || y.zero) && (!x.one || y.one)

theorem monotone_exact (x y : Mask) : monotone x y = true ↔
    ∀ i : Fin 2, get x i = true → get y i = true := by
  constructor
  · intro all i hi
    have yes := Bool.and_eq_true_iff.mp all
    have each : i = 0 ∨ i = 1 := by
      have small : i.val = 0 ∨ i.val = 1 := by omega
      exact small.imp Fin.ext Fin.ext
    rcases each with rfl|rfl
    · change x.zero = true at hi
      change y.zero = true
      simpa [hi] using yes.1
    · change x.one = true at hi
      change y.one = true
      simpa [hi] using yes.2
  · intro all
    have z : x.zero = true → y.zero = true := all 0
    have o : x.one = true → y.one = true := all 1
    cases x <;> cases y
    simp only [monotone] at *
    rename_i xz xo yz yo
    cases xz <;> cases xo <;> cases yz <;> cases yo <;> simp_all

def fire (which : Fin 2) (x y : Mask) : Bool := monotone x y && !get x which && get y which

theorem fire_exact (which : Fin 2) (x y : Mask) : fire which x y = true ↔
    (∀ i : Fin 2, get x i = true → get y i = true) ∧ get x which = false ∧ get y which = true := by
  simp only [fire,Bool.and_eq_true,Bool.not_eq_true',monotone_exact,and_assoc]

def moves (x y : Mask) : Bool := fire 0 x y || fire 1 x y

theorem moves_exact (x y : Mask) : moves x y = true ↔ ∃ which : Fin 2, fire which x y = true := by
  constructor
  · intro yes
    cases Bool.or_eq_true_iff.mp yes with
    | inl z => exact ⟨0,z⟩
    | inr o => exact ⟨1,o⟩
  · rintro ⟨i,h⟩
    have small : i.val = 0 ∨ i.val = 1 := by omega
    rcases small.imp (Fin.ext (b := 0)) (Fin.ext (b := 1)) with rfl|rfl
    · exact Bool.or_eq_true_iff.mpr (Or.inl h)
    · exact Bool.or_eq_true_iff.mpr (Or.inr h)

def rank (x : Mask) : Nat := (if x.zero then 0 else 1) + (if x.one then 0 else 1)

end Yulang.GeneralMixedControlMask306
