import Yulang.GeneralDeclarativeI65CertifiedWhereInputs401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonDeclaredNominalInspection (Kind)
open GeneralDeclarativeWhere319 (Capture)


/-- Forward simulation of successful mixed typed substitution.
Branching and annotation provenance are exactly the *same* tree;
no use of Pattern equality to identify different catalogues. -/
theorem mixed_success_transports_same_tree401 {s c p} {leaf mid dst : Kind → Nat → Type}
    (first : ∀ k n, leaf k n → Option (mid k n))
    (later : ∀ k n, mid k n → dst k n)
    (direct : ∀ k n, leaf k n → Option (dst k n))
    (step : ∀ k n x y, first k n x = some y → direct k n x = some (later k n y))
    (plan : MixedRhs401 s leaf c p) :
    ∀ named, substituteMixedRhs401 first plan = some named →
      substituteMixedRhs401 (fun k n x => some (later k n x)) named =
        substituteMixedRhs401 direct plan := by
  refine MixedRhs401.rec
    (motive_1 := fun _ _ tree => ∀ named, substituteMixedRhs401 first tree = some named →
      substituteMixedRhs401 (fun k n x => some (later k n x)) named = substituteMixedRhs401 direct tree)
    (motive_2 := fun _ _ _ tree => ∀ named, substituteMixedArg401 first tree = some named →
      substituteMixedArg401 (fun k n x => some (later k n x)) named = substituteMixedArg401 direct tree)
    (motive_3 := fun _ _ _ tree => ∀ named, substituteMixedArgs401 first tree = some named →
      substituteMixedArgs401 (fun k n x => some (later k n x)) named = substituteMixedArgs401 direct tree)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro c n x result made
    cases h : first .value n x <;> simp [substituteMixedRhs401,h] at made
    subst result
    simp [substituteMixedRhs401,step _ _ _ _ h]
  · intro c p q label a b ha hb result made
    cases ax : substituteMixedRhs401 first a <;> cases bx : substituteMixedRhs401 first b <;>
      simp [substituteMixedRhs401,ax,bx] at made
    subst result
    simp only [substituteMixedRhs401,ha _ ax,hb _ bx]
  · intro c p tag a ha result made
    cases ax : substituteMixedRhs401 first a <;> simp [substituteMixedRhs401,ax] at made
    subst result
    simp only [substituteMixedRhs401,ha _ ax]
  · intro c p q a b ha hb result made
    cases ax : substituteMixedRhs401 first a <;> cases bx : substituteMixedRhs401 first b <;>
      simp [substituteMixedRhs401,ax,bx] at made
    subst result
    simp only [substituteMixedRhs401,ha _ ax,hb _ bx]
  · intro ps c params n use kinds exacts a ha result made
    cases ax : substituteMixedArgs401 first a <;> simp [substituteMixedRhs401,ax] at made
    subst result
    simp only [substituteMixedRhs401,ha _ ax]
  · intro c n base use kind result made
    change _ = some result at made
    injection made with eq
    subst result
    rfl
  · intro c n use kind result made
    injection made with eq
    subst result
    rfl
  · intro c n use kind result made
    injection made with eq
    subst result
    rfl
  · intro c a b n use prim x y hx hy result made
    cases ax : substituteMixedRhs401 first x <;> cases bx : substituteMixedRhs401 first y <;>
      simp [substituteMixedRhs401,ax,bx] at made
    subst result
    simp only [substituteMixedRhs401,hx _ ax,hy _ bx]
  · intro c p n kind mode x result made
    cases h : first .value n x <;> simp [substituteMixedArg401,h] at made
    subst result
    simp [substituteMixedArg401,step _ _ _ _ h]
  · intro c p n kind mode x result made
    cases h : first .value n x <;> simp [substituteMixedArg401,h] at made
    subst result
    simp [substituteMixedArg401,step _ _ _ _ h]
  · intro c p n kind mode x result made
    cases h : first .row n x <;> simp [substituteMixedArg401,h] at made
    subst result
    simp [substituteMixedArg401,step _ _ _ _ h]
  · intro c p n kind mode x result made
    cases h : first .row n x <;> simp [substituteMixedArg401,h] at made
    subst result
    simp [substituteMixedArg401,step _ _ _ _ h]
  · intro p pat c kind comp child ih result made
    cases ax : substituteMixedRhs401 first child <;> simp [substituteMixedArg401,ax] at made
    subst result
    simp only [substituteMixedArg401,ih _ ax]
  · intro c result made
    injection made with eq
    subst result
    rfl
  · intro c p ps a as firstArg laterArgs ha hb result made
    cases ax : substituteMixedArg401 first firstArg <;> cases bx : substituteMixedArgs401 first laterArgs <;>
      simp [substituteMixedArgs401,ax,bx] at made
    subst result
    simp only [substituteMixedArgs401,ha _ ax,hb _ bx]

def forgetMixedQualification401 {s slots} (k : Kind) (n : Nat)
    (read : InstantiatedSlot401 s slots k n) : NamedSlot401 slots k n :=
  ⟨read.original,read.source⟩

/-- Exact syntactic compatibility: when independently qualified
bound tickets exist, deleting only their proofs recovers precisely
the same retained B6 tree and all three source names at each leaf. -/
theorem qualified_tree_erases_only_proofs401 {s c p} {slots : Nat → Option Capture}
    (plan : B6MixedRhs401 s c p) (qualified : RetainedTree401 s slots c p)
    (made : substituteMixedRhs401 (instantiateMixedSlot401 (s := s) slots) plan = some qualified) :
    substituteMixedRhs401 (fun k n x => some (forgetMixedQualification401 k n x)) qualified =
      substituteMixedRhs401 (instantiateName401 slots) plan := by
  apply mixed_success_transports_same_tree401
    (instantiateMixedSlot401 (s := s) slots) forgetMixedQualification401 (instantiateName401 slots)
    _ plan qualified made
  intro k n x y _
  cases x
  exact instantiateName401_of_some y.source

/-- Lexical substitution cannot counterfeit the endpoint qualification.
This result refers to no extra accepted or rejected language case. -/
theorem exact_name_does_not_supply_bound_ticket401 {s} {slots : Nat → Option Capture} {k n cap}
    (got : slots n = some cap) (unsupported : ¬TypedBodyCapture392 s cap k) :
    instantiateName401 slots k n () = some ⟨cap,got⟩ ∧
      instantiateMixedSlot401 (s := s) slots k n () = none := by
  classical
  refine ⟨instantiateName401_of_some got,?_⟩
  unfold instantiateMixedSlot401
  split
  next missed => rw [got] at missed
  next actual source =>
    have eq := Option.some.inj (source.symm.trans got)
    subst actual
    simp [unsupported]

end Yulang.GeneralDeclarativeI65
