import Yulang.GeneralRebaseReceiptCollision289

/-! The extended gate compares exact entries at the finite nominal
footprint of the raw snapshot. It also filters the producer effect on the
same key list. This is not equality of arbitrary catalogue functions. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28800
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptCatalogue289
open GeneralDeclarationPatterns (Constructors Constructor)
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Wire Offer Decision check)
open GeneralRebaseReceiptExtract289 (extract effectSummary)

def constructorKeys (s : GeneralNominalState.State) : List Nat :=
  (List.ofFn fun slot => (s.nominals slot).map GeneralNominalState.Descriptor.constructor).filterMap id

def signature (c : Constructors) (key : Nat) :=
  (c key).map (fun d => (d.parameters,d.name))

def agreement (keys : List Nat) (first last : Constructors) : Bool :=
  keys.all (fun key => decide (signature first key = signature last key))

theorem signature_injective (first last : Constructors) (key : Nat)
    (eq : signature first key = signature last key) : first key = last key := by
  unfold signature at eq
  cases one : first key with
  | none =>
    cases two : last key with
    | none => rfl
    | some d =>
      rw [one,two] at eq
      cases eq
  | some a =>
    cases two : last key with
    | none =>
      rw [one,two] at eq
      cases eq
    | some b =>
      rw [one,two] at eq
      have shape := Option.some.inj eq
      rcases a with ⟨left,keyA⟩
      rcases b with ⟨right,keyB⟩
      cases shape
      rfl

theorem agreement_exact (keys : List Nat) (first last : Constructors) :
    agreement keys first last = true ↔ ∀ key ∈ keys, first key = last key := by
  unfold agreement
  constructor
  · intro h key member
    exact signature_injective _ _ _ (of_decide_eq_true (List.all_eq_true.mp h key member))
  · intro uniform
    apply List.all_eq_true.mpr
    intro key member
    apply decide_eq_true_eq.mpr
    unfold signature
    rw [uniform key member]

theorem agreement_refl (keys : List Nat) (c : Constructors) : agreement keys c c = true :=
  (agreement_exact keys c c).mpr (fun _ _ => rfl)

def boundedWire (r : Registry) (s : State roles) (focus : Occurrence roles) : Option Wire :=
  let snapshot := s.core.erased.current.context.state
  let keys := constructorKeys snapshot
  if agreement keys r.constructors snapshot.constructors then
    some { extract r s focus with
      producers := (s.effects.filter fun e : Effect roles => agreement keys r.constructors e.registry.constructors).map effectSummary }
  else none

def guarded (r : Registry) (s : State roles) (focus : Occurrence roles) (ask : Offer) : Decision :=
  match boundedWire r s focus with
  | none => .wrongWorld
  | some w => check w ask

theorem guarded_provenance {r : Registry} {s : State roles} {focus : Occurrence roles} {ask : Offer}
    (taken : guarded r s focus ask = .ready) :
    let keys := constructorKeys s.core.erased.current.context.state
    (∀ key ∈ keys, r.constructors key = s.core.erased.current.context.state.constructors key) ∧
      ∃ e : Effect roles, e ∈ s.effects ∧
        (effectSummary e).matches ask = true ∧ ∀ key ∈ keys, r.constructors key = e.registry.constructors key := by
  let keys := constructorKeys s.core.erased.current.context.state
  let filtered : Wire := { extract r s focus with
    producers := (s.effects.filter fun e : Effect roles => agreement keys r.constructors e.registry.constructors).map effectSummary }
  by_cases uniform : agreement keys r.constructors s.core.erased.current.context.state.constructors = true
  · have quote : boundedWire r s focus = some filtered := by
      unfold boundedWire
      exact ite_eq_left uniform
    unfold guarded at taken
    rw [quote] at taken
    have facts := (GeneralRebaseReceiptWire289.check_ready _ _).mp taken
    obtain ⟨p,member,matchOffer⟩ := facts.2.1
    change p ∈ (s.effects.filter fun e : Effect roles => agreement keys r.constructors e.registry.constructors).map effectSummary at member
    simp only [List.mem_map,List.mem_filter] at member
    obtain ⟨e,⟨historical,table⟩,rfl⟩ := member
    exact ⟨(agreement_exact _ _ _).mp uniform, e,historical,matchOffer,(agreement_exact _ _ _).mp table⟩
  · have quote : boundedWire r s focus = none := by
      unfold boundedWire
      exact ite_eq_right uniform
    unfold guarded at taken
    rw [quote] at taken
    cases taken

end Yulang.GeneralRebaseReceiptCatalogue289
