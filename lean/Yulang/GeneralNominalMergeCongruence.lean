import Yulang.GeneralNominalRepeatedMergeTransport

/-! Arbitrary finite allocation merge congruence. Binder occurrences retain
order and names; endpoint source identities may change if denotations agree. -/
namespace Yulang.GeneralNominalMergeCongruence
open GeneralNominalAllocation GeneralDeclarations CommonNominalFullCarrier
open GeneralSourceState (Interval)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalRepeatedMergeTransport

def IntervalEquivalent (model : GeneralNominalCommonBridge.Assignment) (first last : Interval) : Prop :=
  Equivalent (model first.1).1 (model last.1).1 ∧ Equivalent (model first.2).1 (model last.2).1

def BindingEquivalent (model : GeneralNominalCommonBridge.Assignment) (first last : Nat × Interval) : Prop :=
  first.1 = last.1 ∧ IntervalEquivalent model first.2 last.2

theorem occurrences_equivalent (model : GeneralNominalCommonBridge.Assignment)
    {first last : Bindings} (same : GeneralNominalDemandMerging.All₂ (BindingEquivalent model) first last) (name : Nat) :
    GeneralNominalDemandMerging.All₂ (IntervalEquivalent model) (occurrences first name) (occurrences last name) := by
  induction same with
  | nil => exact .nil
  | @cons a b as bs equal rest ih =>
    have names := equal.1
    by_cases hit : a.1 = name
    · have hit' : b.1 = name := names.symm.trans hit
      simp only [occurrences,List.filter_cons,hit,hit',beq_self_eq_true,ite_true,List.map_cons] at *
      exact .cons equal.2 ih
    · have miss : b.1 ≠ name := by simpa [← names] using hit
      simp only [occurrences,List.filter_cons,beq_iff_eq,hit,miss,ite_false] at *
      exact ih

theorem lower_equivalent (model : GeneralNominalCommonBridge.Assignment)
    {first last : List Interval} (same : GeneralNominalDemandMerging.All₂ (IntervalEquivalent model) first last) :
    Equivalent ((lower first).eval CommonNominalFullCarrier.model model)
      ((lower last).eval CommonNominalFullCarrier.model model) := by
  induction same with
  | nil => exact ⟨subtype_refl _,subtype_refl _⟩
  | @cons a b as bs equal rest ih =>
    cases rest with
    | nil => exact equal.1
    | cons equal' rest' => exact union_equivalent equal.1 ih

theorem upper_equivalent (model : GeneralNominalCommonBridge.Assignment)
    {first last : List Interval} (same : GeneralNominalDemandMerging.All₂ (IntervalEquivalent model) first last) :
    Equivalent ((upper first).eval CommonNominalFullCarrier.model model)
      ((upper last).eval CommonNominalFullCarrier.model model) := by
  induction same with
  | nil => exact ⟨subtype_refl _,subtype_refl _⟩
  | @cons a b as bs equal rest ih =>
    cases rest with
    | nil => exact equal.2
    | cons equal' rest' => exact inter_equivalent equal.2 ih

def mergeAtoms (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (name : Nat) : List (PresenceNormalForm.Atom Nat) :=
  match occurrences bindings name with
  | [_] => []
  | bounds => equations ((capture state registry invocation declaration.id bindings).inputs name).1 (lower bounds) ++
      equations ((capture state registry invocation declaration.id bindings).inputs name).2 (upper bounds)

theorem mergeAtoms_iff (before after : GeneralNominalState.State) (oldRegistry newRegistry : Registry)
    (invocation : Nat) (declaration : Declaration) (seed : before.seed = after.seed)
    (model : GeneralNominalCommonBridge.Assignment) {first last : Bindings}
    (same : GeneralNominalDemandMerging.All₂ (BindingEquivalent model) first last) (name : Nat) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (mergeAtoms before oldRegistry invocation declaration first name) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (mergeAtoms after newRegistry invocation declaration last name) := by
  have aligned := occurrences_equivalent model same name
  unfold mergeAtoms capture
  generalize old : occurrences first name = xs at aligned ⊢
  generalize new : occurrences last name = ys at aligned ⊢
  cases aligned with
  | nil => simp [source,seed,old,new]
  | @cons a b as bs equal rest =>
    cases rest with
    | nil => rfl
    | @cons c d cs ds next tail =>
      simp only [source,seed,old,new,PresenceNormalForm.all_append]
      apply and_congr
      · apply equations_congr
        exact lower_equivalent model (.cons equal (.cons next tail))
      · apply equations_congr
        exact upper_equivalent model (.cons equal (.cons next tail))

/-- No arity bound, injectivity, distinct endpoint, or occurrence-count bound.
The ordered names agree and all corresponding endpoints denote equivalent
values. Singleton occurrences generate no merge equations; absent names and
arbitrarily repeated names use the stable allocated identities. -/
theorem merges_iff (before after : GeneralNominalState.State) (oldRegistry newRegistry : Registry)
    (invocation : Nat) (declaration : Declaration) (seed : before.seed = after.seed)
    (model : GeneralNominalCommonBridge.Assignment) {first last : Bindings}
    (same : GeneralNominalDemandMerging.All₂ (BindingEquivalent model) first last) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges before oldRegistry invocation declaration first) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after newRegistry invocation declaration last) := by
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    (declaration.inputNames.flatMap (mergeAtoms before oldRegistry invocation declaration first)) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
    (declaration.inputNames.flatMap (mergeAtoms after newRegistry invocation declaration last))
  have forward (oldState newState : GeneralNominalState.State) (oldReg newReg : Registry)
      (oldBindings newBindings : Bindings)
      (each : ∀ name, PresenceNormalForm.All CommonNominalFullCarrier.model model
        (mergeAtoms oldState oldReg invocation declaration oldBindings name) ↔
        PresenceNormalForm.All CommonNominalFullCarrier.model model
        (mergeAtoms newState newReg invocation declaration newBindings name))
      (valid : PresenceNormalForm.All CommonNominalFullCarrier.model model
        (declaration.inputNames.flatMap (mergeAtoms oldState oldReg invocation declaration oldBindings))) :
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (declaration.inputNames.flatMap (mergeAtoms newState newReg invocation declaration newBindings)) := by
    intro atom member
    obtain ⟨name,declared,atomMember⟩ := List.mem_flatMap.mp member
    apply (each name).mp ?_ atom atomMember
    intro oldAtom oldMember
    exact valid oldAtom (List.mem_flatMap.mpr ⟨name,declared,oldMember⟩)
  have each := mergeAtoms_iff before after oldRegistry newRegistry invocation declaration seed model same
  exact ⟨forward before after oldRegistry newRegistry first last each,
    forward after before newRegistry oldRegistry last first (fun name => (each name).symm)⟩

theorem ofFn_aligned {n : Nat} (model : GeneralNominalCommonBridge.Assignment)
    (names : Fin n → Nat) (first last : Fin n → Interval)
    (same : ∀ i, IntervalEquivalent model (first i) (last i)) :
    GeneralNominalDemandMerging.All₂ (BindingEquivalent model)
      (List.ofFn fun i => (names i,first i)) (List.ofFn fun i => (names i,last i)) := by
  induction n with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact .cons ⟨rfl,same 0⟩ (ih (fun i => names i.succ) (fun i => first i.succ) (fun i => last i.succ)
      (fun i => same i.succ))

/-- Convenient finite-index interface for arbitrary repeated name maps. -/
theorem ofFn_merges_iff (before after : GeneralNominalState.State) (oldRegistry newRegistry : Registry)
    (invocation : Nat) (declaration : Declaration) (seed : before.seed = after.seed)
    (model : GeneralNominalCommonBridge.Assignment) {n : Nat}
    (names : Fin n → Nat) (first last : Fin n → Interval)
    (same : ∀ i, IntervalEquivalent model (first i) (last i)) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges before oldRegistry invocation declaration (List.ofFn fun i => (names i,first i))) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges after newRegistry invocation declaration (List.ofFn fun i => (names i,last i))) :=
  merges_iff before after oldRegistry newRegistry invocation declaration seed model
    (ofFn_aligned model names first last same)

end Yulang.GeneralNominalMergeCongruence
