import Yulang.GeneralNominalFeedbackObstruction

/-! An accepted recursive declaration whose associated output can expose a
new input constructor at the next invocation. The output binder remains absent
from every unnamed child argument. This is the same general declaration check
and child emitter as the concrete feedback boundary. -/
namespace Yulang.GeneralNominalOutputGrowth

open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples (roles constructors)
open GeneralSourceDictionaries CommonNominalFullCarrier

abbrev clause : Clause := ⟨20,1,[.var 0],[⟨21,0,.var 1⟩]⟩
abbrev declaration : Declaration :=
  ⟨2,1,[.app 0 [.var 0]],[clause],[⟨22,0,.app 0 [.var 1]⟩],[⟨1,20,21⟩]⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name
        exact Or.inl ⟨⟨22,0,.app 0 [.var 1]⟩,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro c member
      have same := List.mem_singleton.mp member; subst c
      refine ⟨rfl,?_⟩
      intro equation member
      have same := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,variablesArgs,Pattern.variables]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro c member
    have same := List.mem_singleton.mp member; subst c; exact ⟨rfl,rfl⟩
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    unfold ConservativeSmaller
    decide +kernel
  · intro c member
    have same := List.mem_singleton.mp member; subst c
    exact unary_descent 0 0

abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩

theorem checked : Checked registry :=
  ⟨by decide +kernel,by intro d member; have same := List.mem_singleton.mp member; subst d; exact declaration_checked⟩

theorem output_only : declaration.outputNames = [1] ∧
    declaration.inputNames = [0] ∧ clause.arguments = [.var 0] := ⟨rfl,rfl,rfl⟩

abbrev clauseChecked : clause.Signature roles :=
  declaration_checked.signature.2.2.2 clause (by simp)

def capture (input output : Nat) : Capture := ⟨fun _ => (input,input),fun _ => output⟩

theorem child_equations (input output : Nat) (allocation : Allocation roles clause) :
    (childDemand declaration clause clauseChecked (capture input output) allocation).arguments =
      (fun _ => (input,input)) ∧
    (childDemand declaration clause clauseChecked (capture input output) allocation).outputs = [⟨0,output⟩] := by
  constructor
  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simp [childDemand,zero,inputInterval,normalize,capture]
  · rfl

/-- Finite nominal types used as separating models at every finite prefix. -/
def tower : Nat → Ty
  | 0 => .base .int
  | n+1 => nominal 0 [.inl (tower n)]

private theorem int_not_nominal (name : Nat) (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) (by
      simp only [observe_nominal]
      exact ⟨rfl,List.length_map ..⟩)

theorem tower_equivalent (first last : Nat) : Equivalent (tower first) (tower last) ↔ first = last := by
  constructor
  · induction first generalizing last with
    | zero =>
      intro equal
      cases last with
      | zero => rfl
      | succ last => exact False.elim (int_not_nominal 0 _ equal.1)
    | succ first ih =>
      intro equal
      cases last with
      | zero => exact False.elim (int_not_nominal 0 _ equal.2)
      | succ last =>
        have nested := ((nominal_regular_invariant_exact _ _ _ _).mp equal.1).2.2
          0 (.inl (tower first)) (.inl (tower last)) rfl rfl
        exact congrArg Nat.succ (ih last nested)
  · rintro rfl
    exact ⟨subtype_refl _,subtype_refl _⟩

def PrefixModels (length : Nat) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∀ index, index ≤ length → Equivalent (model index).1 (nominal 0 [.inl (model (index+1)).1])

def finiteModel (length : Nat) : GeneralNominalCommonBridge.Assignment :=
  fun index => (tower (length+1-index),Common.rowEmpty)

theorem finite_prefix_models (length : Nat) : PrefixModels length (finiteModel length) := by
  intro index bound
  have difference : length+1-index = (length+1-(index+1))+1 := by omega
  change Equivalent (tower (length+1-index)) (nominal 0 [.inl (tower (length+1-(index+1)))])
  rw [difference]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem prefix_consistent (length : Nat) : ∃ model, PrefixModels length model :=
  ⟨finiteModel length,finite_prefix_models length⟩

theorem prefix_refines (length : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (valid : PrefixModels (length+1) model) : PrefixModels length model :=
  fun index bound => valid index (by omega)

theorem finite_prefix_separates (length first last : Nat)
    (one : first ≤ length+1) (two : last ≤ length+1) (different : first ≠ last) :
    ¬ Equivalent (finiteModel length first).1 (finiteModel length last).1 := by
  intro same
  have equal := (tower_equivalent _ _).mp same
  omega

/-- No equality of different supported inputs is entailed by a finite prefix. -/
theorem prefix_not_equal (length first last : Nat)
    (one : first ≤ length+1) (two : last ≤ length+1) (different : first ≠ last) :
    ¬ (∀ model, PrefixModels length model → Equivalent (model first).1 (model last).1) := by
  intro all
  exact finite_prefix_separates length first last one two different
    (all (finiteModel length) (finite_prefix_models length))

/-- The preceding shortest finite model is removed by the next output equation. -/
theorem old_minimizer_removed (length : Nat) : ¬ PrefixModels (length+1) (finiteModel length) := by
  intro valid
  have impossible := valid (length+1) (Nat.le_refl _)
  have one : length+1-(length+1) = 0 := by omega
  have two : length+1-(length+1+1) = 0 := by omega
  change Equivalent (tower (length+1-(length+1))) (nominal 0 [.inl (tower (length+1-(length+1+1)))]) at impossible
  rw [one,two] at impossible
  exact int_not_nominal 0 [.inl (tower 0)] impossible.1

/-- A regular infinite nominal value is also a model of every finite prefix. -/
theorem regular_prefix_models (length : Nat) :
    PrefixModels length GeneralNominalProgressObstruction.model :=
  fun _ _ => GeneralNominalProgressObstruction.equation

/-- Thus denotation alone, in every journal model, cannot strictly rank the
parent above its emitted child in any well-founded order. -/
theorem no_universal_denotation_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : Ty → Measure) (length : Nat) :
    ¬ (∀ model, PrefixModels length model →
      less (rank (model (length+1)).1) (rank (model length).1)) := by
  intro descends
  have self := descends GeneralNominalProgressObstruction.model (regular_prefix_models length)
  have irreflexive : ∀ value, ¬ less value value := by
    intro value
    induction wellFounded.apply value with
    | intro value below ih =>
      intro loop
      exact ih value loop loop
  exact irreflexive _ self

end Yulang.GeneralNominalOutputGrowth
