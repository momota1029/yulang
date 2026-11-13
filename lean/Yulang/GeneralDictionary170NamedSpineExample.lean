import Yulang.GeneralDictionary170NamedSpine
import Yulang.GeneralDictionary170NamedCoverage
import Yulang.GeneralDictionaryFiniteObservedExample

/-! An actual ternary nominal input and nonempty named nominal output, justified
by source observations. No scalar-input leaf is used. -/
namespace Yulang.GeneralDictionary170NamedSpineExample
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionary170NamedSpine
abbrev source := GeneralDictionaryFiniteObservedExample.state
abbrev context := GeneralDictionaryFiniteObservedExample.context
abbrev constructors := GeneralDictionaryFiniteObservedExample.constructors
abbrev equation := GeneralDictionaryFiniteObservedExample.equation
abbrev declaration : Declaration := ⟨170,1,[.app 0 [.var 1,.var 2,.var 3]],[],[equation],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev demand : GeneralSourceState.Demand roles := ⟨1,fun _ => (0,0),[⟨0,0⟩],by
  intro o member
  have same := List.mem_singleton.mp member
  subst o
  exact ⟨none,rfl⟩⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨170,demand⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro e member
      have same := List.mem_singleton.mp member; subst e
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨equation,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro c member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors,
      GeneralDictionaryFiniteObservedExample.constructors]
  · intro c member; cases member
  · intro c member; cases member
  · intro c member; cases member
  · intro c member; cases member

def shape : Shape registry context root declaration checked where
  terminal := rfl
  role := rfl
  slot := ⟨0,by decide⟩
  arity := 3
  names := fun i => i.val + 1
  distinct := by intro a b equal; apply Fin.ext; dsimp at equal; omega
  inputs := rfl
  bounds := fun _ => (⟨1,by decide⟩,⟨1,by decide⟩)
  spine := .leaf ⟨0,by decide⟩ GeneralDictionaryFiniteObservedExample.descriptor rfl rfl
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,GeneralNominalSpineFacts.Spine.query,
      GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
      GeneralDictionaryFiniteObservedExample.constructors,List.ofFn_succ]
  located := by decide +kernel
  defined := by
    intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨equation,List.mem_singleton_self _,rfl⟩
  observed := by
    rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro c h; cases h)]
    exact GeneralDictionaryFiniteObservedExample.observed

theorem metadata : Metadata registry context := GeneralDictionaryFiniteObservedExample.metadata

theorem actual_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id []) :=
  evidence_of_shape context registry root declaration (by simp) checked shape metadata assignment valid

theorem nonvacuous : root.demand.outputs ≠ [] ∧
    GeneralNominalState.Models source GeneralDictionaryFiniteObservedExample.model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry context GeneralDictionaryFiniteObservedExample.model
      root (.node declaration.id []) :=
  ⟨(by intro h; cases h),GeneralDictionaryFiniteObservedExample.state_models,
    actual_evidence _ GeneralDictionaryFiniteObservedExample.state_models⟩

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro d member
  have same := List.mem_singleton.mp member
  subst d
  exact checked

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      simp [GeneralNominalState.sources,List.ofFn_succ]
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro id member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> subst id <;> decide +kernel
  unallocated := rfl

abbrev start := GeneralNominalSupport.initial context root

theorem no_current_local_node : ¬ Nonempty (GeneralDictionary170NamedCoverage.Node registry start root) := by
  have absent : ∀ occurrence, GeneralDictionary170NamedCoverage.Node registry start occurrence → occurrence ≠ root := by
    intro occurrence node
    cases node with
    | recorded packet member relocation => cases member
    | scalar occurrence d visible checked shape =>
      intro equal
      subst occurrence
      cases shape.outputs
    | spine occurrence d visible checked shape =>
      intro equal
      subst occurrence
      cases shape.outputs
    | named occurrence d visible checked shape =>
      have same := List.mem_singleton.mp visible
      subst d
      have bad := shape.inputs
      cases bad
  intro ⟨node⟩
  exact absent root node rfl

/-- A reachable source and inhabited named-spine dictionary exist even though
this cycle's scalar-named local-node datatype still lacks a constructor for it. -/
theorem coverage_gap : GeneralNominalSourceFormation.InitialSource registry context root ∧
    (∃ assignment, GeneralNominalState.Models source assignment ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id [])) ∧
    ¬ Nonempty (GeneralDictionary170NamedCoverage.Node registry start root) :=
  ⟨initial_source,⟨_,GeneralDictionaryFiniteObservedExample.state_models,
    actual_evidence _ GeneralDictionaryFiniteObservedExample.state_models⟩,no_current_local_node⟩
end Yulang.GeneralDictionary170NamedSpineExample
