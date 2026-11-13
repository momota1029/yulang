import Yulang.GeneralDictionaryProvenanceMultiScalarBranch
import Yulang.GeneralDictionaryFiniteObservedExample

/-! Two actual unnamed scalar arguments sharing their source identity. This is
an inhabited initial-source semantic dictionary, not an assumed successful run. -/
namespace Yulang.GeneralDictionaryMultiScalarExample
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles)
open GeneralDictionaryFiniteObservedExample (state context interpretation constructors model state_models)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralDictionaryMultiScalarInspection

abbrev declaration : Declaration := ⟨156,4,[.app 2 [],.app 2 []],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev demand : GeneralSourceState.Demand roles := ⟨4,fun _ => (1,1),[],by simp⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨156,demand⟩
abbrev start := GeneralNominalSupport.initial context root

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.binaryRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals intro c member; cases member

theorem metadata : Metadata registry context := GeneralDictionaryFiniteObservedExample.metadata

abbrev shape : Shape context root declaration where
  role := rfl
  entries := [(1,.int),(1,.int)]
  observed := by
    intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst entry
    exact ⟨rfl,rfl⟩
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,interpretation,GeneralNominalExamples.interpretation,
      queries]
  located := by decide +kernel
  defined := by intro output member; cases member

theorem requests_empty (captures : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests state registry root declaration checked captures = [] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by intro c member; cases member)]
  rfl

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := GeneralDictionaryFiniteObservedExample.initial_source.below_seed
  unallocated := rfl

theorem reachable :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩

theorem actual_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models start.current assignment) :
    Instance registry context assignment root declaration.id [] := by
  have supported : GeneralDictionaryRequestProvenance.Supported registry root start
      (GeneralNominalMaterialization.requests state registry root declaration checked
        (bindings state (report context declaration (points shape.entries)))) := by
    rw [requests_empty]
    intro request member
    cases member
  have rule := GeneralDictionaryProvenanceMultiScalarBranch.instance_of_shape registry root root start
    reachable declaration (by simp) checked shape supported metadata assignment valid
  change Instance registry context assignment root declaration.id
    (GeneralNominalAllocation.children state registry root declaration checked
      (bindings state (report context declaration (points shape.entries)))) at rule
  rw [GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked rfl] at rule
  exact rule

theorem inhabited_dictionary :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry context model root (.node declaration.id []) ∧
    (roles root.demand.role).arity = 2 := by
  have valid : GeneralNominalSaturationState.Models start.current model :=
    (GeneralNominalSaturationState.initial_models context root model).mpr state_models
  exact ⟨reachable,valid,evidence_node registry context model root declaration.id [] []
    (actual_instance model valid) .nil,rfl⟩
end Yulang.GeneralDictionaryMultiScalarExample
