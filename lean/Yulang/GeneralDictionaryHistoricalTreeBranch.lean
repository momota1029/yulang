import Yulang.GeneralDictionaryHistoricalValueRequests
import Yulang.GeneralDictionaryFiniteTreeBranch
import Yulang.GeneralNominalStructuralSelectedGraph

/-! Historical finite request observations justify current selected branches.
Only the materialization observation is historical: current head inspection,
input edges and locations remain explicit. The trace may change observations. -/
namespace Yulang.GeneralDictionaryHistoricalTreeBranch
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralDictionaryRecursiveEvidence

structure Shape (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration) where
  role : declaration.role = root.demand.role
  slot : Fin context.state.base.slots
  arity : Nat
  names : Fin arity → Nat
  distinct : Function.Injective names
  inputs : declaration.inputNames = List.ofFn names
  bounds : Fin arity → GeneralNominalInspection.Bounds context.state
  tree : GeneralNominalTreeFacts.Tree context.state names bounds slot
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [tree.query]
  located : arguments context root = some [(slot,slot)]
  defined : GeneralNominalMaterialization.RootDefined declaration root

/-- All-model branch validity from current head structure and historical finite
request trees. No current output-observation certificate is required. -/
theorem branch_models (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    BranchModels registry after.context root declaration checked [(shape.slot,shape.slot)] model := by
  have privateValid := GeneralNominalTreeFacts.private_models after.context registry root declaration
    shape.names shape.distinct shape.inputs shape.bounds shape.tree shape.query model valid.1
  exact ⟨privateValid.1,privateValid.2,
    GeneralDictionaryHistoricalValueRequests.generated_models_after_trace registry saturationRoot before after
      path _ observed declaration _ _ model valid⟩

theorem ready (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)])))) :
    RequestReady registry after.context root declaration checked [(shape.slot,shape.slot)] :=
  ⟨shape.defined,(GeneralDictionaryHistoricalValueRequests.generated_shape_after_trace
    registry saturationRoot before after path _ observed).2⟩

theorem instance_of_shape (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (metadata : Metadata registry after.context)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    Instance registry after.context model root declaration.id
      (GeneralNominalAllocation.children after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))) := by
  refine ⟨declaration,visible,checked,rfl,shape.role,[(shape.slot,shape.slot)],shape.located,?_,
    ready registry saturationRoot root before after path declaration checked shape observed,rfl,metadata,
    branch_models registry saturationRoot root before after path declaration checked shape observed model valid⟩
  rw [GeneralNominalTreeFacts.report_exact after.context declaration shape.tree shape.query]
  exact GeneralNominalTreeFacts.tree_finished after.context.state shape.tree none

/-- Selected key and child identities come from the actual current judgment;
output materialization is supplied by earlier structural observations. -/
theorem selected_instance (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    declaration.id = key ∧ Instance registry after.context model root key children := by
  have metadata : Metadata registry after.context := by
    cases selected with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have rule := instance_of_shape registry saturationRoot root before after path declaration visible checked
    shape observed metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry after root model declaration.id key
    _ children rule selected
  exact ⟨same.1,by simpa only [same.1,same.2] using rule⟩

/-- The same final model satisfies the actual branch used by alias Joint.
Current output syntax is not an extra assumption. -/
theorem selected_branch (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSaturationState.State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.context.state before.context.interpretation
      (GeneralNominalMaterialization.requests after.context.state registry root declaration checked
        (bindings after.context.state (report after.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after model) :
    declaration.id = key ∧ GeneralNominalJointCandidates.BranchAt registry after root declaration.id model := by
  have rule := selected_instance registry saturationRoot root before after path declaration visible checked
    shape observed key children selected model valid
  have survivor : Survivor registry after.context root key children := by
    cases selected with | selected _ unique => exact unique.1
  exact ⟨rule.1,rule.1.symm ▸ GeneralNominalStructuralSelectedGraph.branchAt_of_instance
    registry after root key children survivor model rule.2⟩


/-- The actual value trace carries named-output semantic materialization to
its final current head. Joint and old-boundary stability are not premises. -/
theorem value_selected_branch (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.current.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed
      before.current.context.state before.current.context.interpretation
      (GeneralNominalMaterialization.requests after.current.context.state registry root declaration checked
        (bindings after.current.context.state (report after.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model) :
    declaration.id = key ∧ GeneralNominalJointCandidates.BranchAt registry after.current root declaration.id model :=
  selected_branch registry saturationRoot root before.current after.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry saturationRoot before after path)
    declaration visible checked shape observed key children
    (GeneralNominalValueBoundary.selected_old selected) model valid

/-- Model-wise full recursive payload evidence from structural current heads,
historical finite materialization observations, and the actual selected node.
Child evidence uses this same final model. No Joint or Stable premise occurs;
this is still conditional on structural shape and historical observations. -/
theorem value_node_evidence (registry : Registry) (saturationRoot root : Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry saturationRoot) before after)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : Shape after.current.context registry root declaration checked)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed
      before.current.context.state before.current.context.interpretation
      (GeneralNominalMaterialization.requests after.current.context.state registry root declaration checked
        (bindings after.current.context.state (report after.current.context declaration [(shape.slot,shape.slot)]))))
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local registry after root (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models after.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (Evidence registry after.current.context model) children dictionaries) :
    Evidence registry after.current.context model root (.node key dictionaries) := by
  have rule := selected_instance registry saturationRoot root before.current after.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry saturationRoot before after path)
    declaration visible checked shape observed key children
    (GeneralNominalValueBoundary.selected_old selected) model valid
  exact evidence_node registry after.current.context model root key children dictionaries rule.2 given

end Yulang.GeneralDictionaryHistoricalTreeBranch
