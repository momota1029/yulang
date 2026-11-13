import Yulang.GeneralDictionaryRequestBatchAssembly
import Yulang.GeneralDictionaryHistoricalValueRequests

/-! A current batch may mix requests observed at different actual earlier states
with variable-free requests justified by different recorded packets. The input
is syntactic/operational provenance, not all-model request validity. -/
namespace Yulang.GeneralDictionaryRequestProvenance
open GeneralNominalMaterialization GeneralNominalSaturationState
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
variable {roles : Roles.RoleDecls}

/-- Different requests may choose different earlier states and trace suffixes.
The recorded alternative does not require any carrier slot at the target. -/
def Supported (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (batch : List Request) : Prop :=
  ∀ request ∈ batch,
    (∃ before : Tracked roles,
      B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root before ∧
      B4Target.Steps (GeneralNominalValueSteps.Step registry root) before state ∧
      GeneralDictionaryObservedFiniteRequests.Observed before.current.context.state
        before.current.context.interpretation [request]) ∨
    GeneralDictionaryRecordedBatchModels.Covered state.current [request]

theorem supported_of_recorded (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (batch : List Request)
    (covered : GeneralDictionaryRecordedBatchModels.Covered state.current batch) :
    Supported registry root state batch := by
  intro request member
  exact Or.inr (by intro other present; have same := List.mem_singleton.mp present; subst other; exact covered request member)

theorem supported_of_observed (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root before)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (batch : List Request)
    (observed : GeneralDictionaryObservedFiniteRequests.Observed before.current.context.state
      before.current.context.interpretation batch) : Supported registry root after batch := by
  intro request member
  refine Or.inl ⟨before,reachable,path,?_⟩
  intro other present
  have same := List.mem_singleton.mp present
  subst other
  exact observed request member

theorem supported_append (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (first last : List Request) :
    Supported registry root state (first ++ last) ↔
      Supported registry root state first ∧ Supported registry root state last := by
  simp only [Supported,List.mem_append,or_imp,forall_and]

theorem shape (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (batch : List Request) (supported : Supported registry root state batch) :
    (generated state.current.context.state state.current.context.interpretation batch).variables = [] ∧
      (generated state.current.context.state state.current.context.interpretation batch).unknown = false := by
  apply GeneralDictionaryRequestBatchAssembly.shape_of_singletons
  intro request member
  rcases supported request member with ⟨before,_prior,path,observed⟩ | recorded
  · exact GeneralDictionaryHistoricalValueRequests.value_generated_shape registry root before state path [request] observed
  · exact GeneralDictionaryRecordedBatchModels.reachable_shape registry root state reachable [request] recorded

theorem models (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (batch : List Request) (supported : Supported registry root state batch)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state declaration capture report
      (generated state.current.context.state state.current.context.interpretation batch) model := by
  apply GeneralDictionaryRequestBatchAssembly.models_of_singletons
  intro request member
  rcases supported request member with ⟨before,_prior,path,observed⟩ | recorded
  · exact ⟨(GeneralDictionaryHistoricalValueRequests.value_generated_shape registry root before state path [request] observed).1,
      GeneralDictionaryHistoricalValueRequests.value_generated_models registry root before state path [request] observed
        declaration capture report model valid⟩
  · exact ⟨(GeneralDictionaryRecordedBatchModels.reachable_shape registry root state reachable [request] recorded).1,
      GeneralDictionaryRecordedBatchModels.reachable_models registry root state reachable [request] recorded
        declaration capture report model valid⟩
end Yulang.GeneralDictionaryRequestProvenance
