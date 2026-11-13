import Yulang.GeneralDictionaryVariableClauseCatalog
import Yulang.GeneralDictionaryReservedCatalogEvidence
import Yulang.GeneralDictionaryReservedRefreshedClassification

/-! The generic variable-clause catalog bridge applies across an actual
2-slot to 3-slot nominal refresh, including an initially unobserved named output.
No example-specific request equality is supplied to the generic bridge. -/
namespace Yulang.GeneralDictionaryVariableClauseCatalogExample
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration checked)
open GeneralDictionaryReservedNominalRefresh (refreshed refreshed_reachable refreshed_inhabited)
open GeneralDictionaryReservedRefreshedEvidence (current)
open GeneralDictionaryReservedCollectedHistory (installed_closed)
open GeneralDictionaryRecursiveEvidence

noncomputable def scalarShape : GeneralDictionaryMultiScalarInspection.Shape current root declaration where
  role := rfl
  entries := [((1 : Fin 3),.int)]
  observed := by intro entry member; have equal := List.mem_singleton.mp member; subst entry; exact ⟨rfl,rfl⟩
  inputs := rfl
  query := GeneralDictionaryReservedRefreshedEvidence.shape.query
  located := GeneralDictionaryReservedRefreshedEvidence.shape.located
  defined := GeneralDictionaryReservedRefreshedEvidence.shape.defined

theorem changed_context : packet.context ≠ current := by
  intro equal
  have slots := congrArg (fun context : GeneralNominalCandidates.Context => context.state.base.slots) equal
  change 2 = 3 at slots
  contradiction

theorem coverage (captures : GeneralNominalAllocation.Bindings) :
    ∀ request ∈ GeneralNominalMaterialization.requests current.state registry root declaration checked captures,
      request ∈ GeneralDictionaryReachableRequestHistory.safeCatalog refreshed :=
  GeneralDictionaryVariableClauseCatalog.current_covered refreshed packet
    GeneralDictionaryReservedRefreshedEvidence.recorded (by intro clause member; cases member) installed_closed captures

theorem instance_after_refresh (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models refreshed.current model) :
    Instance registry current model root declaration.id [] := by
  have result := GeneralDictionaryVariableClauseCatalog.scalar_instance packet root refreshed
    refreshed_reachable GeneralDictionaryReservedRefreshedEvidence.recorded
    (by intro clause member; cases member) installed_closed (by simp) scalarShape
    GeneralDictionaryReservedRefreshedEvidence.metadata model valid
  have empty := GeneralDictionaryLinearLeaf.children_empty current registry root declaration checked rfl
    (GeneralNominalRecursiveInspection.bindings current.state
      (GeneralNominalRecursiveCandidates.report current declaration
        (GeneralDictionaryMultiScalarInspection.points scalarShape.entries)))
  change Instance registry current model root declaration.id
    (GeneralNominalAllocation.children current.state registry root declaration checked
      (GeneralNominalRecursiveInspection.bindings current.state
        (GeneralNominalRecursiveCandidates.report current declaration
          (GeneralDictionaryMultiScalarInspection.points scalarShape.entries)))) at result
  rw [empty] at result
  exact result

theorem evidence_after_refresh (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models refreshed.current model) :
    Evidence registry current model root (.node declaration.id []) :=
  evidence_node registry current model root declaration.id [] [] (instance_after_refresh model valid) .nil

theorem inhabited_changed_context :
    packet.context ≠ current ∧
    (¬ GeneralDictionaryObservedFiniteRequests.Observed state
      GeneralDictionaryFiniteObservedExample.interpretation [request]) ∧
    GeneralNominalSaturationState.Models refreshed.current positive ∧
    Evidence registry current positive root (.node declaration.id []) :=
  ⟨changed_context,not_observed,refreshed_inhabited,evidence_after_refresh positive refreshed_inhabited⟩
end Yulang.GeneralDictionaryVariableClauseCatalogExample
