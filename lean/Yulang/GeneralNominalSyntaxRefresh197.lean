import Yulang.GeneralNominalFinishedObservation197

set_option backward.isDefEq.respectTransparency false
/-! Same-slot nominal-only evidence transport. Completion is recovered from the
actual source Instance; callers provide no descriptor trace/report agreement. -/
namespace Yulang.GeneralNominalSyntaxRefresh197
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalViewTransport196
open GeneralNominalFinishedObservation197

variable {roles : Roles.RoleDecls} {registry : Registry}
variable {old : GeneralNominalCandidates.Context} {next : View old.state}

def RegistrySyntax (registry : Registry) (old : GeneralNominalCandidates.Context) : Prop :=
  ∀ declaration ∈ registry.declarations, ∀ query ∈
    GeneralNominalInspection.queries old.state old.interpretation declaration, Syntax query

theorem node_transport (shape : RegistrySyntax registry old)
    (refinement : GeneralNominalRefinements.Refines old.state (replace old.state next))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralDictionaryRecursiveEvidence.Instance registry old model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (context old next) model root key children := by
  obtain ⟨decl,visible,checked,identity,role,bs,located,finished,ready,kids,metadata,branch⟩ := source
  have observed := many_observed_of_finished (shape decl visible) finished
  have same := GeneralNominalRefinementTrace197.rechecked old next decl bs refinement observed
  refine ⟨decl,visible,checked,identity,role,bs,located,?_,?_,?_,metadata,?_⟩
  · rw [same]; exact finished
  · unfold GeneralNominalRecursiveCandidates.RequestReady at ready ⊢
    rw [generated_eq same]; exact ready
  · rw [same]
    simp only [context,bindings_report]
    exact kids
  · exact branch_transport same registry root checked model valid branch

theorem tree_transport (shape : RegistrySyntax registry old)
    (refinement : GeneralNominalRefinements.Refines old.state (replace old.state next))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry old model) tree) :
    GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry (context old next) model) tree := by
  induction source with
  | node localRule _ ih => exact .node (node_transport shape refinement model valid localRule) ih

theorem evidence_transport (shape : RegistrySyntax registry old)
    (refinement : GeneralNominalRefinements.Refines old.state (replace old.state next))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralDictionaryRecursiveEvidence.Evidence registry old model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (context old next) model root payload := by
  obtain ⟨tree,readback,evidence⟩ := source
  exact ⟨tree,readback,tree_transport shape refinement model valid evidence⟩

/-- Source witnesses may depend on the model. There is no uniform-witness,
TreeObserved, report-equality or final-evidence premise. -/
theorem universal_refresh {state : GeneralNominalCenteredHeadStepEffects.State roles}
    {next : View state.core.erased.current.context.state}
    (certificate : GeneralNominalCenteredSteps.Refresh state.core
      (context state.core.erased.current.context next))
    (shape : RegistrySyntax registry state.core.erased.current.context)
    (source : ∀ model, GeneralNominalCenteredHeadStepEffects.Models state model →
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry state model root payload) :
    ∀ model, GeneralNominalCenteredHeadStepEffects.Models
      (GeneralNominalCenteredHeadStepKernel.refresh state (context state.core.erased.current.context next)) model →
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry
        (GeneralNominalCenteredHeadStepKernel.refresh state (context state.core.erased.current.context next))
        model root payload := by
  intro model valid
  apply evidence_transport shape certificate.refines model valid.1.1.1
  exact source model ((GeneralNominalCenteredHeadStepKernel.refresh_models certificate model).mp valid)
end Yulang.GeneralNominalSyntaxRefresh197
