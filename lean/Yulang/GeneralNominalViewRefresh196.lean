import Yulang.GeneralNominalViewTransport196
import Yulang.GeneralNominalOrdinaryEvidence191
import Yulang.GeneralNominalReuseCatalogue195

set_option backward.isDefEq.respectTransparency false
/-! Connect structural reinspection to the actual WF refresh function, retaining
the same model and payload. This does not derive reinspection from stability. -/
namespace Yulang.GeneralNominalViewRefresh196
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalViewTransport196
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadStepKernel (refresh refresh_models)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {next : View state.core.erased.current.context.state}

theorem evidence_refresh
    (rechecked : Rechecks registry state.core.erased.current.context next)
    (model : Assignment)
    (valid : Models (refresh state (context state.core.erased.current.context next)) model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (source : (boundary roles).Evidence registry state model root payload) :
    (boundary roles).Evidence registry (refresh state (context state.core.erased.current.context next))
      model root payload :=
  evidence_transport registry rechecked model valid.1.1.1 root payload source

/-- The real certificate restricts the final model to the original state;
no substitute or existential model is introduced. -/
theorem universal_refresh
    (certificate : GeneralNominalCenteredSteps.Refresh state.core
      (context state.core.erased.current.context next))
    (rechecked : Rechecks registry state.core.erased.current.context next)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (source : ∀ model, Models state model → (boundary roles).Evidence registry state model root payload) :
    ∀ model, Models (refresh state (context state.core.erased.current.context next)) model →
      (boundary roles).Evidence registry (refresh state (context state.core.erased.current.context next)) model root payload := by
  intro model valid
  exact evidence_refresh rechecked model valid root payload (source model ((refresh_models certificate model).mp valid))

/-- A current plan's semantic instance survives the reinspection without
claiming that its historical Frame becomes a current Frame. -/
theorem reusable_instance_refresh
    (certificate : GeneralNominalCenteredSteps.Refresh state.core
      (context state.core.erased.current.context next))
    (rechecked : Rechecks registry state.core.erased.current.context next)
    {plan : GeneralNominalCenters.Plan roles}
    (reuse : GeneralNominalReuseCatalogue195.Reusable registry state plan)
    (model : Assignment)
    (valid : Models (refresh state (context state.core.erased.current.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry
      (context state.core.erased.current.context next) model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children :=
  instance_transport registry rechecked model valid.1.1.1 _ _ _
    (GeneralNominalReuseCatalogue195.reusable_instance reuse model ((refresh_models certificate model).mp valid))
end Yulang.GeneralNominalViewRefresh196
