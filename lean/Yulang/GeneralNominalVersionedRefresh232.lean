import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalVersionedFrameTransport232
import Yulang.GeneralNominalCenteredHeadMatStepRefresh
set_option backward.isDefEq.respectTransparency false

/-! Sufficient inherited-certificate observation fragment for mixed journals.
Refresh/Reobserve use the existing structural/trusted-cache certificates over
the legacy journal, not a postulated equivalence of new full Models. They may
be stronger than certificates eventually available to a complete successor.
Stored new plans retain their original snapshots and interpretations. -/
namespace Yulang.GeneralNominalVersionedRefresh232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)

variable {roles : Roles.RoleDecls}

def refresh (state : State roles) (context : GeneralNominalCandidates.Context) : State roles :=
  ⟨GeneralNominalCenteredHeadMatStepJournal.refresh state.legacy context,state.plans,state.effects⟩

def reobserve (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) : State roles :=
  ⟨GeneralNominalCenteredHeadMatStepJournal.change state.legacy revision.result,state.plans,state.effects⟩

theorem requests_iff_of_same_lists {before after : GeneralNominalCenteredSteps.State roles}
    (sites : before.erased.current.sites = after.erased.current.sites)
    (aliases : before.erased.current.aliases = after.erased.current.aliases) :
    output ∈ requests before root ↔ output ∈ requests after root :=
  ⟨fun h => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
    (before := before) (after := after) (fun _ h => sites ▸ h) (fun _ h => aliases ▸ h) h,
   fun h => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
    (before := after) (after := before) (fun _ h => sites.symm ▸ h) (fun _ h => aliases.symm ▸ h) h⟩

theorem refresh_requests (state : State roles) (context : GeneralNominalCandidates.Context) :
    output ∈ requests (refresh state context).core root ↔ output ∈ requests state.core root :=
  requests_iff_of_same_lists rfl rfl

theorem reobserve_requests (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    output ∈ requests (reobserve state revision).core root ↔ output ∈ requests state.core root :=
  requests_iff_of_same_lists rfl rfl

theorem refresh_live_iff (state : State roles) (context : GeneralNominalCandidates.Context)
    (effect : Effect roles) (model : Assignment) :
    effect.Live (refresh state context).core model ↔ effect.Live state.core model :=
  GeneralNominalVersionedFrameTransport232.class_effects_iff (fun _ => refresh_requests state context)

theorem reobserve_live_iff (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (effect : Effect roles) (model : Assignment) :
    effect.Live (reobserve state revision).core model ↔ effect.Live state.core model :=
  GeneralNominalVersionedFrameTransport232.class_effects_iff (fun _ => reobserve_requests state revision)

theorem refresh_models (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh state.legacy context)
    (model : Assignment) : Models (refresh state context) model ↔ Models state model := by
  unfold Models
  change (Legacy.Models (GeneralNominalCenteredHeadMatStepJournal.refresh state.legacy context) model ∧
    (∀ plan ∈ state.plans, GeneralNominalVersionedPlans231.Holds plan model) ∧
    ∀ effect ∈ state.effects, effect.Holds model ∧ effect.Live (refresh state context).core model) ↔ _
  unfold Legacy.Models
  rw [GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate]
  simp only [refresh_live_iff]

theorem reobserve_models {state : State roles}
    {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve state.legacy revision)
    (model : Assignment) : Models (reobserve state revision) model ↔ Models state model := by
  unfold Models
  change (Legacy.Models (GeneralNominalCenteredHeadMatStepJournal.change state.legacy revision.result) model ∧
    (∀ plan ∈ state.plans, GeneralNominalVersionedPlans231.Holds plan model) ∧
    ∀ effect ∈ state.effects, effect.Holds model ∧ effect.Live (reobserve state revision).core model) ↔ _
  unfold Legacy.Models
  rw [GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate]
  simp only [reobserve_live_iff]

theorem refresh_plans : (refresh state context).plans = state.plans := rfl
theorem refresh_effects : (refresh state context).effects = state.effects := rfl
theorem reobserve_plans : (reobserve state revision).plans = state.plans := rfl
theorem reobserve_effects : (reobserve state revision).effects = state.effects := rfl

end Yulang.GeneralNominalVersionedRefresh232
