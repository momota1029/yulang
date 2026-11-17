import Yulang.GeneralNominalVersionedObservations233
set_option backward.isDefEq.respectTransparency false
/-! Exact full-journal model transport for the new trusted-slice observation
certificates. No operational rule is replaced here; only the existing concrete
refresh/reobserve state transformers are interpreted under the new certificate. -/
namespace Yulang.GeneralNominalVersionedObservationTransport233
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedRefresh232
open GeneralNominalVersionedObservations233
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

theorem refresh_forward_raw
    (valid : Models state model) (raw : GeneralNominalState.Models context.state model) :
    Models (refresh state context) model := by
  refine ⟨⟨raw,valid.1.2.1,valid.1.2.2.1,valid.1.2.2.2.1,valid.1.2.2.2.2.1,?_⟩,valid.2.1,?_⟩
  · intro effect member
    have held := valid.1.2.2.2.2.2 effect member
    exact ⟨held.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := (refresh state context).core) (after := state.core)
        (fun _ h => h) (fun _ h => h)) held.2⟩
  · intro effect member
    have held := valid.2.2 effect member
    exact ⟨held.1,(refresh_live_iff state context effect model).mpr held.2⟩

theorem refresh_backward_raw
    (valid : Models (refresh state context) model)
    (raw : GeneralNominalState.Models state.core.erased.current.context.state model) : Models state model := by
  refine ⟨⟨raw,valid.1.2.1,valid.1.2.2.1,valid.1.2.2.2.1,valid.1.2.2.2.2.1,?_⟩,valid.2.1,?_⟩
  · intro effect member
    have held := valid.1.2.2.2.2.2 effect member
    exact ⟨held.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (refresh state context).core)
        (fun _ h => h) (fun _ h => h)) held.2⟩
  · intro effect member
    have held := valid.2.2 effect member
    exact ⟨held.1,(refresh_live_iff state context effect model).mp held.2⟩

theorem refresh_models (certificate : GeneralNominalVersionedObservations233.Refresh state context) :
    Models (refresh state context) model ↔ Models state model := by
  constructor
  · intro valid
    exact refresh_backward_raw valid (GeneralNominalRefinements.models certificate.refines model valid.1.1)
  · intro valid
    exact refresh_forward_raw valid (raw_models (certificate.constraints model valid) certificate.cache valid)

theorem reobserve_forward_raw
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (valid : Models state model) (raw : GeneralNominalState.Models revision.snapshot model) :
    Models (reobserve state revision) model := by
  refine ⟨⟨raw,valid.1.2.1,valid.1.2.2.1,valid.1.2.2.2.1,valid.1.2.2.2.2.1,?_⟩,valid.2.1,?_⟩
  · intro effect member
    have held := valid.1.2.2.2.2.2 effect member
    exact ⟨held.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := (reobserve state revision).core) (after := state.core)
        (fun _ h => h) (fun _ h => h)) held.2⟩
  · intro effect member
    have held := valid.2.2 effect member
    exact ⟨held.1,(reobserve_live_iff state revision effect model).mpr held.2⟩

theorem reobserve_backward_raw
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current)
    (valid : Models (reobserve state revision) model)
    (raw : GeneralNominalState.Models state.core.erased.current.context.state model) : Models state model := by
  refine ⟨⟨raw,valid.1.2.1,valid.1.2.2.1,valid.1.2.2.2.1,valid.1.2.2.2.2.1,?_⟩,valid.2.1,?_⟩
  · intro effect member
    have held := valid.1.2.2.2.2.2 effect member
    exact ⟨held.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (reobserve state revision).core)
        (fun _ h => h) (fun _ h => h)) held.2⟩
  · intro effect member
    have held := valid.2.2 effect member
    exact ⟨held.1,(reobserve_live_iff state revision effect model).mp held.2⟩

theorem reobserve_models {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}
    (certificate : GeneralNominalVersionedObservations233.Reobserve state revision) :
    Models (reobserve state revision) model ↔ Models state model := by
  constructor
  · intro valid
    exact reobserve_backward_raw revision valid (certificate.raw model valid.1.1)
  · intro valid
    exact reobserve_forward_raw revision valid
      (raw_models ⟨valid.1.1.1,valid.1.1.2.2⟩ certificate.cache valid)

end Yulang.GeneralNominalVersionedObservationTransport233
