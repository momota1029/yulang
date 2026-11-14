import Yulang.GeneralNominalCenteredHeadMatStepCoverage

set_option backward.isDefEq.respectTransparency false

/-! Journal restriction for the corrected models. The frozen refresh update
and certificate remain intact. Its forward-model premise is exposed separately
because the certificate is phrased using the legacy packet interpretation. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepPreservation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles} {model : Assignment}

theorem install_restrict (snapshot : effect.snapshot = state.core)
    (valid : Models (install state effect) model) : Models state model :=
  ((install_models snapshot).mp valid).1

theorem merge_restrict (valid : Models (merge state first last) model) : Models state model :=
  (merge_models.mp valid).1

theorem refresh_restrict
    (certificate : GeneralNominalCenteredSteps.Refresh state.core context)
    (valid : Models (refresh state context) model) : Models state model := by
  refine ⟨GeneralNominalRefinements.models certificate.refines model valid.1,
    valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
  intro effect member
  have pair := valid.2.2.2.2.2 effect member
  exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
    (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
      (before := state.core) (after := (refresh state context).core)
      (fun _ h => h) (fun _ h => h)) pair.2⟩

def RefreshExactTransport (state : State roles) (context : GeneralNominalCandidates.Context) : Prop :=
  ∀ model, Models state model → GeneralNominalState.Models context.state model

theorem refresh_forward (exact : RefreshExactTransport state context)
    (valid : Models state model) : Models (refresh state context) model := by
  refine ⟨exact model valid,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
  intro effect member
  have pair := valid.2.2.2.2.2 effect member
  exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
    (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
      (before := (refresh state context).core) (after := state.core)
      (fun _ h => h) (fun _ h => h)) pair.2⟩

theorem refresh_models_iff
    (certificate : GeneralNominalCenteredSteps.Refresh state.core context)
    (exact : RefreshExactTransport state context) :
    Models (refresh state context) model ↔ Models state model :=
  ⟨refresh_restrict certificate,refresh_forward exact⟩

theorem refresh_exact_iff : RefreshExactTransport state context ↔
    ∀ model, Models state model → Models (refresh state context) model :=
  ⟨fun exact _ valid => refresh_forward exact valid,fun forward model valid => (forward model valid).1⟩

theorem source_refresh_exact
    (certificate : GeneralNominalCenteredSteps.Refresh (initial context root).core after) :
    RefreshExactTransport (initial context root) after := by
  intro model valid
  apply certificate.exact
  exact (GeneralNominalCenteredSteps.initial_models _ _ _).mpr ((initial_models ..).mp valid)

theorem merged_output_effect (valid : Models (merge state first last) model)
    (recorded : effect ∈ state.effects)
    (requested : output ∈ GeneralNominalCenteredHeadOutputs.requests (merge state first last).core
      effect.plan.packet.site.occurrence)
    (found : GeneralDictionaryAssociatedProvenance.lookup roles effect.plan.packet.declaration output.name = some body) :
    GeneralNominalCenteredHeadMatEffects.BodyHolds effect.plan output.target model body :=
  (valid.2.2.2.2.2 effect recorded).2.1 output requested body found

theorem merge_retains_effect (valid : Models (merge state first last) model)
    (recorded : effect ∈ state.effects) : effect.Holds model ∧ effect.Live state.core model :=
  (merge_restrict valid).2.2.2.2.2 effect recorded

theorem install_retains_effect (snapshot : effect.snapshot = state.core)
    (valid : Models (install state effect) model) (recorded : prior ∈ state.effects) :
    prior.Holds model ∧ prior.Live state.core model :=
  (install_restrict snapshot valid).2.2.2.2.2 prior recorded

end Yulang.GeneralNominalCenteredHeadMatStepPreservation
