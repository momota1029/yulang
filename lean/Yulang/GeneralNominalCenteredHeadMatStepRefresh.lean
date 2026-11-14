import Yulang.GeneralNominalCenteredHeadMatStepObservations

set_option backward.isDefEq.respectTransparency false

/-! Observation updates retain ordinary constraints while requiring exact
cached heads to be entailed by trusted slices. No full-journal head certificate
can substitute for the trusted observation premise. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepRefresh
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepObservations
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

def Constraints (snapshot : GeneralNominalState.State) (model : Assignment) : Prop :=
  GeneralNominalCommonBridge.Models snapshot.base model ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model snapshot.ordinary

structure Refresh (state : State roles) (context : GeneralNominalCandidates.Context) where
  refines : GeneralNominalRefinements.Refines state.core.erased.current.context.state context.state
  interpretation : context.interpretation = state.core.erased.current.context.interpretation
  support : ∀ source ∈ GeneralNominalState.sources context.state,
    source ∈ GeneralNominalState.sources state.core.erased.current.context.state
  constraints : ∀ model, Models state model → Constraints context.state model
  cache : CacheSound state context.state

theorem raw_models (constraints : Constraints snapshot model) (cache : CacheSound state snapshot)
    (valid : Models state model) : GeneralNominalState.Models snapshot model :=
  ⟨constraints.1,fun slot descriptor recorded => cache_sound cache (.nominal slot descriptor recorded) valid,
    constraints.2⟩

theorem refresh_exact_transport (certificate : Refresh state context) :
    GeneralNominalCenteredHeadMatStepPreservation.RefreshExactTransport state context :=
  fun model valid => raw_models (certificate.constraints model valid) certificate.cache valid

theorem refresh_models (certificate : Refresh state context) :
    Models (refresh state context) model ↔ Models state model := by
  constructor
  · intro valid
    refine ⟨GeneralNominalRefinements.models certificate.refines model valid.1,
      valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    intro effect member
    have pair := valid.2.2.2.2.2 effect member
    exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (refresh state context).core)
        (fun _ h => h) (fun _ h => h)) pair.2⟩
  · exact GeneralNominalCenteredHeadMatStepPreservation.refresh_forward (refresh_exact_transport certificate)

structure Reobserve (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) : Prop where
  raw : ∀ model, GeneralNominalState.Models revision.snapshot model →
    GeneralNominalState.Models state.core.erased.current.context.state model
  cache : CacheSound state revision.snapshot

theorem reobserve_exact_transport (certificate : Reobserve state revision) :
    GeneralNominalCenteredHeadMatStepPreservation.RefreshExactTransport state
      ⟨revision.snapshot,state.core.erased.current.context.interpretation⟩ := by
  intro model valid
  exact raw_models ⟨valid.1.1,valid.1.2.2⟩ certificate.cache valid

theorem reobserve_models (certificate : Reobserve state revision) :
    Models (change state revision.result) model ↔ Models state model := by
  constructor
  · intro valid
    refine ⟨certificate.raw model valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    intro effect member
    have pair := valid.2.2.2.2.2 effect member
    exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (change state revision.result).core)
        (fun _ h => h) (fun _ h => h)) pair.2⟩
  · exact GeneralNominalCenteredHeadMatStepPreservation.refresh_forward (reobserve_exact_transport certificate)

theorem refresh_excluded (cut : Cut state model) (recorded : GeneralCanonicalObservations.Recorded context.state observation)
    (falseHead : ¬ observation.Holds model) : ¬ Nonempty (Refresh state context) :=
  fun ⟨certificate⟩ => cache_excluded cut recorded falseHead certificate.cache

theorem reobserve_excluded (cut : Cut state model) (recorded : GeneralCanonicalObservations.Recorded revision.snapshot observation)
    (falseHead : ¬ observation.Holds model) : ¬ Reobserve state revision :=
  fun certificate => cache_excluded cut recorded falseHead certificate.cache

end Yulang.GeneralNominalCenteredHeadMatStepRefresh
