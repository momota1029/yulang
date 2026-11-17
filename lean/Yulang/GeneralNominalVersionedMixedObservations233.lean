import Yulang.GeneralNominalVersionedObservationTransport233
set_option backward.isDefEq.respectTransparency false
/-! A conservative auxiliary cache interface combining independently trusted
legacy and versioned slices. Both original systems inject into it. It is not
installed in Kernel232, and no cross-system trust induction is postulated. -/
namespace Yulang.GeneralNominalVersionedMixedObservations233
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralCanonicalObservations (Observation Recorded)
variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

def Justified (state : State roles) (observation : Observation) : Prop :=
  ∃ oldFacts newFacts,
    GeneralNominalCenteredHeadMatStepSupport.Trusted state.legacy oldFacts ∧
    GeneralNominalVersionedSupport233.Trusted state newFacts ∧
    ∀ model, GeneralNominalCenteredHeadMatStepSupport.Models state.legacy oldFacts model →
      GeneralNominalVersionedSupport233.SliceModels state newFacts model → observation.Holds model

def CacheSound (state : State roles) (snapshot : GeneralNominalState.State) : Prop :=
  ∀ observation, Recorded snapshot observation → Justified state observation

theorem legacy_cache (cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound state.legacy snapshot) :
    CacheSound state snapshot := by
  intro observation recorded
  obtain ⟨facts,trusted,sound⟩ := cache observation recorded
  exact ⟨facts,[],trusted,.source,fun model old _ => sound model old⟩

theorem versioned_cache (cache : GeneralNominalVersionedObservations233.CacheSound state snapshot) :
    CacheSound state snapshot := by
  intro observation recorded
  obtain ⟨facts,trusted,sound⟩ := cache observation recorded
  exact ⟨[],facts,.source,trusted,fun model _ current => sound model current⟩

theorem justified_sound (justified : Justified state observation) (valid : Models state model) : observation.Holds model := by
  obtain ⟨oldFacts,newFacts,oldTrusted,newTrusted,sound⟩ := justified
  exact sound model (GeneralNominalCenteredHeadMatStepSupport.trusted_models oldTrusted valid.1)
    (GeneralNominalVersionedSupport233.trusted_models newTrusted valid)

theorem cache_sound (cache : CacheSound state snapshot) (recorded : Recorded snapshot observation)
    (valid : Models state model) : observation.Holds model := justified_sound (cache observation recorded) valid

theorem raw_models
    (constraints : GeneralNominalCenteredHeadMatStepRefresh.Constraints snapshot model)
    (cache : CacheSound state snapshot) (valid : Models state model) : GeneralNominalState.Models snapshot model :=
  ⟨constraints.1,fun slot descriptor recorded => cache_sound cache (.nominal slot descriptor recorded) valid,constraints.2⟩

structure Refresh (state : State roles) (context : GeneralNominalCandidates.Context) where
  refines : GeneralNominalRefinements.Refines state.core.erased.current.context.state context.state
  interpretation : context.interpretation = state.core.erased.current.context.interpretation
  support : ∀ source ∈ GeneralNominalState.sources context.state,
    source ∈ GeneralNominalState.sources state.core.erased.current.context.state
  constraints : ∀ model, Models state model → GeneralNominalCenteredHeadMatStepRefresh.Constraints context.state model
  cache : CacheSound state context.state

structure Reobserve (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) : Prop where
  raw : ∀ model, GeneralNominalState.Models revision.snapshot model →
    GeneralNominalState.Models state.core.erased.current.context.state model
  cache : CacheSound state revision.snapshot

def of_legacy_refresh (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh state.legacy context) :
    Refresh state context :=
  ⟨certificate.refines,certificate.interpretation,certificate.support,
    fun model valid => certificate.constraints model valid.1,legacy_cache certificate.cache⟩

def of_versioned_refresh (certificate : GeneralNominalVersionedObservations233.Refresh state context) :
    Refresh state context :=
  ⟨certificate.refines,certificate.interpretation,certificate.support,certificate.constraints,versioned_cache certificate.cache⟩

theorem refresh_models (certificate : Refresh state context) :
    Models (GeneralNominalVersionedRefresh232.refresh state context) model ↔ Models state model := by
  constructor
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.refresh_backward_raw valid
      (GeneralNominalRefinements.models certificate.refines model valid.1.1)
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.refresh_forward_raw valid
      (raw_models (certificate.constraints model valid) certificate.cache valid)

theorem reobserve_models {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}
    (certificate : Reobserve state revision) :
    Models (GeneralNominalVersionedRefresh232.reobserve state revision) model ↔ Models state model := by
  constructor
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.reobserve_backward_raw revision valid
      (certificate.raw model valid.1.1)
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.reobserve_forward_raw revision valid
      (raw_models ⟨valid.1.1.1,valid.1.1.2.2⟩ certificate.cache valid)

end Yulang.GeneralNominalVersionedMixedObservations233
