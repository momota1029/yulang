import Yulang.GeneralNominalVersionedSupport233
import Yulang.GeneralNominalVersionedRefresh232
set_option backward.isDefEq.respectTransparency false
/-! Sound observations justified by versioned trusted slices. This new auxiliary
cache interface is not substituted into Kernel232 in this cycle. -/
namespace Yulang.GeneralNominalVersionedObservations233
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedSupport233
open GeneralNominalCommonBridge (Assignment)
open GeneralCanonicalObservations (Observation Recorded)

variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

def CacheSound (state : State roles) (snapshot : GeneralNominalState.State) : Prop :=
  ∀ observation, Recorded snapshot observation →
    ∃ facts, Trusted state facts ∧ ∀ model, SliceModels state facts model → observation.Holds model

def Cut (state : State roles) (model : Assignment) : Prop :=
  ∀ facts, Trusted state facts → SliceModels state facts model

theorem full_cut (valid : GeneralNominalVersionedJournal232.Models state model) : Cut state model :=
  fun _ trusted => trusted_models trusted valid

theorem cache_sound (cache : CacheSound state snapshot) (recorded : Recorded snapshot observation)
    (valid : GeneralNominalVersionedJournal232.Models state model) : observation.Holds model := by
  obtain ⟨facts,trusted,sound⟩ := cache observation recorded
  exact sound model (trusted_models trusted valid)

theorem cache_excluded (cut : Cut state model) (recorded : Recorded snapshot observation)
    (falseHead : ¬ observation.Holds model) : ¬ CacheSound state snapshot := by
  intro cache
  obtain ⟨facts,trusted,sound⟩ := cache observation recorded
  exact falseHead (sound model (cut facts trusted))

theorem source_cache (state : State roles) : CacheSound state state.core.erased.source.state := by
  intro observation recorded
  exact ⟨[],.source,fun model valid => GeneralCanonicalObservations.recorded_sound _ model valid.1 recorded⟩

theorem raw_models
    (constraints : GeneralNominalCenteredHeadMatStepRefresh.Constraints snapshot model)
    (cache : CacheSound state snapshot) (valid : GeneralNominalVersionedJournal232.Models state model) :
    GeneralNominalState.Models snapshot model :=
  ⟨constraints.1,fun slot descriptor recorded => cache_sound cache (.nominal slot descriptor recorded) valid,constraints.2⟩

structure Refresh (state : State roles) (context : GeneralNominalCandidates.Context) where
  refines : GeneralNominalRefinements.Refines state.core.erased.current.context.state context.state
  interpretation : context.interpretation = state.core.erased.current.context.interpretation
  support : ∀ source ∈ GeneralNominalState.sources context.state,
    source ∈ GeneralNominalState.sources state.core.erased.current.context.state
  constraints : ∀ model, GeneralNominalVersionedJournal232.Models state model →
    GeneralNominalCenteredHeadMatStepRefresh.Constraints context.state model
  cache : CacheSound state context.state

structure Reobserve (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) : Prop where
  raw : ∀ model, GeneralNominalState.Models revision.snapshot model →
    GeneralNominalState.Models state.core.erased.current.context.state model
  cache : CacheSound state revision.snapshot

end Yulang.GeneralNominalVersionedObservations233
