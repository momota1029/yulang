import Yulang.GeneralRebaseLeafOutput288
import Yulang.GeneralNominalVersionedObservationTransport233

/-! Local certificate and model transport for the unchanged refresh
transformer. It is deliberately not the kernel's Refresh certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLeafObservation288
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedSupport233 (SliceModels Fact)
open GeneralCanonicalObservations (Recorded)
open GeneralRebaseLeafOutput288 (Extension output_models)
variable {roles : Roles.RoleDecls}

structure Cache (state : State roles) (snapshot : GeneralNominalState.State) : Prop where
  supports : ∃ prior effect, Extension state prior effect ∧
    ∀ observation, Recorded snapshot observation →
      ∀ model, SliceModels state (.output effect :: prior) model → observation.Holds model

theorem observation {state : State roles} {snapshot : GeneralNominalState.State}
    (cache : Cache state snapshot) (recorded : Recorded snapshot seen)
    (valid : Models state model) : seen.Holds model := by
  obtain ⟨_,_,extension,sound⟩ := cache.supports
  exact sound seen recorded model (output_models extension valid)

structure AuxiliaryRefresh (state : State roles) (context : GeneralNominalCandidates.Context) where
  refines : GeneralNominalRefinements.Refines state.core.erased.current.context.state context.state
  interpretation : context.interpretation = state.core.erased.current.context.interpretation
  support : ∀ source ∈ GeneralNominalState.sources context.state,
    source ∈ GeneralNominalState.sources state.core.erased.current.context.state
  constraints : ∀ model, Models state model → GeneralNominalCenteredHeadMatStepRefresh.Constraints context.state model
  cache : Cache state context.state

theorem raw_sound {state : State roles} {context : GeneralNominalCandidates.Context}
    (aux : AuxiliaryRefresh state context) (valid : Models state model) :
    GeneralNominalState.Models context.state model :=
  ⟨(aux.constraints model valid).1,fun slot descriptor recorded =>
    observation aux.cache (.nominal slot descriptor recorded) valid,(aux.constraints model valid).2⟩

theorem transform_exact {state : State roles} {context : GeneralNominalCandidates.Context}
    (aux : AuxiliaryRefresh state context) (model : Assignment) :
    Models (GeneralNominalVersionedRefresh232.refresh state context) model ↔ Models state model := by
  constructor
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.refresh_backward_raw valid
      (GeneralNominalRefinements.models aux.refines model valid.1.1)
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.refresh_forward_raw valid (raw_sound aux valid)

end Yulang.GeneralRebaseLeafObservation288
