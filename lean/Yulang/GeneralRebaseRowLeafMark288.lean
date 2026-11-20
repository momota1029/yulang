import Yulang.GeneralRebaseRowLeafSlice288
import Yulang.GeneralRebaseRowSemanticMark287
import Yulang.GeneralRebaseLeafObservation288

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralRebaseRowLeafMark288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after effect after_exact)
open GeneralRebaseRowLeafSlice288 (prior finalFacts same_models)
open GeneralRebaseRowSemanticMark287 (marked target refines all_models_support known_output)
open GeneralRebaseLeafObservation288 (Cache AuxiliaryRefresh)
open GeneralNominalVersionedSupport233 (SliceModels)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem cache_iff (choice : Bool) : Cache (after choice) (marked choice) ↔ choice = true := by
  constructor
  · rintro ⟨⟨prior',effect',certificate,_⟩⟩
    have recorded := certificate.effectRecorded
    change effect' ∈ [effect choice] at recorded
    cases List.mem_singleton.mp recorded
    exact (GeneralRebaseRowLeafWitness288.parent_iff choice).mp certificate.settled
  · intro positive
    refine ⟨⟨prior choice,effect choice,(GeneralRebaseRowLeafSlice288.extension_iff choice).mpr positive,?_⟩⟩
    intro obs recorded m slice
    exact GeneralCanonicalObservations.recorded_sound _ m
      (all_models_support choice m ((same_models choice m).mp slice)) recorded

theorem auxiliary_iff (choice : Bool) :
    Nonempty (AuxiliaryRefresh (after choice) (target choice)) ↔ choice = true := by
  constructor
  · rintro ⟨certificate⟩
    exact (cache_iff choice).mp certificate.cache
  · intro pos
    refine ⟨⟨refines choice,rfl,(by intro _ found; exact found),?_,(cache_iff choice).mpr pos⟩⟩
    intro m valid
    have raw := all_models_support choice m valid
    exact ⟨raw.1,raw.2.2⟩

theorem auxiliary_only (choice : Bool) :
    (Nonempty (AuxiliaryRefresh (after choice) (target choice)) ↔ choice = true) ∧
    ¬ Nonempty (GeneralNominalVersionedMixedObservations233.Refresh (after choice) (target choice)) :=
  ⟨auxiliary_iff choice,GeneralRebaseRowSemanticMark287.not_certified_mark choice⟩

theorem positive_transport (m : Assignment) :
    Models (GeneralNominalVersionedRefresh232.refresh (after true) (target true)) m ↔ Models (after true) m :=
  by obtain ⟨cert⟩ := (auxiliary_iff true).mpr rfl; exact GeneralRebaseLeafObservation288.transform_exact cert m

theorem both_semantic_transports (choice : Bool) (m : Assignment) :
    Models (GeneralNominalVersionedRefresh232.refresh (after choice) (target choice)) m ↔ Models (after choice) m := by
  constructor
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.refresh_backward_raw valid
      (GeneralNominalRefinements.models (refines choice) m valid.1.1)
  · intro valid
    exact GeneralNominalVersionedObservationTransport233.refresh_forward_raw valid
      (all_models_support choice m valid)

theorem both_entail_but_only_positive_certified (choice : Bool) :
    (∀ m, Models (after choice) m → GeneralNominalState.Models (marked choice) m) ∧
    (Nonempty (AuxiliaryRefresh (after choice) (target choice)) ↔ choice = true) :=
  ⟨all_models_support choice,auxiliary_iff choice⟩

end Yulang.GeneralRebaseRowLeafMark288
