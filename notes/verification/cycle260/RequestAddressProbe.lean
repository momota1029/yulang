import Yulang.GeneralRebaseBodyActual260
namespace Cycle260RequestAddressProbe
open Yulang
open GeneralDictionaryDefaultGap206Source
open GeneralDefaultRebaseBody260 (body)
open GeneralDictionaryVersionedGap206233 (current)

-- Only output0 is an actual request in this source. output1 is a deliberately
-- supplied internal decoder argument, not a source-reachable new request.
theorem alternate_not_requested :
 (⟨0,1⟩ : GeneralSourceState.Output) ∉ GeneralNominalCenteredHeadOutputs.requests current.core root := by
 intro member
 have impossible := GeneralDefaultRebaseBody260.request_exact ⟨0,1⟩ member
 have targets := congrArg GeneralSourceState.Output.target impossible
 cases targets

theorem same_address :
 GeneralRebaseBodyDecoder260.compile plan 37 ⟨0,0⟩ = GeneralRebaseBodyDecoder260.compile plan 37 ⟨0,1⟩ := rfl

theorem alternate_holds (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalVersionedEffects231.BodyHolds plan 1 assignment body := by
 apply (GeneralNominalVersionedEffects231.body_holds_iff ..).mpr
 apply (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mpr
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem actual_fails : ¬ GeneralNominalVersionedEffects231.BodyHolds plan 0 counter body := by
 intro valid
 have classes := (GeneralDefaultRebaseBody260.classes_exact counter).mpr
   ((GeneralDefaultRebaseBody260.body_meaning counter).mp valid)
 exact GeneralDefaultRebaseInstalled260.counter_removed.2
  ((GeneralDefaultRebaseModels260.final_exact counter).mpr
    ⟨GeneralDictionaryVersionedGap206Install233.counter_model,classes⟩)

theorem address_does_not_determine_payload :
 GeneralRebaseBodyDecoder260.compile plan 37 ⟨0,0⟩ = GeneralRebaseBodyDecoder260.compile plan 37 ⟨0,1⟩ ∧
 GeneralNominalVersionedEffects231.BodyHolds plan 1 counter body ∧
 ¬ GeneralNominalVersionedEffects231.BodyHolds plan 0 counter body :=
 ⟨same_address,alternate_holds counter,actual_fails⟩
#print axioms address_does_not_determine_payload
end Cycle260RequestAddressProbe
