import Yulang.GeneralObservedMetadataTotal290

/-! A checked alternate declaration whose body is outside supported
materialization exposes the distinction between model agreement and Ready.
It is a supplied Plan, not an installed or source-reachable effect. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralObservedMetadataTotalFixture290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (before_requests after_requests after effect)
open GeneralRebaseRowParentPacket287 (packet plan)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCenteredHeadMatEffects (Ready compileBody bodySchema BodyHolds)
open GeneralNominalCommonBridge (Assignment)
open GeneralObservedMetadataMaterializationFixture290 (alternate alternate_checked bounds)
open GeneralObservedMetadataHistoryFixture290 (compoundBody actual_producer_body_good)
open GeneralObservedMetadataLive290 (liveKeys)
open GeneralObservedMetadataScope290 (certify good_exact)
open GeneralObservedMetadataTotal290 (total certified_total_iff_ready)

abbrev unsupported : Plan roles :=
  ⟨⟨registry true,ctx,(packet true).site,alternate,alternate_checked,bounds⟩,(plan true).input,rfl⟩

theorem no_compiled_body : compileBody unsupported compoundBody = none := rfl

theorem lookup_unique : GeneralDictionaryAssociatedProvenance.lookup roles alternate 0 = some compoundBody := rfl

theorem unsupported_metadata_agrees :
    certify (liveKeys before.core root unsupported) constructors interp constructors interp = .good := by
  decide +kernel

theorem unsupported_total_fails : total before.core root unsupported constructors interp = false := by
  decide +kernel

theorem unsupported_not_ready : ¬ Ready before.core root unsupported := by
  intro success
  have checked := (certified_total_iff_ready before.core root unsupported constructors interp
    unsupported_metadata_agrees).mpr success
  rw [unsupported_total_fails] at checked
  cases checked

theorem unsupported_effect_imposes_no_equation (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects before.core root unsupported m := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff _ _ _ _).mpr
  constructor
  · intro out present body found
    rw [before_requests] at present
    rcases List.mem_singleton.mp present with rfl
    have known : body = compoundBody := Option.some.inj (found.symm.trans lookup_unique)
    subst body
    simp [BodyHolds,bodySchema,no_compiled_body,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
  · intro a fa b fb _
    rw [before_requests] at fa fb
    rcases List.mem_singleton.mp fa with rfl
    rcases List.mem_singleton.mp fb with rfl
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem live_total_real (choice : Bool) :
    total (after choice).core root (effect choice).plan (registry choice).constructors interp = true := by
  apply (certified_total_iff_ready _ _ _ _ _ (actual_producer_body_good choice)).mpr
  apply GeneralNominalCenteredHeadMatEffects.ready_restrict
    (fun _ member => (after_requests choice _).mp member)
  exact (effect choice).ready

end Yulang.GeneralObservedMetadataTotalFixture290
