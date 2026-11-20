import Yulang.GeneralObservedMetadataHistorical290
import Yulang.GeneralObservedMetadataMaterializationFixture290

/-! Closed check on the actual installed historical parent. Distinguish
the old recursive schema from the class-effect body compiled after install. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralObservedMetadataHistoryFixture290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowParentPacket287 (child plan sole_child)
open GeneralRebaseReceiptFixture289 (request producer_exact producer_matches)
open GeneralObservedMetadataActual290 (exact_install_diagnostics exact_initial_diagnostic)
open GeneralObservedMetadataHistorical290 (bodyCheck resolve ready_exact HasOwner)
open GeneralObservedMetadataLive290 (liveKeys ProposedModels)
open GeneralObservedMetadataBodies290 (bodyKeys compileFrom)
open GeneralObservedMetadataMaterializationFixture290 (alternate anotherInterp)
open GeneralObservedMetadataScope290 (good_exact)
open GeneralRebaseReceiptCollision289 (removed)

theorem recorded_body_keys (choice : Bool) :
    liveKeys (after choice).core root (effect choice).plan = [0,0] := by
  cases choice <;> decide +kernel

theorem actual_producer_body_good (choice : Bool) :
    bodyCheck (registry choice) (after choice) root interp (effect choice) = .good := by
  apply (good_exact ..).mpr
  exact ⟨fun _ _ => ⟨rfl,rfl,rfl⟩, fun _ _ _ h => by cases h⟩

theorem actual_owner (choice : Bool) :
    HasOwner (registry choice) (after choice) root (child choice) (request choice) interp := by
  refine ⟨effect choice,List.mem_singleton_self _,rfl,?_,?_,fun _ _ => rfl,actual_producer_body_good choice⟩
  · rw [show (effect choice).plan = plan choice from rfl,sole_child]
    exact List.mem_singleton_self _
  · rw [producer_exact]
    exact producer_matches choice

theorem actual_installed_results (choice : Bool) :
    resolve (registry choice) (after choice) root (child choice) (request choice) interp =
      .prior (.receipt (if choice then .ready else .unfinished)) := by
  cases choice
  · exact GeneralObservedMetadataHistorical290.preserved_other_outcome (exact_install_diagnostics false) (by decide)
  · exact (ready_exact ..).mpr ⟨exact_install_diagnostics true,actual_owner true⟩

theorem actual_preinstall (choice : Bool) :
    resolve (registry choice) before root (child choice) (request choice) interp =
      .prior (.receipt .missingProducer) :=
  GeneralObservedMetadataHistorical290.preserved_other_outcome (exact_initial_diagnostic choice) (by decide)

abbrev compoundBody : GeneralDictionaryAssociatedProvenance.Body :=
  .explicit ⟨0,0,.app 0 [.app 1 [.var 0]]⟩

theorem live_compiler_needs_compound_key :
    bodyKeys compoundBody = [0,1] ∧
    (compileFrom constructors anotherInterp compoundBody).isSome = true ∧
    (compileFrom (removed 1).constructors anotherInterp compoundBody).isSome = false := by
  decide +kernel

abbrev defaultBody : GeneralDictionaryAssociatedProvenance.Body :=
  .default 0 0 (.app 1 [.var 0])

theorem defaults_use_their_term_keys :
    bodyKeys defaultBody = [1] ∧
    (compileFrom constructors anotherInterp defaultBody).isSome = true ∧
    (compileFrom (removed 1).constructors anotherInterp defaultBody).isSome = false := by
  decide +kernel

end Yulang.GeneralObservedMetadataHistoryFixture290
