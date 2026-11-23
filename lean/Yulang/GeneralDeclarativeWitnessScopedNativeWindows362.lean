import Yulang.GeneralDeclarativeWitnessNonpointReceiver362
import Yulang.GeneralDeclarativeWitnessInheritedEnvelope362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 72000
set_option maxHeartbeats 78000000
namespace Yulang.GeneralDeclarativeWitnessScopedNativeWindows362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority ctor first last)
open GeneralDeclarativeWitnessNativeOrder362 (Chain chain low center high release_and_order_in_every_fit)
open GeneralDeclarativeWitnessInheritedEnvelope362 (Enveloped envelope interval)
open GeneralDeclarativeWitnessNativeInvariantCut362 (wrap proper_record_interval)
open GeneralDeclarativeWitnessNonpointPort362 (Transport forward)
open GeneralDeclarativeWitnessNonpointReceiver362 (Applied receive fitting exactBody fitting_state)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact_model_iff)
open GeneralDeclarativeWitnessOrderedNativeRelease362 (withoutLow withoutMid withoutHigh)
open GeneralDeclarativeWitnessNativeValue360 (Value)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews atTarget)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralNominalCommonBridge (Assignment)

structure Closed {contra : Bool} (r : Run contra) where
  ordering : Chain r
  ordered : chain r = some ordering
  projected : Enveloped r
  chosen : envelope r = some projected
  emitted : Transport r authority
  received : Applied emitted

def close {contra} (r : Run contra) : Option (Closed r) :=
  match one : chain r, two : envelope r with
  | some ord,some bounds => do
    let p ← forward r authority
    let actual ← receive p
    pure ⟨ord,one,bounds,two,p,actual⟩
  | _,_ => none

def checked {contra r} (w : @Closed contra r) : Bool :=
  exactBody w.received &&
  ([210,211,214,215].all (fun n => (atTarget w.received.world.board n).isNone)) &&
  (forward r withoutLow).isNone && (forward r withoutMid).isNone && (forward r withoutHigh).isNone

theorem exact_receive_and_controls (contra : Bool) :
    ((run contra).bind fun r => (close r).map checked).getD false = true := by cases contra <;> decide +kernel

theorem ordered_released_values_in_actual_receiver {contra} {r : Run contra}
    (startup : run contra = some r) (w : Closed r) (m : Assignment) (v : NativeViews)
    (fit : Fits w.received.world m v) :
    (v 201 = some (.unary (ctor contra) (.leaf (m (first contra)).1)) ∧
      v 202 = some (.unary (ctor contra) (.leaf (m 61).1)) ∧
      v 203 = some (.unary (ctor contra) (.leaf (m (last contra)).1))) ∧
    ContextDerives table m false (low r) (center r) ∧ ContextDerives table m false (center r) (high r) ∧
    ContextDerives table m false (wrap (interval (ctor contra) w.projected.a w.projected.b))
      (wrap (interval (ctor contra) w.projected.b w.projected.c)) := by
  have upstream := (GeneralDeclarativeWitnessNonpointReceiver362.returned_body_retains_prior_fit w.received m v fit).2
  have directed := release_and_order_in_every_fit startup w.ordered m v upstream
  have nested := GeneralDeclarativeWitnessInheritedEnvelope362.overlaps_at_the_separately_authored_center startup w.chosen m v upstream
  exact ⟨directed.2.2.2,directed.2.1,directed.2.2.1,nested.2.2.2.2.2⟩

theorem actual_receiver_with_two_fits (contra : Bool) :
    ∃ (r : Run contra) (w : Closed r), run contra = some r ∧ close r = some w ∧
      ∀ u, Fits w.received.world (fitting contra u) (interpreted w.received.world.board (fitting contra u)) := by
  have q := exact_receive_and_controls contra
  cases made : run contra with
  | none => rw [made] at q; cases q
  | some r =>
    rw [made] at q
    change ((close r).map checked).getD false = true at q
    cases output : close r with
    | none => rw [output] at q; cases q
    | some w =>
      rw [output] at q
      have p := Bool.and_eq_true_iff.mp (show checked w = true from q)
      have p := Bool.and_eq_true_iff.mp p.1
      have p := Bool.and_eq_true_iff.mp p.1
      have p := Bool.and_eq_true_iff.mp p.1
      have state := (Bool.and_eq_true_iff.mp p.1).2
      exact ⟨r,w,rfl,output,fun u => ⟨(exact_model_iff state _).mpr (fitting_state contra u),fun _ => rfl⟩⟩

theorem equal_ordinary_slots_do_not_collapse_native_endpoints {contra} {r : Run contra} {w : Closed r}
    (startup : run contra = some r) (u : Bool)
    (fit : Fits w.received.world (fitting contra u) (interpreted w.received.world.board (fitting contra u))) :
    (fitting contra u 201).1 = (fitting contra u 203).1 ∧
    interpreted w.received.world.board (fitting contra u) 201 ≠
      interpreted w.received.world.board (fitting contra u) 203 := by
  have reads := (ordered_released_values_in_actual_receiver startup w _ _ fit).1
  refine ⟨?_,?_⟩
  · cases contra <;> rfl
  · intro same
    rw [reads.1,reads.2.2] at same
    have payload := Value.leaf.inj (Value.unary.inj (Option.some.inj same)).2
    apply proper_record_interval
    cases contra
    · have eq : GeneralDeclarativeWitnessRecordWidthFixture359.lowTy = GeneralDeclarativeWitnessRecordWidthFixture359.highTy := payload
      rw [← eq]
      exact CommonNominalFullCarrier.subtype_refl _
    · have eq : GeneralDeclarativeWitnessRecordWidthFixture359.highTy = GeneralDeclarativeWitnessRecordWidthFixture359.lowTy := payload
      rw [eq]
      exact CommonNominalFullCarrier.subtype_refl _

end Yulang.GeneralDeclarativeWitnessScopedNativeWindows362
