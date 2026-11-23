import Yulang.GeneralDeclarativeWitnessReleasedForward360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 53000000
namespace Yulang.GeneralDeclarativeWitnessForwardModel360
open GeneralDeclarativeWitnessReleasedForward360
  (Forwarded originalBody send confirm child_reads_exact_released_output different_actual_body_compiles_child_at_released_center)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNestedModels360 (stage commonModel fitting_nested)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessNativePipeline360 (valueCode)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def additions : List (Atom Nat) :=
  [(101,101),(101,101),(110,101),(101,110),(111,101),(101,111),(110,101),(101,111),
   (67,67),(67,67),(112,65),(65,112),(113,66),(66,113),(112,67),(67,113)].map
     fun coordinates => .tyLe (.var coordinates.1) (.var coordinates.2)

def state : State :=
  ⟨⟨stage.normal.ordinary ++ additions,stage.normal.intervals⟩,stage.equations⟩

def stageRead {negative r} (a : @Forwarded negative r) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same a.world.ordinary state

theorem exact_forwarding_state (negative : Bool) :
    ((originalBody negative).bind fun r => (send r).map stageRead).getD false = true := by
  cases negative <;> decide +kernel

def model (upper : Bool) (scalar : Inference.Base) : Assignment := fun n =>
  if n = 110 then commonModel upper scalar 101
  else if n = 111 then commonModel upper scalar 101
  else if n = 112 then commonModel upper scalar 65
  else if n = 113 then commonModel upper scalar 66
  else commonModel upper scalar n

theorem fitting_forwarding_state (upper : Bool) (scalar : Inference.Base) : Models state (model upper scalar) := by
  have no10 : 110 ∉ stateNames stage := by decide +kernel
  have no11 : 111 ∉ stateNames stage := by decide +kernel
  have no12 : 112 ∉ stateNames stage := by decide +kernel
  have no13 : 113 ∉ stateNames stage := by decide +kernel
  have priorSlots (n : Nat) (member : n ∈ stateNames stage) :
      commonModel upper scalar n = model upper scalar n := by
    have d10 : n ≠ 110 := fun e => no10 (e ▸ member)
    have d11 : n ≠ 111 := fun e => no11 (e ▸ member)
    have d12 : n ≠ 112 := fun e => no12 (e ▸ member)
    have d13 : n ≠ 113 := fun e => no13 (e ▸ member)
    simp [model,d10,d11,d12,d13]
  have had := (preserves_models stage priorSlots).mp (fitting_nested upper scalar)
  refine ⟨⟨?_,had.1.2⟩,had.2⟩
  intro atom included
  rcases (List.mem_append.mp included : atom ∈ stage.normal.ordinary ∨ atom ∈ additions) with prior|new
  · exact had.1.1 _ prior
  · simp only [additions,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered

theorem actual_child_binds_native_payload {negative} {r : Run negative} {child : Forwarded r}
    (root : originalBody negative = some r) (forwarded : send r = some child)
    (m : Assignment) (v : NativeViews) (fit : Fits child.world m v) :
    child.slot.center = 101 ∧
      (v child.slot.center).bind (fun value => observe value (actualRead negative)) = some (m 61).1 := by
  have compiled := different_actual_body_compiles_child_at_released_center negative
  rw [root] at compiled
  change ((send r).map confirm).getD false = true at compiled
  rw [forwarded] at compiled
  have output := of_decide_eq_true (show confirm child = true from compiled)
  have code : r.typed.code = valueCode negative := output.2.2
  have read := child_reads_exact_released_output child m v fit
  have center : child.slot.center = 101 := child.addressed
  refine ⟨center,?_⟩
  rw [read.2.2.2,code]
  cases negative <;> rfl

theorem real_forwarded_same_model (negative : Bool) :
    ∃ (r : Run negative) (c : Forwarded r),
      originalBody negative = some r ∧ send r = some c ∧ c.slot.center = 101 ∧
      ∀ upper scalar,Fits c.world (model upper scalar) (interpreted c.world.board (model upper scalar)) ∧
        ((interpreted c.world.board (model upper scalar) c.slot.center).bind
          (fun value => observe value (actualRead negative))) = some (model upper scalar 61).1 := by
  have check := exact_forwarding_state negative
  cases r : originalBody negative with
  | none => rw [r] at check; cases check
  | some a =>
    rw [r] at check
    change ((send a).map stageRead).getD false = true at check
    cases sent : send a with
    | none => rw [sent] at check; cases check
    | some c =>
      rw [sent] at check
      have same := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show stageRead c = true from check)
      refine ⟨a,c,rfl,sent,c.addressed,?_⟩
      intro upper scalar
      have fit : Fits c.world (model upper scalar) (interpreted c.world.board (model upper scalar)) :=
        ⟨same.symm ▸ fitting_forwarding_state upper scalar,fun _ => rfl⟩
      exact ⟨fit,(actual_child_binds_native_payload r sent _ _ fit).2⟩

end Yulang.GeneralDeclarativeWitnessForwardModel360
