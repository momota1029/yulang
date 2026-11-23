import Yulang.GeneralDeclarativeWitnessNativeReceiver360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 53000000
namespace Yulang.GeneralDeclarativeWitnessReceiverModel360
open GeneralDeclarativeWitnessNativeReceiver360 (Received receive same_model_received_binder)
open GeneralDeclarativeWitnessReleasedForward360 (Forwarded originalBody send)
open GeneralDeclarativeWitnessForwardModel360 (state model fitting_forwarding_state)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

def receivedAtoms : List (Atom Nat) :=
  [(101,101),(101,101),(114,110),(110,114),(115,111),(111,115),(114,101),(101,115)].map
    fun pair => .tyLe (.var pair.1) (.var pair.2)

def finalState : State :=
  ⟨⟨state.normal.ordinary ++ receivedAtoms,state.normal.intervals⟩,state.equations⟩

def verify {negative r f} (out : @Received negative r f) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same out.world.ordinary finalState

theorem exact_actual_receiver_constraints (negative : Bool) :
    ((originalBody negative).bind fun r => (send r).bind fun f => (receive f).map verify).getD false = true := by
  cases negative <;> decide +kernel

def fullModel (upper : Bool) (scalar : Inference.Base) : Assignment := fun name =>
  if name = 114 then model upper scalar 110
  else if name = 115 then model upper scalar 111
  else model upper scalar name

theorem model_fits (upper : Bool) (scalar : Inference.Base) : Models finalState (fullModel upper scalar) := by
  have h14 : 114 ∉ stateNames state := by decide +kernel
  have h15 : 115 ∉ stateNames state := by decide +kernel
  have same (n : Nat) (seen : n ∈ stateNames state) : model upper scalar n = fullModel upper scalar n := by
    have no14 : n ≠ 114 := fun e => h14 (e ▸ seen)
    have no15 : n ≠ 115 := fun e => h15 (e ▸ seen)
    simp [fullModel,no14,no15]
  have prior := (preserves_models state same).mp (fitting_forwarding_state upper scalar)
  refine ⟨⟨?_,prior.1.2⟩,prior.2⟩
  intro a included
  rcases (List.mem_append.mp included : a ∈ state.normal.ordinary ∨ a ∈ receivedAtoms) with rest|new
  · exact prior.1.1 _ rest
  · simp only [receivedAtoms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem actual_received_in_same_world (negative : Bool) :
    ∃ (r : Run negative) (forward : Forwarded r) (received : Received forward),
      originalBody negative = some r ∧ send r = some forward ∧ receive forward = some received ∧
      received.prepared.impl.head = [.var 92] ∧ received.span.center = 101 ∧
      ∀ upper scalar,
        let m := fullModel upper scalar
        let v := interpreted received.world.board m
        Fits received.world m v ∧
          (v 101).bind (fun value => observe value (actualRead negative)) = some (m 61).1 ∧
          received.body.fixed = [] ∧ received.body.kids = [] := by
  have gate := exact_actual_receiver_constraints negative
  cases root : originalBody negative with
  | none => rw [root] at gate; cases gate
  | some r =>
    rw [root] at gate
    change ((send r).bind fun f => (receive f).map verify).getD false = true at gate
    cases sent : send r with
    | none => rw [sent] at gate; cases gate
    | some f =>
      rw [sent] at gate
      change ((receive f).map verify).getD false = true at gate
      cases received : receive f with
      | none => rw [received] at gate; cases gate
      | some result =>
        rw [received] at gate
        have current := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show verify result = true from gate)
        have fit (u : Bool) (scalar : Inference.Base) :
            Fits result.world (fullModel u scalar) (interpreted result.world.board (fullModel u scalar)) :=
          ⟨current.symm ▸ model_fits u scalar,fun _ => rfl⟩
        have present := same_model_received_binder root sent result _ _ (fit false .int)
        refine ⟨r,f,result,rfl,sent,received,result.literalHead,present.2.1,?_⟩
        intro u scalar
        have read := same_model_received_binder root sent result _ _ (fit u scalar)
        exact ⟨fit u scalar,read.2.1 ▸ read.2.2.1,read.2.2.2⟩

end Yulang.GeneralDeclarativeWitnessReceiverModel360
