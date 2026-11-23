import Yulang.GeneralDeclarativeWitnessSequentialNative360
import Yulang.GeneralDeclarativeWitnessNativeReceiver360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 56000000
namespace Yulang.GeneralDeclarativeWitnessSequentialReceiver361
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNativeReceiver360 (key)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared Layout prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews interpreted)
open GeneralDeclarativeWitnessNativeSnapshot360 (same)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)

/-- Use the returned continuation state, not an independently previewed state.
The source binder takes the actual newly emitted occurrence's triple. -/
def layout {negative r} (s : @Sequence negative r) : Layout :=
  ⟨s.final.ordinary,[(92,s.place)],
    [101,105,106,107,108,109,110,111,112,113,114,115],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Received {negative : Bool} {r : Run negative} (s : Sequence r) where
  prepared : Prepared r.env key s.receiver (layout s)
  literalHead : prepared.impl.head = [.var 92]
  span : Capture
  bound : slots [prepared.captures] key 92 = some span
  center : span.center = s.place.center
  body : Finished
  ran : execute (context r.env s.receiver prepared.impl (layout s)) = some body
  noWrites : body.fixed = []
  noKids : body.kids = []
  kept : preserves s.final.ordinary body.state = true

def receive {negative} {r : Run negative} (s : Sequence r) : Option (Received s) := do
  let p ← prepare r.env key s.receiver (layout s)
  if head : p.impl.head = [.var 92] then
    match binding : slots [p.captures] key 92 with
    | none => none
    | some cap =>
      if center : cap.center = s.place.center then
        match ran : execute (context r.env s.receiver p.impl (layout s)) with
        | none => none
        | some body =>
          if exact : body.fixed = [] ∧ body.kids = [] ∧
              preserves s.final.ordinary body.state = true then
            some ⟨p,head,cap,binding,center,body,ran,exact.1,exact.2.1,exact.2.2⟩
          else none
      else none
  else none

def Received.world {negative r s} (read : @Received negative r s) : World :=
  ⟨read.body.state,s.final.board⟩

def tailAtoms : List (Atom Nat) :=
  [(101,101),(101,101),(116,112),(112,116),(117,113),(113,117),(116,101),(101,117)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def finalState : State :=
  let s := GeneralDeclarativeWitnessSequentialNative360.final
  ⟨⟨s.normal.ordinary ++ tailAtoms,s.normal.intervals⟩,s.equations⟩

def inspect {negative r s} (read : @Received negative r s) : Bool :=
  (decide (read.span.lower = 116 ∧ read.span.center = 101 ∧ read.span.upper = 117)) &&
    same read.world.ordinary finalState

theorem actual_receiver_state (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).bind fun s => (receive s).map inspect).getD false = true := by
  cases negative <;> decide +kernel

theorem read_in_every_final_model {negative} {r : Run negative} {s : Sequence r}
    (root : originalBody negative = some r) (sent : sequence r = some s) (read : Received s)
    (m : Assignment) (v : NativeViews) (fit : Fits read.world m v) :
    (v read.span.center).bind (fun val => observe val (actualRead negative)) = some (m 61).1 ∧
    Holds m ⟨105,.variable 61⟩ ∧ s.ordinaryChild.result.fixed = [⟨105,.variable 61⟩] ∧
    printDemand s.receiver = (8,[(112,101,113)],[]) ∧ read.body.fixed = [] ∧ read.body.kids = [] := by
  have prior : Fits s.final m v := ⟨restrict ((preserves_iff ..).mp read.kept) m fit.1,fit.2⟩
  have old := GeneralDeclarativeWitnessSequentialNative360.one_state_checked_sequence root sent m v prior
  exact ⟨read.center.symm ▸ old.1,old.2.1,old.2.2.1,old.2.2.2,read.noWrites,read.noKids⟩


def model (upper : Bool) (scalar : Inference.Base) : Assignment := fun n =>
  if n = 116 then GeneralDeclarativeWitnessSequentialNative360.model upper scalar 112
  else if n = 117 then GeneralDeclarativeWitnessSequentialNative360.model upper scalar 113
  else GeneralDeclarativeWitnessSequentialNative360.model upper scalar n

theorem model_fits (upper : Bool) (scalar : Inference.Base) : Models finalState (model upper scalar) := by
  let prev := GeneralDeclarativeWitnessSequentialNative360.final
  let old := GeneralDeclarativeWitnessSequentialNative360.model upper scalar
  have h16 : 116 ∉ stateNames prev := by decide +kernel
  have h17 : 117 ∉ stateNames prev := by decide +kernel
  have agrees (n : Nat) (used : n ∈ stateNames prev) : old n = model upper scalar n := by
    have ne16 : n ≠ 116 := fun e => h16 (e ▸ used)
    have ne17 : n ≠ 117 := fun e => h17 (e ▸ used)
    simp [model,old,ne16,ne17]
  have prior := (preserves_models prev agrees).mp
    (GeneralDeclarativeWitnessSequentialNative360.ordered_model upper scalar)
  refine ⟨⟨?_,prior.1.2⟩,prior.2⟩
  intro atom included
  rcases (List.mem_append.mp included : atom ∈ prev.normal.ordinary ∨ atom ∈ tailAtoms) with old|new
  · exact prior.1.1 _ old
  · simp only [tailAtoms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at new
    rcases new with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact subtype_refl _

theorem exact_run_is_inhabited (negative : Bool) :
    ∃ (r : Run negative) (s : Sequence r) (read : Received s),
      originalBody negative = some r ∧ sequence r = some s ∧ receive s = some read ∧
      read.span.lower = 116 ∧ read.span.center = 101 ∧ read.span.upper = 117 ∧
      read.world.ordinary = finalState ∧
      ∀ upper scalar, Fits read.world (model upper scalar) (interpreted read.world.board (model upper scalar)) := by
  have proof := actual_receiver_state negative
  cases root : originalBody negative with
  | none => rw [root] at proof; cases proof
  | some r =>
    rw [root] at proof
    change ((sequence r).bind fun s => (receive s).map inspect).getD false = true at proof
    cases sent : sequence r with
    | none => rw [sent] at proof; cases proof
    | some s =>
      rw [sent] at proof
      change ((receive s).map inspect).getD false = true at proof
      cases applied : receive s with
      | none => rw [applied] at proof; cases proof
      | some read =>
        rw [applied] at proof
        have eq := Bool.and_eq_true_iff.mp (show inspect read = true from proof)
        have pos := of_decide_eq_true eq.1
        have world := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp eq.2
        exact ⟨r,s,read,rfl,sent,applied,pos.1,pos.2.1,pos.2.2,world,fun u v =>
          ⟨world.symm ▸ model_fits u v,fun _ => rfl⟩⟩

theorem checked_state_links_all_receipts (negative : Bool) :
    ∃ (r : Run negative) (s : Sequence r) (read : Received s),
      originalBody negative = some r ∧ sequence r = some s ∧ receive s = some read ∧
      printDemand s.receiver = (8,[(112,101,113)],[]) ∧
      (read.span.lower,read.span.center,read.span.upper) = (116,101,117) ∧
      read.prepared.impl.head = [.var 92] ∧ read.body.fixed = [] ∧ read.body.kids = [] ∧
      (∀ upper scalar, Fits read.world (model upper scalar) (interpreted read.world.board (model upper scalar))) ∧
      (∀ m v, Fits read.world m v →
        Holds m ⟨105,.variable 61⟩ ∧ (v 101).bind (fun value => observe value (actualRead negative)) = some (m 61).1) := by
  obtain ⟨r,s,read,root,sent,ran,lower,center,upper,_,fit⟩ := exact_run_is_inhabited negative
  have receipts := read_in_every_final_model root sent read _ _ (fit false .int)
  refine ⟨r,s,read,root,sent,ran,receipts.2.2.2.1,?_,read.literalHead,read.noWrites,read.noKids,fit,?_⟩
  · rw [lower,center,upper]
  · intro m v ready
    have all := read_in_every_final_model root sent read m v ready
    exact ⟨all.2.1,center ▸ all.1⟩

end Yulang.GeneralDeclarativeWitnessSequentialReceiver361
