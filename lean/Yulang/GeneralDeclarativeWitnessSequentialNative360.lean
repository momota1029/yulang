import Yulang.GeneralDeclarativeWitnessBranchFootprint360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 59000
set_option maxHeartbeats 56000000
namespace Yulang.GeneralDeclarativeWitnessSequentialNative360
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNestedOrdered360 (Child replay actual_model)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody forwardKey forwardDemand fixed)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared prepare)
open GeneralDeclarativeWitnessNativePipeline360 (authority valueCode)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease checkExactRelease)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews interpreted)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open PresenceNormalForm (Atom)

structure Sequence {negative : Bool} (r : Run negative) where
  ordinaryChild : Child r
  authority : ExactRelease ordinaryChild.final.board authority r.typed.write
  continuation : Prepared r.env forwardKey forwardDemand (fixed ordinaryChild.final)
  receiver : Demand
  exactReceiver : continuation.kids = [receiver]
  place : Capture
  args : receiver.arguments = [place]
  readsNative : place.center = r.typed.write.address.target

def sequence {negative} (r : Run negative) : Option (Sequence r) := do
  let ordinaryChild ← replay r
  let granted ← checkExactRelease ordinaryChild.final.board authority r.typed.write
  let continuation ← prepare r.env forwardKey forwardDemand (fixed ordinaryChild.final)
  match actual : continuation.kids with
  | [receiver] =>
    match args : receiver.arguments with
    | [place] =>
      if exactly : place.center = r.typed.write.address.target then
        some ⟨ordinaryChild,granted,continuation,receiver,actual,place,args,exactly⟩
      else none
    | _ => none
  | _ => none

def Sequence.final {negative r} (s : @Sequence negative r) : World :=
  ⟨s.continuation.stage,s.ordinaryChild.final.board⟩

def data {negative r} (s : @Sequence negative r) : Bool :=
  decide (printDemand s.ordinaryChild.demand = (6,[(106,61,107)],[(0,105)]) ∧
    s.ordinaryChild.result.fixed = [⟨105,.variable 61⟩] ∧
    printDemand s.receiver = (8,[(112,101,113)],[]) ∧ r.typed.write.code = valueCode negative)

theorem compiler_reallocates_after_ordinary_child (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map data).getD false = true := by
  cases negative <;> decide +kernel

theorem one_state_checked_sequence {negative} {r : Run negative} {s : Sequence r}
    (ran : originalBody negative = some r) (sent : sequence r = some s)
    (m : Assignment) (v : NativeViews) (fit : Fits s.final m v) :
    (v s.place.center).bind (fun value => observe value (actualRead negative)) = some (m 61).1 ∧
    Holds m ⟨105,.variable 61⟩ ∧
    s.ordinaryChild.result.fixed = [⟨105,.variable 61⟩] ∧
    printDemand s.receiver = (8,[(112,101,113)],[]) := by
  have checked := compiler_reallocates_after_ordinary_child negative
  rw [ran] at checked
  change ((sequence r).map data).getD false = true at checked
  rw [sent] at checked
  have fact := of_decide_eq_true (show data s = true from checked)
  have knownCode : r.typed.write.code = valueCode negative := fact.2.2.2
  have stored := GeneralDeclarativeWitnessNativeRelease360.checked_exact_written_value (w := s.final)
    s.authority m v fit
  have old := (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared s.continuation m fit.1).1
  have retains := ((model_append m).mp old).2
  have output := retains _ (by rw [fact.2.1]; exact List.mem_cons_self)
  refine ⟨?_,output,fact.2.1,fact.2.2.1⟩
  rw [s.readsNative,stored,knownCode]
  cases negative <;> rfl

def appended : List (Atom Nat) :=
  [(101,101),(101,101),(112,101),(101,112),(113,101),(101,113),(112,101),(101,113),
   (67,67),(67,67),(114,65),(65,114),(115,66),(66,115),(114,67),(67,115)].map
     fun p => .tyLe (.var p.1) (.var p.2)

def final : State := ⟨⟨GeneralDeclarativeWitnessNestedOrdered360.finalStage.normal.ordinary ++ appended,
    GeneralDeclarativeWitnessNestedOrdered360.finalStage.normal.intervals⟩,
  GeneralDeclarativeWitnessNestedOrdered360.finalStage.equations⟩

def exactState {negative r} (s : @Sequence negative r) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same s.final.ordinary final

theorem actual_ordered_state (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map exactState).getD false = true := by
  cases negative <;> decide +kernel

open GeneralDeclarativeWitnessNestedOrdered360 (shared finalStage)

def model (upper : Bool) (scalar : Inference.Base) : Assignment := fun n =>
  if n = 112 then shared upper scalar 101
  else if n = 113 then shared upper scalar 101
  else if n = 114 then shared upper scalar 65
  else if n = 115 then shared upper scalar 66
  else shared upper scalar n

theorem ordered_model (upper : Bool) (scalar : Inference.Base) : Models final (model upper scalar) := by
  have h12 : 112 ∉ stateNames finalStage := by decide +kernel
  have h13 : 113 ∉ stateNames finalStage := by decide +kernel
  have h14 : 114 ∉ stateNames finalStage := by decide +kernel
  have h15 : 115 ∉ stateNames finalStage := by decide +kernel
  have agrees (n : Nat) (seen : n ∈ stateNames finalStage) :
      shared upper scalar n = model upper scalar n := by
    have a : n ≠ 112 := fun e => h12 (e ▸ seen)
    have b : n ≠ 113 := fun e => h13 (e ▸ seen)
    have c : n ≠ 114 := fun e => h14 (e ▸ seen)
    have d : n ≠ 115 := fun e => h15 (e ▸ seen)
    simp [model,a,b,c,d]
  have prior := (preserves_models finalStage agrees).mp (actual_model upper scalar)
  refine ⟨⟨?_,prior.1.2⟩,prior.2⟩
  intro atom included
  rcases (List.mem_append.mp included : atom ∈ finalStage.normal.ordinary ∨ atom ∈ appended) with old|fresh
  · exact prior.1.1 _ old
  · simp only [appended,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at fresh
    rcases fresh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered

theorem whole_exact_sequence_is_inhabited (negative : Bool) :
    ∃ (r : Run negative) (s : Sequence r), originalBody negative = some r ∧ sequence r = some s ∧
      ∀ upper scalar,Fits s.final (model upper scalar) (interpreted s.final.board (model upper scalar)) := by
  have gate := actual_ordered_state negative
  cases ran : originalBody negative with
  | none => rw [ran] at gate; cases gate
  | some r =>
    rw [ran] at gate
    change ((sequence r).map exactState).getD false = true at gate
    cases sent : sequence r with
    | none => rw [sent] at gate; cases gate
    | some s =>
      rw [sent] at gate
      have remembered := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show exactState s = true from gate)
      refine ⟨r,s,rfl,sent,fun u t => ⟨remembered.symm ▸ ordered_model u t,fun _ => rfl⟩⟩

end Yulang.GeneralDeclarativeWitnessSequentialNative360
