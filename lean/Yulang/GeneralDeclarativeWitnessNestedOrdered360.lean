import Yulang.GeneralDeclarativeWitnessReleasedObservation360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 54000000
namespace Yulang.GeneralDeclarativeWitnessNestedOrdered360
open GeneralDeclarativeWitnessNestedInstall360 (Run native)
open GeneralDeclarativeWitnessNestedModels360 (stage commonModel fitting_nested authored_nested_value_in_every_fitting_model)
open GeneralDeclarativeWitnessNativePipeline360 (authority valueCode)
open GeneralDeclarativeWitnessOrderedChild360 (childKey childLayout)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews interpreted)
open GeneralDeclarativeWitnessNativeRelease360 (checkExactRelease ExactRelease)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand fixed_targets)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open CommonNominalFullCarrier (subtype_refl)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

structure Child {negative : Bool} (r : Run negative) where
  demand : Demand
  literal : r.prep.kids = [demand]
  span : Capture
  used : demand.arguments = [span]
  opened : ExactRelease r.final.board authority r.typed.write
  prepared : Prepared r.env childKey demand (childLayout r.final span)
  result : Finished
  actual : execute (context r.env demand prepared.impl (childLayout r.final span)) = some result
  terminalBody : result.kids = []
  keeps : preserves r.final.ordinary result.state = true

def replay {negative} (r : Run negative) : Option (Child r) := do
  let opened ← checkExactRelease r.final.board authority r.typed.write
  match kids : r.prep.kids with
  | [child] =>
    match slots : child.arguments with
    | [span] => do
      let p ← prepare r.env childKey child (childLayout r.final span)
      match ran : execute (context r.env child p.impl (childLayout r.final span)) with
      | none => none
      | some result =>
        if leafBody : result.kids = [] then
          if kept : preserves r.final.ordinary result.state = true then
            some ⟨child,kids,span,slots,opened,p,result,ran,leafBody,kept⟩
          else none
        else none
    | _ => none
  | _ => none

def Child.final {negative r} (c : @Child negative r) : World := ⟨c.result.state,r.final.board⟩

def receipt {negative r} (c : @Child negative r) : Bool :=
  decide (printDemand c.demand = (6,[(106,61,107)],[(0,105)]) ∧ c.result.fixed = [⟨105,.variable 61⟩])

theorem actual_full_child (negative : Bool) :
    ((native negative).bind fun r => (replay r).map receipt).getD false = true := by
  cases negative <;> decide +kernel

theorem joint_ordered_writes {negative} {r : Run negative} (root : native negative = some r)
    (child : Child r) (m : Assignment) (views : NativeViews) (fit : Fits child.final m views) :
    views 101 = some ((valueCode negative).eval m) ∧
    r.prep.kids = [child.demand] ∧ child.result.kids = [] ∧
    child.result.fixed.map Equation.left = child.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ item ∈ child.result.fixed,Holds m item := by
  have parent : Fits r.final m views :=
    ⟨restrict ((preserves_iff ..).mp child.keeps) m fit.1,fit.2⟩
  exact ⟨authored_nested_value_in_every_fitting_model root m views parent,child.literal,child.terminalBody,
    fixed_targets child.actual,((model_append m).mp fit.1).2⟩

def exactTail : List (Atom Nat) :=
  [(61,61),(61,61),(110,106),(106,110),(111,107),(107,111),(110,61),(61,111)].map
    fun p => .tyLe (.var p.1) (.var p.2)

def finalStage : State := ⟨⟨stage.normal.ordinary ++ exactTail,stage.normal.intervals⟩,
  stage.equations ++ [⟨105,.variable 61⟩]⟩

def checks {negative r} (c : @Child negative r) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same c.final.ordinary finalStage

theorem compiler_final_is_exact (negative : Bool) :
    ((native negative).bind fun r => (replay r).map checks).getD false = true := by
  cases negative <;> decide +kernel

def shared (upper : Bool) (scalar : Inference.Base) : Assignment := fun n =>
  if n = 110 then commonModel upper scalar 106
  else if n = 111 then commonModel upper scalar 107
  else commonModel upper scalar n

theorem actual_model (upper : Bool) (scalar : Inference.Base) : Models finalStage (shared upper scalar) := by
  have a10 : 110 ∉ stateNames stage := by decide +kernel
  have a11 : 111 ∉ stateNames stage := by decide +kernel
  have kept (n : Nat) (h : n ∈ stateNames stage) : commonModel upper scalar n = shared upper scalar n := by
    have diff10 : n ≠ 110 := fun e => a10 (e ▸ h)
    have diff11 : n ≠ 111 := fun e => a11 (e ▸ h)
    simp [shared,diff10,diff11]
  have prior := (preserves_models stage kept).mp (fitting_nested upper scalar)
  refine ⟨⟨?_,prior.1.2⟩,?_⟩
  · intro row used
    rcases (List.mem_append.mp used : row ∈ stage.normal.ordinary ∨ row ∈ exactTail) with old|tail
    · exact prior.1.1 _ old
    · simp only [exactTail,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at tail
      rcases tail with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered
  · intro row used
    rcases (List.mem_append.mp used : row ∈ stage.equations ∨ row ∈ [⟨105,.variable 61⟩]) with old|new
    · exact prior.2 _ old
    · cases List.mem_singleton.mp new
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _

theorem full_positive_in_one_model (negative upper : Bool) (scalar : Inference.Base) :
    ∃ (r : Run negative) (child : Child r),
      native negative = some r ∧ replay r = some child ∧
      Fits child.final (shared upper scalar) (interpreted child.final.board (shared upper scalar)) := by
  have positive := compiler_final_is_exact negative
  cases ran : native negative with
  | none => rw [ran] at positive; cases positive
  | some r =>
    rw [ran] at positive
    change ((replay r).map checks).getD false = true at positive
    cases read : replay r with
    | none => rw [read] at positive; cases positive
    | some child =>
      rw [read] at positive
      have matched := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show checks child = true from positive)
      exact ⟨r,child,rfl,read,matched.symm ▸ actual_model upper scalar,fun _ => rfl⟩

end Yulang.GeneralDeclarativeWitnessNestedOrdered360
