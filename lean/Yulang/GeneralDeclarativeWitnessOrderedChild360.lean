import Yulang.GeneralDeclarativeWitnessNativeSnapshot360
import Yulang.GeneralDeclarativeWitnessNativeModel360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralDeclarativeWitnessOrderedChild360
open GeneralDeclarativeWitnessNativePipeline360 (Run run authority valueCode)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare context)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessNativeModel360 (checked_target_in_every_native_model model afterWhere fitting_ordinary_nonpoint)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease checkExactRelease)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand fixed_targets)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeWitnessRecordWidthFixture359 (endpoints_ordered)
open CommonNominalFullCarrier (subtype_refl)
open PresenceNormalForm (Atom)
open GeneralDeclarativeHead320 (Models Equation State)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralNominalCommonBridge (Assignment)

def childKey : FrameKey := ⟨[5,0],73,1⟩

def childLayout (w : World) (span : Capture) : Layout :=
  ⟨w.ordinary,[(90,span)],[101,105,106,107],fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Checked {negative : Bool} (r : Run negative) where
  opened : ExactRelease r.current.board authority r.output.write
  child : Demand
  children : r.prepared.kids = [child]
  span : Capture
  actual : child.arguments = [span]
  prepared : Prepared r.env childKey child (childLayout r.current span)
  body : Finished
  executed : execute (context r.env child prepared.impl (childLayout r.current span)) = some body
  done : body.kids = []
  forward : preserves r.current.ordinary body.state = true

def replay {negative : Bool} (r : Run negative) : Option (Checked r) := do
  let opened ← checkExactRelease r.current.board authority r.output.write
  match source : r.prepared.kids with
  | [child] =>
    match input : child.arguments with
    | [span] => do
      let p ← prepare r.env childKey child (childLayout r.current span)
      match ran : execute (context r.env child p.impl (childLayout r.current span)) with
      | none => none
      | some wrote =>
        if done : wrote.kids = [] then
          if keeps : preserves r.current.ordinary wrote.state = true then
            some ⟨opened,child,source,span,input,p,wrote,ran,done,keeps⟩
          else none
        else none
    | _ => none
  | _ => none

def Checked.final {negative r} (c : @Checked negative r) : World :=
  ⟨c.body.state,r.current.board⟩

theorem same_world_obligation {negative r} (c : @Checked negative r) (m : Assignment) (v : NativeViews) :
    Fits c.final m v → Fits r.current m v := by
  intro final
  exact ⟨restrict ((preserves_iff ..).mp c.forward) m final.1,final.2⟩

def report {negative r} (c : @Checked negative r) : Bool :=
  decide (printDemand c.child = (6,[(106,61,107)],[(0,105)]) ∧
    c.body.fixed = [⟨105,.variable 61⟩])

theorem real_generated_child_replays (negative : Bool) :
    ((run negative).bind fun r => (replay r).map report).getD false = true := by
  cases negative <;> decide +kernel

theorem all_model_ordered_fixed_writes {negative} {r : Run negative}
    (ran : run negative = some r) (child : Checked r)
    (m : Assignment) (views : NativeViews) (fit : Fits child.final m views) :
    views 101 = some ((valueCode negative).eval m) ∧
    r.prepared.kids = [child.child] ∧ child.body.kids = [] ∧
    child.body.fixed.map Equation.left = child.child.outputs.map GeneralSourceState.Output.target ∧
    ∀ row ∈ child.body.fixed,Holds m row := by
  have native := checked_target_in_every_native_model ran m views (same_world_obligation child m views fit)
  exact ⟨native.1,child.children,child.done,fixed_targets child.executed,((model_append m).mp fit.1).2⟩

def childAtoms : List (Atom Nat) :=
  [(61,61),(61,61),(108,106),(106,108),(109,107),(107,109),(108,61),(61,109)].map
    fun positions => .tyLe (.var positions.1) (.var positions.2)

def compilerFinal : State :=
  ⟨⟨afterWhere.normal.ordinary ++ childAtoms,afterWhere.normal.intervals⟩,
    afterWhere.equations ++ [⟨105,.variable 61⟩]⟩

def exactStage {negative r} (child : @Checked negative r) : Bool :=
  GeneralDeclarativeWitnessNativeSnapshot360.same child.final.ordinary compilerFinal

theorem actual_stage_has_exact_aliases (negative : Bool) :
    ((run negative).bind fun r => (replay r).map exactStage).getD false = true := by
  cases negative <;> decide +kernel

def sharedModel (upper : Bool) : Assignment := fun n =>
  if n = 108 then model upper .int 106
  else if n = 109 then model upper .int 107
  else model upper .int n

theorem actual_child_model (upper : Bool) : Models compilerFinal (sharedModel upper) := by
  have h8 : 108 ∉ stateNames afterWhere := by decide +kernel
  have h9 : 109 ∉ stateNames afterWhere := by decide +kernel
  have preserved (n : Nat) (present : n ∈ stateNames afterWhere) : model upper .int n = sharedModel upper n := by
    have e8 : n ≠ 108 := fun same => h8 (same ▸ present)
    have e9 : n ≠ 109 := fun same => h9 (same ▸ present)
    simp [sharedModel,e8,e9]
  have fitted := (preserves_models afterWhere preserved).mp (fitting_ordinary_nonpoint upper .int)
  refine ⟨⟨?_,fitted.1.2⟩,?_⟩
  · intro a member
    rcases (List.mem_append.mp member : a ∈ afterWhere.normal.ordinary ∨ a ∈ childAtoms) with old|added
    · exact fitted.1.1 _ old
    · simp only [childAtoms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at added
      rcases added with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals cases upper <;> first | exact subtype_refl _ | exact endpoints_ordered
  · intro e member
    rcases (List.mem_append.mp member : e ∈ afterWhere.equations ∨ e ∈ [⟨105,.variable 61⟩]) with old|added
    · exact fitted.2 _ old
    · cases List.mem_singleton.mp added
      exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _

theorem real_shared_fit (negative : Bool) (upper : Bool) :
    ∃ (r : Run negative) (child : Checked r),
      run negative = some r ∧ replay r = some child ∧
      Fits child.final (sharedModel upper)
        (GeneralDeclarativeWitnessNativeInstall360.interpreted child.final.board (sharedModel upper)) := by
  have gate := actual_stage_has_exact_aliases negative
  cases rr : run negative with
  | none => rw [rr] at gate; cases gate
  | some r =>
    rw [rr] at gate
    change ((replay r).map exactStage).getD false = true at gate
    cases cc : replay r with
    | none => rw [cc] at gate; cases gate
    | some child =>
      rw [cc] at gate
      have stages := GeneralDeclarativeWitnessNativeSnapshot360.same_exact.mp (show exactStage child = true from gate)
      exact ⟨r,child,rfl,cc,stages.symm ▸ actual_child_model upper,fun _ => rfl⟩

end Yulang.GeneralDeclarativeWitnessOrderedChild360
