import Yulang.GeneralDeclarativeWitnessCovariantInterval353
import Yulang.GeneralDeclarativeWitnessCovariantFixture353

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 36000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralDeclarativeWitnessCovariantIntervalFixture353
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessCovariantInterval353 (Wire read decode)
open GeneralDeclarativeWitnessCovariantFixture353 (root rows stage out)
open GeneralDeclarativeWitnessCompiler350 (Finished execute printDemand)
open GeneralDeclarativeWitnessOrderedFixture350 (literalPlan atomic)

def upperEq : Equation := ⟨10,.join (.variable 9) (.primitive (.scalar .unit) [])⟩
def inputState : State :=
  ⟨⟨[atomic 7 9,atomic 9 10],[]⟩,stage.equations ++ [upperEq]⟩
def problem : Problem :=
  let base := GeneralDeclarativeWitnessCovariantFixture353.problem
  let extended := rows ++ [⟨11,13,0,7⟩,⟨21,13,0,10⟩]
  let target := {root with arguments := [⟨11,20,21⟩]}
  {base with stage := inputState, rows := extended, demand := target, keep := [11,20,21,30,31]}
def wire : Wire := ⟨GeneralDeclarativeWitnessCovariantFixture353.wire,3,4,.constraint 0,.constraint 1⟩

def run : Option Finished := do
  let b ← read problem wire
  execute b.ctx

def data : Option (State × GeneralDeclarativeWitnessCompiler350.Wire) := do
  let f ← run
  let receipt ← literalPlan f.state f.state
  pure (f.state,⟨f.kids.map printDemand,f.fixed,receipt⟩)

def test (p : Problem := problem) (w : Wire := wire)
    (edit : GeneralDeclarativeWitnessCompiler350.Wire → GeneralDeclarativeWitnessCompiler350.Wire := id) : Bool :=
  (data.map (fun (s,r) => (decode p w s (edit r)).isSome)).getD false

theorem accepted : test = true := by decide +kernel

theorem real_coordinates : (read problem wire |>.map (fun b =>
    ((b.arg.lower,b.arg.center,b.arg.upper), b.center.names))) =
    some ((11,20,21),[31,32]) := by decide +kernel

theorem cannot_use_endpoint_for_center :
    test problem {wire with center := {wire.center with center := 3}} = false := by decide +kernel

theorem cannot_reuse_another_upper :
    test problem {wire with high := 2} = false := by decide +kernel

theorem checked_lower_direction :
    test problem {wire with lowerBound := .constraint 1} = false := by decide +kernel

theorem checked_outer_target_order :
    test problem wire (fun r => {r with outputRows := r.outputRows.reverse}) = false := by decide +kernel

theorem at_original_demand :
    (read problem wire |>.map (fun b => printDemand b.ctx.demand)) =
    some (printDemand problem.demand) := by decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantIntervalFixture353
