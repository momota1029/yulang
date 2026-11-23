import Yulang.GeneralDeclarativeWitnessSiblingFixture358
import Yulang.GeneralDeclarativeWitnessSourceChain358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 92000000
namespace Yulang.GeneralDeclarativeWitnessSiblingLinks358
open GeneralDeclarativeWitnessSiblingSeed358 (Data data firstLayout laterLayout)
open GeneralDeclarativeWitnessRecursiveSeed358 (author recipe)
open GeneralDeclarativeWitnessJoinedFixture357 (root written)
open GeneralDeclarativeWitnessJoinedCheck357 (Answer replay)
open GeneralDeclarativeWitnessProjectionCheck358 (Certificate)
open GeneralDeclarativeWitnessSourceChain358 (Edge check exact)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def leftRecipe (d : Data) :=
  {recipe with outer := d.left.arguments.headD recipe.outer}

def rightRecipe (d : Data) :=
  {recipe with outer := d.right.arguments.headD recipe.outer}

def observed (d : Data) (leftBinder rightBinder : Nat := 32) : Bool :=
  ((replay d.current root written firstLayout d.parentWire).map fun p =>
    ((GeneralDeclarativeWitnessProjectionCheck358.replay author d.current d.left
      (leftRecipe d) 33 (laterLayout d.first) d.leftWire).map fun l =>
        ((GeneralDeclarativeWitnessProjectionCheck358.replay author d.current d.right
          (rightRecipe d) 34 (laterLayout d.second) d.rightWire).map fun r =>
            check p l 0 81 leftBinder && check p r 1 83 rightBinder).getD false).getD false).getD false

def parentExpected (target : Nat) : Equation := ⟨target,.variable 10⟩
def returned (target : Nat) : Equation := ⟨target,.variant 7 (.variable 4)⟩

def relative (d : Data) : Bool :=
  decide (parentExpected 41 ∈ d.first.beforeOutputs.equations ∧
    parentExpected 42 ∈ d.first.beforeOutputs.equations ∧
    d.leftWire.outputRows = [returned 41] ∧ d.rightWire.outputRows = [returned 42] ∧
    ∀ e ∈ [parentExpected 41,parentExpected 42,returned 41,returned 42],
      e ∈ d.current.ordinary.equations)

theorem independently_checked_edges :
    (data.map fun d => observed d 32 31 && relative d).getD false = true := by decide +kernel

theorem not_replace_binders_because_values_equal :
    (data.map fun d => observed d 31 32).getD false = false := by decide +kernel

theorem all_actual_where_outputs {d : Data} (live : data = some d)
    (m : Assignment) (fit : Models d.current.ordinary m) :
    ∃ (p : Answer d.current root d.parentWire)
      (left : Certificate author d.current d.left d.leftWire)
      (right : Certificate author d.current d.right d.rightWire),
      Edge p left 0 81 32 ∧ Edge p right 1 83 31 ∧
      parentExpected 41 ∈ d.first.beforeOutputs.equations ∧
      parentExpected 42 ∈ d.first.beforeOutputs.equations ∧
      d.leftWire.outputRows = [returned 41] ∧ d.rightWire.outputRows = [returned 42] ∧
      ∀ e ∈ [parentExpected 41,parentExpected 42,returned 41,returned 42],Holds m e := by
  have tested := independently_checked_edges
  rw [live] at tested
  obtain ⟨seen,rows⟩ := splitAnd (show (observed d 32 31 && relative d) = true from tested)
  unfold observed at seen
  cases recorded : replay d.current root written firstLayout d.parentWire with
  | none => rw [recorded] at seen; cases seen
  | some p =>
    rw [recorded] at seen
    cases leftRun : GeneralDeclarativeWitnessProjectionCheck358.replay author d.current d.left
        (leftRecipe d) 33 (laterLayout d.first) d.leftWire with
    | none => simp [leftRun] at seen
    | some left =>
      cases rightRun : GeneralDeclarativeWitnessProjectionCheck358.replay author d.current d.right
          (rightRecipe d) 34 (laterLayout d.second) d.rightWire with
      | none => simp [leftRun,rightRun] at seen
      | some right =>
        have both : (check p left 0 81 32 && check p right 1 83 31) = true := by
          simpa only [leftRun,rightRun,Option.map_some,Option.getD_some] using seen
        have leftEdge := exact (splitAnd both).1
        have rightEdge := exact (splitAnd both).2
        obtain ⟨a,b,l,r,hold⟩ := of_decide_eq_true rows
        exact ⟨p,left,right,leftEdge,rightEdge,a,b,l,r,fun e h => fit.2 e (hold e h)⟩

end Yulang.GeneralDeclarativeWitnessSiblingLinks358
