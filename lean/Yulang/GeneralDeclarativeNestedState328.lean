import Yulang.GeneralDeclarativeNestedDecl328
import Yulang.GeneralDeclarativeOpaqueCapture328
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeNestedState328
open GeneralDeclarativeNestedDecl328
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeOpaqueNested328 (Named run Builds build)
open GeneralDeclarativeOpaquePlan328 (Plan Read)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeOpaqueIntervals328 (Ends)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeGrowth327 (trans facts derives fits)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeTrace321 (Trace)

abbrev lo : Expr := pair (.variable 11) (.variable 12)
abbrev hi : Expr := pair (.variable 13) (.variable 14)
abbrev lowVar : Expr := .variant 4 (.variable 3)
abbrev highVar : Expr := .variant 4 (.variable 4)
abbrev lowNom : Expr := .nominal 0 [.variable 9]
abbrev highNom : Expr := .nominal 0 [.variable 10]
abbrev scalar : Expr := .primitive (.scalar .int) []
abbrev sourceRows : List Equation :=
  [⟨0,lo⟩,⟨2,hi⟩,⟨11,lowVar⟩,⟨13,highVar⟩,⟨12,lowNom⟩,⟨14,highNom⟩,⟨3,scalar⟩]
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,sourceRows⟩
abbrev keep : List Nat := [5,6]
abbrev chosenPlan : Plan :=
  .product ⟨11,13,12,14⟩ (.tagged 4 3 4 (.capture 0)) (.invariant 0 9 10 (.capture 1))
abbrev cooked := run keep initial rootArg chosenPlan
abbrev prepared := cooked.state
abbrev base (n : Nat) := choose (fun _ => ⟨99,99,99⟩) n cooked.binds
abbrev left : Capture := ⟨3,17,4⟩
abbrev right : Capture := ⟨9,9,9⟩
abbrev child : Demand := ⟨2,[left],[⟨1,5⟩]⟩
abbrev childRow : Equation := ⟨5,.variable 17⟩
abbrev rootRow : Equation := ⟨6,.variable 5⟩
abbrev final := appendFacts (appendFacts prepared [rootRow]) [childRow]

theorem exact_binds : cooked.binds = [(0,left),(1,right)] := rfl
theorem first : base 0 = left := rfl
theorem last : base 1 = right := rfl
theorem positive : Read initial 0 2 chosenPlan := by
  refine .product (.row List.mem_cons_self) (.row (List.mem_cons_of_mem _ List.mem_cons_self)) ?_ ?_
  · exact .tagged (.row (by simp [sourceRows])) (.row (by simp [sourceRows])) .capture
  · exact .invariant (.row (by simp [sourceRows])) (.row (by simp [sourceRows])) .capture

theorem original_range : Bounds initial rootArg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
theorem built : Builds initial keep rootArg chosenPlan := build keep chosenPlan rootArg original_range positive
theorem old_projection (m) :
    Models initial m ↔ ∃ n, Models prepared n ∧ ∀ v ∈ stateNames initial ++ keep, n v = m v :=
  GeneralDeclarativeOpaqueConserve328.exact built.modeled m

theorem old_rows {e : Equation} (seen : e ∈ sourceRows) : e ∈ prepared.equations :=
  built.modeled.grows.equations seen

def support0 (done : Nat → Prop) : Supported prepared done :=
  ⟨fun e o => e ∈ sourceRows ∧ o = .source,fun h => old_rows h.1⟩

abbrev support (done : Nat → Prop) := emit (emit (support0 done) 1 [rootRow]) 2 [childRow]

theorem authorized (done : Nat → Prop) {e : Equation} (source : e ∈ sourceRows) :
    e ∈ (restriction (support done)).equations :=
  from_source _ (.inl (.inl ⟨source,rfl⟩))

theorem grow_tail : GeneralDeclarativeGrowth327.Extends prepared final :=
  trans (facts prepared [rootRow]) (facts _ [childRow])

theorem actual_center :
    Derives final (.variable 1) (pair (.variant 4 (.variable 17)) (.nominal 0 [.variable 9])) :=
  derives grow_tail built.center

theorem range_left : Bounds final left :=
  fits grow_tail (built.bounds (0,left) (show (0,left) ∈ cooked.binds from List.mem_cons_self))
theorem range_right : Bounds final right :=
  fits grow_tail (built.bounds (1,right) (show (1,right) ∈ cooked.binds from List.mem_cons_of_mem _ List.mem_cons_self))
theorem range_root : Bounds final rootArg :=
  fits (trans built.modeled.grows grow_tail) original_range

theorem center_absent : ¬∃ code, (⟨1,code⟩ : Equation) ∈ initial.equations := by
  rintro ⟨code,row⟩
  change _ ∈ sourceRows at row
  simp only [sourceRows,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with one|one|one|one|one|one|one <;>
    have problem := congrArg Equation.left one <;> cases problem

end Yulang.GeneralDeclarativeNestedState328
