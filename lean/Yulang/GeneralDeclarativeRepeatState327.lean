import Yulang.GeneralDeclarativeRepeatDecl327
import Yulang.GeneralDeclarativeRepeatedHead327
import Yulang.GeneralDeclarativeFreshInputs325

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativePairCenters326 (pair project_first)
open GeneralDeclarativePairNames326 (Span first second)
open GeneralDeclarativeProjectInterval326 (projectAll)
open GeneralDeclarativeRepeatedProjection327 (mergeState merged merge_from_source)
open GeneralDeclarativeRepeatedHead327 (original_grows)
open GeneralDeclarativeGrowth327 (Extends trans ordinary span facts fits derives restrict)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeFreshInputs325 (prepared names_observed names_bounded whole_input_projection)
open GeneralDeclarativeFreshWhere325 (seed)
open GeneralDeclarativeSparseWhere325 (plan atPosition bodies)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeNewNames321 (supply)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationExamples (itemEquation)

abbrev low : Expr := pair (.variable 3) (.variable 9)
abbrev high : Expr := pair (.variable 4) (.variable 10)
abbrev mid : Expr := pair (.variable 7) (.variable 7)
abbrev presentRows : List Equation :=
  [⟨0,low⟩,⟨2,high⟩,⟨11,pair (.variable 1) (.variable 3)⟩,⟨11,pair mid (.variable 3)⟩]
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,presentRows⟩
abbrev protect : List Nat := [5,6]
abbrev leftView : Span := ⟨.variable 3,.variable 7,.variable 4⟩
abbrev rightView : Span := ⟨.variable 9,.variable 7,.variable 10⟩
abbrev combined := merged initial protect leftView rightView
abbrev mergedState := mergeState initial protect leftView rightView
abbrev base (_ : Nat) : Capture := combined
abbrev jobs := plan clause.arguments [compoundCode]
abbrev argC := atPosition (seed mergedState protect base jobs) jobs 0
abbrev child : Demand := ⟨2,[argC],[⟨1,5⟩]⟩
abbrev place : Placement := ⟨fun _ _ => argC,fun cl eq => if cl.id = clause.id ∧ eq = itemEquation.id then 5 else 99⟩
abbrev clausesState := prepared mergedState protect base jobs
abbrev inputRows := supply mergedState protect (bodies base jobs)
abbrev rootRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable argC.center⟩
abbrev result := appendFacts (appendFacts clausesState [rootRow]) [childRow]

theorem root_bounds : Bounds initial arg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem lower : Derives initial (.variable 0) low := .row List.mem_cons_self
theorem upper : Derives initial (.variable 2) high := .row (by simp [presentRows])
theorem shared_root : Derives initial (.variable 1) mid :=
  project_first (host := 11) (spare := .variable 3) (second := .variable 3)
    (.row (by simp [presentRows])) (.row (by simp [presentRows]))

theorem exactly_views : projectAll low mid high = some (leftView,rightView) := rfl
abbrev aggregate := (merge_from_source root_bounds lower shared_root upper exactly_views protect shared_root)
theorem named : combined = ⟨18,13,19⟩ := rfl
theorem child_named : argC = ⟨20,21,22⟩ := rfl
theorem emitted : children impl (sourceNames impl place base) place = [child] := rfl
theorem input_exact : inputRows = [⟨20,.nominal 0 [.variable 13]⟩,
    ⟨21,.nominal 0 [.variable 13]⟩,⟨22,.nominal 0 [.variable 13]⟩] := rfl

end Yulang.GeneralDeclarativeRepeatState327
