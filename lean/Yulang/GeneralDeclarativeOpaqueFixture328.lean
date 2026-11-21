import Yulang.GeneralDeclarativeOpaqueIntervals328
import Yulang.GeneralDeclarativePairDecl326
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueFixture328
open GeneralDeclarativePairDecl326 (rootArg root impl reg interpret)
open GeneralDeclarationExamples (containerChild)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOpaqueIntervals328 (Ends low high left right ready preserved actual)
open GeneralDeclarativeOpaqueNames328 (kept)
open GeneralDeclarativeEntailment320 (Entails literal appendFacts model_append)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeGrowth327 (Extends trans facts fits derives)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEqualities322 (Derives)

abbrev endpoints : Ends := ⟨3,4,3,4⟩
abbrev keep : List Nat := [5,6]
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev oldRows : List Equation := [⟨0,low endpoints⟩,⟨2,high endpoints⟩,scalar]
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,oldRows⟩
abbrev leftCapture := left initial 1 keep endpoints
abbrev rightCapture := right initial 1 keep endpoints
abbrev prepared := ready initial 1 keep endpoints
abbrev child : Demand := ⟨2,[leftCapture],[⟨1,5⟩]⟩
abbrev parentRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable leftCapture.center⟩
abbrev final := appendFacts (appendFacts prepared [parentRow]) [childRow]

theorem left_exact : leftCapture = ⟨3,7,4⟩ := rfl
theorem right_exact : rightCapture = ⟨3,8,4⟩ := rfl
theorem root_range : Bounds initial rootArg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
theorem lo : Entails initial ⟨0,low endpoints⟩ := literal List.mem_cons_self
theorem hi : Entails initial ⟨2,high endpoints⟩ := literal (List.mem_cons_of_mem _ List.mem_cons_self)

theorem roots_exist (m) :
    Models initial m ↔ ∃ n, Models prepared n ∧
      ∀ key ∈ kept initial rootArg.center (GeneralDeclarativeOpaqueIntervals328.protect keep endpoints), n key = m key :=
  preserved root_range lo hi keep m

theorem no_old_center : ¬ ∃ exp, (⟨1,exp⟩ : Equation) ∈ initial.equations := by
  rintro ⟨exp,there⟩
  change ⟨1,exp⟩ ∈ oldRows at there
  simp only [oldRows,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with equal|equal|equal <;> have impossible := congrArg Equation.left equal <;> cases impossible

theorem older {eq : Equation} (old : eq ∈ oldRows) : eq ∈ prepared.equations :=
  List.mem_append_left _ old

def support0 (done : Nat → Prop) : Supported prepared done :=
  ⟨fun row origin => row ∈ oldRows ∧ origin = .source,fun yes => older yes.1⟩

abbrev support (done : Nat → Prop) := emit (emit (support0 done) 1 [parentRow]) 2 [childRow]

theorem authorized (done : Nat → Prop) {eq : Equation} (original : eq ∈ oldRows) :
    eq ∈ (restriction (support done)).equations :=
  from_source _ (.inl (.inl ⟨original,rfl⟩))

theorem actual_center : Derives final (.variable 1)
    (GeneralDeclarativePairCenters326.pair (.variable 7) (.variable 8)) :=
  derives (trans (facts prepared [parentRow]) (facts _ [childRow])) (actual 1 keep endpoints)

theorem range_left : Bounds final leftCapture :=
  fits (trans (facts prepared [parentRow]) (facts _ [childRow]))
    (GeneralDeclarativeOpaqueIntervals328.bounds (s := initial) 1 keep endpoints).1
theorem range_right : Bounds final rightCapture :=
  fits (trans (facts prepared [parentRow]) (facts _ [childRow]))
    (GeneralDeclarativeOpaqueIntervals328.bounds (s := initial) 1 keep endpoints).2
theorem range_root : Bounds final rootArg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

end Yulang.GeneralDeclarativeOpaqueFixture328
