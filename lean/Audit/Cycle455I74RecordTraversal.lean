import Yulang.GeneralDeclarativeI65I74RecordTraversal455

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.QA
open GeneralNominalCenteredHeadMatExpressions (Expr)
open List410 (ExactEscapeWire)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RecordK2412 (FieldCycleWire)

def empty : Expr := .primitive .emptyRecord []
def outer : Expr := .record 10 (.variable 1) (.record 90 (.variable 9) (.record 10 (.variable 8) empty))
def raw : RawSnapshot :=
  ⟨⟨[],[]⟩,[⟨0,outer⟩,⟨1,.variable 11⟩,
    ⟨11,.record 20 (.variable 2) empty⟩,⟨2,.record 30 (.variable 3) empty⟩,
    ⟨3,.nominal 100 [.variable 3]⟩,⟨9,.nominal 100 [.variable 9]⟩,
    ⟨8,.nominal 100 [.variable 8]⟩]⟩

def ledger (middle : Bool) : OpenOps where
  Token := Unit
  allowed := fun _ row => row.left = 0 ∨ row.left = 2 ∨ (middle = true ∧ row.left = 11)
  check := fun _ row _ => (row.left == 0) || (row.left == 2) || (middle && row.left == 11)
  exactCheck := by
    intro root row
    simp [Bool.or_eq_true,Bool.and_eq_true,or_assoc]

def candidate : Expr :=
  .record 10 (.record 20 (.record 30 (.nominal 100 [.variable 31]) empty) empty)
    (.record 10 (.nominal 100 [.variable 32]) empty)

def variableLeaf : Expr :=
  .record 10 (.record 20 (.record 30 (.variable 31) empty) empty) empty

def c0 : ExactEscapeWire := ⟨List.range 12,[0,1,1,1,2,2,2,2,2,1,2,1]⟩
def c1 : ExactEscapeWire := ⟨List.range 12,[2,0,1,1,2,2,2,2,2,2,2,0]⟩
def c2 : ExactEscapeWire := ⟨List.range 12,[2,2,0,1,2,2,2,2,2,2,2,2]⟩
def finalCycle : FieldCycleWire := ⟨⟨4,.same,3⟩,[],.same⟩
def hiddenCycle : FieldCycleWire := ⟨⟨5,.same,9⟩,[],.same⟩
def walk (m : Bool) : TrailWire (ledger m) :=
  .down ⟨0,.same,0,0,()⟩ c0
    (.down ⟨2,.forward 1,0,0,()⟩ c1
      (.down ⟨3,.same,0,0,()⟩ c2 .stop))
def wrongAlias : TrailWire (ledger true) :=
  .down ⟨0,.same,0,0,()⟩ c0
    (.down ⟨2,.same,0,0,()⟩ c1
      (.down ⟨3,.same,0,0,()⟩ c2 .stop))
def otherField : TrailWire (ledger true) :=
  .down ⟨0,.same,1,0,()⟩ c0 .stop
def duplicateField : TrailWire (ledger true) :=
  .down ⟨0,.same,2,1,()⟩ c0 .stop
def earlierRaw : RawSnapshot :=
  {raw with equations := raw.equations ++ [⟨1,.nominal 100 [.variable 1]⟩]}
def earlyTrail : TrailWire (ledger true) := .down ⟨0,.same,0,0,()⟩ c0 .stop
def earlyCycle : FieldCycleWire := ⟨⟨7,.same,1⟩,[],.same⟩

/-- info: [some ([(10, 1), (20, 2), (30, 3)], 3), none, none, none, none, none, none, some ([(10, 1)], 1), none] -/
#guard_msgs in
#eval [readCycleVisit raw (ledger true) 0 candidate ⟨walk true,finalCycle⟩,
  readCycleVisit raw (ledger false) 0 candidate ⟨walk false,finalCycle⟩,
  readCycleVisit raw (ledger true) 0 candidate ⟨wrongAlias,finalCycle⟩,
  readCycleVisit raw (ledger true) 0 candidate ⟨otherField,hiddenCycle⟩,
  readCycleVisit raw (ledger true) 0 candidate ⟨duplicateField,hiddenCycle⟩,
  readCycleVisit raw (ledger true) 0 variableLeaf ⟨walk true,finalCycle⟩,
  readCycleVisit earlierRaw (ledger true) 0 candidate ⟨walk true,finalCycle⟩,
  readCycleVisit earlierRaw (ledger true) 0 candidate ⟨earlyTrail,earlyCycle⟩,
  readCycleVisit raw (ledger true) 9 (.nominal 100 [.variable 31]) ⟨.stop,hiddenCycle⟩]

theorem actual_deep_alias_route_and_unopened_terminal455 :
    ExactCycleVisit raw (ledger true) 0 candidate [(10,1),(20,2),(30,3)] 3 ∧
    ¬(ledger true).allowed 3 ⟨3,.nominal 100 [.variable 3]⟩ ∧
    AliasCycle raw (observed raw) 9 := by
  refine ⟨read_cycle_visit_sound455 (w := ⟨walk true,finalCycle⟩) (by decide +kernel),?_,?_⟩
  · simp [ledger]
  · exact RecordK2412.cycle_at_sound412 (w := hiddenCycle) (by decide +kernel)

#print axioms step_projects_original_visit455
#print axioms read_step_sound455
#print axioms step_has_finite_wire455
#print axioms read_trail_exact455
#print axioms exact_cycle_visit_iff_finite_wire455
#print axioms exact_cycle_visit_is_safe_at_root_and_real_at_site455
#print axioms actual_deep_alias_route_and_unopened_terminal455

end Yulang.GeneralDeclarativeI65.I72.RecordTraversal455.QA
