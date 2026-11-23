import Yulang.GeneralDeclarativeWitnessNestedModels360
import Yulang.GeneralDeclarativeWitnessOrderedChild360

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 57000
set_option maxHeartbeats 54000000
namespace Yulang.GeneralDeclarativeWitnessReleasedObservation360
open GeneralDeclarativeWitnessNativeValue360 (Code Value Write)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews interpreted atTarget)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease checked_exact_written_value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)

def sourceSlot : Code → List Nat → Option Nat
  | .leaf n,[] => some n
  | .unary key ch,step::more => if key = step then sourceSlot ch more else none
  | _,_ => none

def observe : Value → List Nat → Option Ty
  | .leaf value,[] => some value
  | .unary key ch,step::more => if key = step then observe ch more else none
  | _,_ => none

theorem exact_navigated_source (m : Assignment) (code : Code) (path : List Nat) :
    observe (code.eval m) path = (sourceSlot code path).map (fun n => (m n).1) := by
  induction code generalizing path with
  | leaf n => cases path <;> rfl
  | nullary n => cases path <;> rfl
  | unary key ch ih =>
    cases path with
    | nil => rfl
    | cons step more =>
      by_cases matched : key = step
      · simp [observe,Code.eval,sourceSlot,matched,ih]
      · simp [observe,Code.eval,sourceSlot,matched]

/-- Observation in one current native view, after real readback of
the exact write and grant. No comparison can produce this read on its own. -/
theorem from_actual_release {world : World} {gate written} (read : ExactRelease world.board gate written)
    (m : Assignment) (v : NativeViews) (fit : Fits world m v) (path : List Nat) :
    (v written.address.target).bind (fun value => observe value path) =
      (sourceSlot written.code path).map (fun n => (m n).1) := by
  rw [checked_exact_written_value read m v fit]
  exact exact_navigated_source m written.code path

open GeneralDeclarativeWitnessNestedInstall360 (Run native checks unchanged_two_nested_heads_install)
open GeneralDeclarativeWitnessNestedModels360
  (authored_nested_value_in_every_fitting_model actual_nested_has_native_model commonModel)
open GeneralDeclarativeWitnessNativePipeline360 (valueCode)
open GeneralDeclarativeWitnessNominalRecordFixture359 (ctor)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeWhere319 (Capture)

def actualRead (negative : Bool) := [55,ctor negative]

theorem actual_nested_payload_is_original_center {negative} {r : Run negative}
    (run : native negative = some r) (m : Assignment) (v : NativeViews) (fit : Fits r.final m v) :
    (v 101).bind (fun result => observe result (actualRead negative)) = some (m 61).1 ∧
    (v 101).bind (fun result => observe result (actualRead (!negative))) = none := by
  rw [authored_nested_value_in_every_fitting_model run m v fit]
  cases negative <;> constructor <;> rfl

/-- This actual compiled child does not address the new native output.
It reads the original physical argument interval instead. In particular
neither the child nor its ordinary output can be used to claim typed uptake. -/
def noNativeUptake {negative} (r : Run negative) : Bool :=
  r.prep.kids.all fun child =>
    (child.arguments.all fun sp => decide (sp.lower ≠ 101 ∧ sp.center ≠ 101 ∧ sp.upper ≠ 101)) &&
    (child.outputs.all fun out => decide (out.target ≠ 101))

theorem ordered_child_has_no_native_target (negative : Bool) :
    ((native negative).map noNativeUptake).getD false = true := by cases negative <;> decide +kernel

theorem exact_missing_child_reference {negative} {r : Run negative}
    (actual : native negative = some r) {kid} (emitted : kid ∈ r.prep.kids) :
    (∀ sp ∈ kid.arguments,sp.lower ≠ 101 ∧ sp.center ≠ 101 ∧ sp.upper ≠ 101) ∧
    (∀ out ∈ kid.outputs,out.target ≠ 101) := by
  have ran := ordered_child_has_no_native_target negative
  rw [actual] at ran
  have test : noNativeUptake r = true := ran
  have relevant := GeneralDeclarativeWitnessProblem349.splitAnd (List.all_eq_true.mp test kid emitted)
  exact ⟨fun sp h => of_decide_eq_true (List.all_eq_true.mp relevant.1 sp h),
    fun out h => of_decide_eq_true (List.all_eq_true.mp relevant.2 out h)⟩

end Yulang.GeneralDeclarativeWitnessReleasedObservation360
