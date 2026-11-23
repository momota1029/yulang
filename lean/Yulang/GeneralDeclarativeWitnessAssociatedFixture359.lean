import Yulang.GeneralDeclarativeWitnessAssociatedBatch359
import Yulang.GeneralDeclarativeWitnessJointObservation359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeWitnessAssociatedFixture359
open GeneralDeclarativeWitnessAssociatedDescriptor359 (Wire describe)
open GeneralDeclarativeWitnessAssociatedBatch359 (verify accepted_exact_order same_fixed_target_order)
open GeneralDeclarativeWitnessJointObservation359 (parentScope parentSpan secondSpan)
open GeneralDeclarativeWitnessScopedBindings359 (Frame)
open GeneralDeclarativeWitnessNominalRecordFixture359 (sourceDecl route)
open GeneralDeclarativeWitnessCoverageFixture357 (prepare bundle)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)

def authored (negative : Bool) : Declaration :=
  {sourceDecl negative with associated := [
    ⟨111,0,.app 55 [.app (if negative then 42 else 20) [.var 80]]⟩,
    ⟨112,1,.app 55 [.app (if negative then 42 else 20) [.var 81]]⟩]}

def available (negative : Bool) : Option Environment :=
  prepare {bundle with roles := ⟨0,[⟨5,2,[(0,none),(1,none)]⟩]⟩,declarations := [authored negative]}

def frames : List Frame := [⟨parentScope,[(80,parentSpan),(81,secondSpan)]⟩]
def request : Demand := ⟨5,[parentSpan,secondSpan],[⟨0,101⟩,⟨1,102⟩]⟩

def wires (negative : Bool) : List Wire :=
  [⟨0,111,101,route negative 80⟩,⟨1,112,102,route negative 81⟩]

def checks (negative : Bool) (change : List Wire → List Wire := id) : Bool :=
  ((available negative).map fun e => verify e table frames parentScope request (change (wires negative))).getD false

theorem checked_written_nominal_output_descriptors (negative : Bool) :
    checks negative = true := by cases negative <;> decide +kernel

theorem rejects_swapped_descriptor_order (negative : Bool) :
    checks negative List.reverse = false := by cases negative <;> decide +kernel

theorem rejects_fixed_target_change (negative : Bool) :
    checks negative (List.modify · 0 (fun row => {row with target := 102})) = false := by
  cases negative <;> decide +kernel

theorem rejects_wrong_exact_author_id (negative : Bool) :
    checks negative (List.modify · 0 (fun row => {row with sourceEquation := 112})) = false := by
  cases negative <;> decide +kernel

theorem rejects_different_source_capture (negative : Bool) :
    checks negative (List.modify · 0 (fun row => {row with route := route negative 81})) = false := by
  cases negative <;> decide +kernel

theorem actual_complete_descriptor_addresses (negative : Bool) :
    ∃ e,available negative = some e ∧
      GeneralDeclarativeWitnessAssociatedBatch359.Ordered e table frames parentScope request (wires negative) ∧
      (wires negative).map Wire.target = [101,102] := by
  have yes := checked_written_nominal_output_descriptors negative
  unfold checks at yes
  cases active : available negative with
  | none => rw [active] at yes; cases yes
  | some e =>
    rw [active] at yes
    have ordered := accepted_exact_order (show verify e table frames parentScope request (wires negative) = true from yes)
    exact ⟨e,rfl,ordered,same_fixed_target_order ordered⟩

end Yulang.GeneralDeclarativeWitnessAssociatedFixture359
