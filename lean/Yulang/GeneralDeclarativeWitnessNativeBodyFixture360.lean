import Yulang.GeneralDeclarativeWitnessNativePreparation360
import Yulang.GeneralDeclarativeWitnessAssociatedFixture359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 52000
set_option maxHeartbeats 48000000
namespace Yulang.GeneralDeclarativeWitnessNativeBodyFixture360
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey slots)
open GeneralDeclarativeWitnessNominalRecordFixture359 (current sourceDecl route)
open GeneralDeclarativeWitnessJointObservation359 (parentScope parentSpan secondSpan)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessCompiler350 (printDemand trip)

def whereClause : Clause := ⟨81,6,[.var 80],[⟨132,0,.var 80⟩]⟩
def original (negative : Bool) : Declaration :=
  {sourceDecl negative with head := [.app 55 [.var 80]], requirements := [whereClause], associated :=
    [⟨111,0,.app 55 [.app (if negative then 42 else 20) [.var 80]]⟩]}

def childDecl : Declaration := ⟨73,6,[.var 90],[],[⟨113,0,.var 90⟩],[]⟩

def input (negative : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨5,1,[(0,none)]⟩,⟨6,1,[(0,none)]⟩]⟩,
    declarations := [original negative,childDecl]}

def request : Demand := ⟨5,[parentSpan],[⟨0,101⟩]⟩
def initial : Layout :=
  ⟨current,[(80,parentSpan)],[61,67,101,105],
    fun _ => ⟨0,0,0⟩,fun _ _ => 105⟩

def body (e : Environment) := prepare e parentScope request initial

def view {e} (prepared : Prepared e parentScope request initial) : Bool :=
  decide (prepared.whereRows = [⟨105,.variable 61⟩]) &&
  (match prepared.kids with
   | [kid] => decide (kid.role = 6 ∧ kid.arguments.map Capture.center = [61] ∧
       kid.outputs.map GeneralSourceState.Output.target = [105])
   | _ => false) &&
  (slots [prepared.captures] parentScope 80).map Capture.center == some 61

theorem genuine_preparation_and_where (negative : Bool) :
    ((input negative).bind fun e => (body e).map view).getD false = true := by
  cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessNativeBodyFixture360
