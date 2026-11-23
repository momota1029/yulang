import Yulang.GeneralDeclarativeWitnessNestedLeaf361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 63000
set_option maxHeartbeats 61000000
namespace Yulang.GeneralDeclarativeWitnessNestedFixture361
open GeneralDeclarativeWitnessNestedLeaf361 (Choice FinishedNested elect compile)
open GeneralDeclarativeWitnessNativePortTransport361 (Port transport)
open GeneralDeclarativeWitnessNativeDirectSource361 (actualWire)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run written requested layout)
open GeneralDeclarativeWitnessNativeBodyFixture360 (childDecl)
open GeneralDeclarativeWitnessReleasedForward360 (forward)
open GeneralDeclarativeWitnessNativePipeline360 (authority gate wire)
open GeneralDeclarativeWitnessNativePreparation360 (prepare)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessJointObservation359 (parentScope)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit)
open GeneralDeclarativeWitnessNativeReceiver360 (key)
open GeneralDeclarativeWitnessScopedBindings359 (slots)
open GeneralDeclarativeWitnessCompiler350 (trip printDemand)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)

def nestedHead (negative : Bool) : Pattern :=
  .app 55 [.app (if negative then 42 else 20) [.var 92]]

def receiver (negative swapped : Bool) : Declaration :=
  ⟨75,8,[nestedHead (if swapped then !negative else negative)],[],[],[]⟩

def input (negative swapped : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨5,2,[(0,none)]⟩,⟨6,1,[(0,none)]⟩,⟨7,2,[]⟩,⟨8,1,[]⟩]⟩,
    declarations := [written negative,childDecl,forward,receiver negative swapped]}

def start (negative swapped : Bool) : Option (Run negative) := do
  let env ← input negative swapped
  let p ← prepare env parentScope requested layout
  let compiled ← GeneralDeclarativeWitnessNativeValue360.compile p table (wire negative) 3
  match saved : commit p compiled ⟨layout.named,gate⟩ with
  | none => none
  | some final => some ⟨env,p,compiled,final,saved⟩

structure CheckedLeaf {negative : Bool} {r : Run negative} (s : Sequence r) where
  origin : Port s authority actualWire
  chosen : Choice origin
  result : FinishedNested chosen

def close {negative} {r : Run negative} (s : Sequence r) : Option (CheckedLeaf s) := do
  let origin ← transport s authority actualWire
  let chosen ← elect origin
  let result ← compile chosen
  pure ⟨origin,chosen,result⟩

def full {negative r} (s : @Sequence negative r) (n : CheckedLeaf s) : Bool :=
  decide (printDemand s.receiver = (8,[(112,101,113)],[]) ∧ n.chosen.impl.id = 75 ∧
    n.chosen.pattern = nestedHead negative) &&
  ((n.chosen.captures.map fun x => (x.1,trip x.2)) == [(92,(106,61,107))]) &&
  ((slots [n.result.prep.captures] key 92).map trip == some (116,61,117))

theorem actual_nested_binder_does_not_use_nominal_address (negative : Bool) :
    ((start negative false).bind fun r => (sequence r).bind fun s =>
      (close s).map (full s)).getD false = true := by
  cases negative <;> decide +kernel

def swappedControl {negative r} (s : @Sequence negative r) : Bool :=
  ((transport s authority actualWire).map fun p => (elect p).isNone).getD false

theorem matching_port_and_release_do_not_select_other_constructor (negative : Bool) :
    ((start negative true).bind fun r => (sequence r).map swappedControl).getD false = true := by
  cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessNestedFixture361
