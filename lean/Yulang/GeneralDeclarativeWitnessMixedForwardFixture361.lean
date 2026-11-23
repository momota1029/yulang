import Yulang.GeneralDeclarativeWitnessMixedForwardChoice361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 64000
set_option maxHeartbeats 67000000
namespace Yulang.GeneralDeclarativeWitnessMixedForwardFixture361
open GeneralDeclarativeWitnessMixedForwardChoice361 (aligned Choice pick checkOrdinary)
open GeneralDeclarativeWitnessNestedFixture361 (receiver CheckedLeaf close full)
open GeneralDeclarativeWitnessNestedInstall360 (Run written requested layout)
open GeneralDeclarativeWitnessNativeBodyFixture360 (childDecl)
open GeneralDeclarativeWitnessNativePreparation360 (prepare)
open GeneralDeclarativeWitnessNativePipeline360 (gate wire)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit same)
open GeneralDeclarativeWitnessNestedModel361 (state)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody forward)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessJointObservation359 (parentScope)

def input (negative : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨5,2,[(0,none)]⟩,⟨6,1,[(0,none)]⟩,⟨7,2,[]⟩,⟨8,1,[]⟩]⟩,
    declarations := [written negative,childDecl,aligned,receiver negative false]}

def start (negative : Bool) : Option (Run negative) := do
  let env ← input negative
  let p ← prepare env parentScope requested layout
  let result ← GeneralDeclarativeWitnessNativeValue360.compile p table (wire negative) 3
  match saved : commit p result ⟨layout.named,gate⟩ with
  | none => none
  | some final => some ⟨env,p,result,final,saved⟩

structure PairOfNodes {negative : Bool} {r : Run negative} (s : Sequence r) where
  parent : Choice r s.ordinaryChild.final
  leaf : CheckedLeaf s

def run {negative} {r : Run negative} (s : Sequence r) : Option (PairOfNodes s) := do
  let chosen ← pick r s.ordinaryChild.final
  let leaf ← close s
  pure ⟨chosen,leaf⟩

def verify {negative r s} (p : @PairOfNodes negative r s) : Bool :=
  (decide (p.parent.impl.id = 74 ∧ p.leaf.chosen.impl.id = 75) &&
    full s p.leaf) && same p.leaf.result.world.ordinary state

theorem actual_aligned_two_nodes (negative : Bool) :
    ((start negative).bind fun r => (sequence r).bind fun s =>
      (run s).map verify).getD false = true := by
  cases negative <;> decide +kernel

def forcedReplayScope {negative r} (s : @Sequence negative r) : Bool :=
  decide (s.continuation.impl = forward &&
    s.continuation.impl.head[1]? = some (.app 55 [.var 91])) &&
  checkOrdinary s.ordinaryChild.final.ordinary &&
  (pick r s.ordinaryChild.final).isNone

theorem previous_preparation_was_not_this_parent_choice (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).map forcedReplayScope).getD false = true := by
  cases negative <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessMixedForwardFixture361
