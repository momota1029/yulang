import Yulang.GeneralDeclarativeWitnessReadout334
import Yulang.GeneralDeclarativeWitnessJournalCase334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
open Yulang
open GeneralDeclarativeWitnessReadout334
open GeneralDeclarativeWitnessJournalCase334
open GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedSiblingsResult332 (current)
open GeneralDeclarativeNestedSiblingsDecl332 (registry impl checked)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedFrame332 (spans fallback)
open GeneralDeclarativeWitnessFixture334 (waiting rootWitness)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeDemand320 (Demand)

example (done : Nat → Prop) :
    Rule (current done) registry interpretation waiting root (.selected impl.id childList) := by
  let w := rootWitness done
  exact selected_from_replay w.chosen w.slice w.source
    ((replay_exact (r := registry) (i := interpretation) (d := root) (impl := impl)
      (named := stage) (spans := spans) (protect := keep) (fallback := fallback)
      (targets := targets) (key := impl.id) (kids := childList) (ordinary := parent)).mpr
      ⟨rfl,exact_order_writes.1⟩) w.receipt

example : replay registry interpretation root impl stage spans keep fallback targets impl.id
    [second,first] = none := rfl

example : replay registry interpretation root impl stage spans keep fallback targets impl.id
    [first,⟨2,[captureTwo],[⟨1,5⟩]⟩] = none := rfl

example : replay registry interpretation root impl stage spans keep fallback targets impl.id
    [first, ⟨2, [⟨20,3,21⟩], [⟨1,10⟩]⟩] = none := rfl

example : replay registry interpretation root impl stage spans keep fallback targets (impl.id+1)
    childList = none := rfl

#print axioms Yulang.GeneralDeclarativeWitnessReadout334.replay_exact
#print axioms Yulang.GeneralDeclarativeWitnessReadout334.selected_from_replay
#print axioms Yulang.GeneralDeclarativeWitnessReadout334.chosen_declaration
#print axioms Yulang.GeneralDeclarativeWitnessReadout334.chosen_key
