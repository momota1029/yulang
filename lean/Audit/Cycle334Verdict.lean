import Yulang.GeneralDeclarativeWitnessVerdict334
import Yulang.GeneralDeclarativeWitnessCompletion334

open Yulang
open GeneralDeclarativeWitnessVerdict334
open GeneralDeclarativeWitnessCompletion334 (view actually_pending_before exactly_completed)
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeWitnessCut334 (waiting)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeNestedExample332 (interpretation)

example {done : Nat → Prop} (missing : ¬done 100)
    (seen : Rule (view done) registry interpretation waiting root outcome) :
    outcome = .pending := by
  have matchType := verdict_functional checked seen (actually_pending_before missing)
  cases outcome <;> cases matchType <;> rfl

example {done : Nat → Prop} (known : done 100)
    (seen : Rule (view done) registry interpretation waiting root outcome) :
    ∃ kids, outcome = .selected impl.id kids := by
  have matchType := verdict_functional checked seen ((exactly_completed done).mpr known)
  cases outcome <;> cases matchType
  exact ⟨_,rfl⟩

#print axioms Yulang.GeneralDeclarativeWitnessVerdict334.verdict_functional
#print axioms Yulang.GeneralDeclarativeWitnessVerdict334.only_lists_can_differ
