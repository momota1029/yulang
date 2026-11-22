import Yulang.GeneralDeclarativeWitnessFreshness351
import Yulang.GeneralDeclarativeWitnessAuthModel351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeWitnessFreshFixture351
open GeneralDeclarativeWitnessIdentity351 (Stamp)
open GeneralDeclarativeWitnessAuthForest351 (Problem)
open GeneralDeclarativeWitnessAuthFixture351 (setup problem state answer)
open GeneralDeclarativeWitnessWriterFixture351 (stamp key)
open GeneralDeclarativeWitnessFreshness351 (check)

def fresh (active : List Stamp) (change : Problem → Problem := id) : Bool :=
  (setup.map (fun (f,w) => check active (change (problem (state f) [key])) w answer)).getD false

theorem actually_fresh : fresh [stamp] = true := by decide +kernel

theorem stale_independent_stamp :
    fresh [{stamp with version := 8}] = false := by decide +kernel

theorem no_two_active_versions :
    fresh [stamp,{stamp with version := 8}] = false := by decide +kernel

theorem no_unidentified_required_version :
    fresh [stamp] (fun p => {p with writer :=
      {p.writer with required := [⟨{stamp with version := 8},0⟩]}}) = false := by
  decide +kernel

theorem no_replay_of_historic_releases :
    fresh [{stamp with version := 8}] (fun p => {p with writer :=
      {p.writer with required := [⟨{stamp with version := 8},0⟩]}}) = false := by
  decide +kernel

def bump (p : Problem) : Problem :=
  let owner := {p.writer with required := [⟨{stamp with version := 8},0⟩]}
  {p with writer := {owner with releases := [{key with version := 8}]}}

theorem another_current_version_with_matching_release :
    fresh [{stamp with version := 8}] bump = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessFreshFixture351
