import Yulang.GeneralRebaseNormalizedBody263
import Yulang.GeneralRebaseNormalizedFacts263
import Yulang.GeneralRebaseHeadSupport263
import Yulang.GeneralRebaseOwnerTags263
import Yulang.GeneralRebaseOwnerTable263
import Yulang.GeneralRebaseMultiSelection263
import Yulang.GeneralRebaseMultiObserver263
import Yulang.GeneralRebaseValidatedDriver263
import Yulang.GeneralRebaseValidatedOutcome263
import Yulang.GeneralRebaseMultiRun263
import Yulang.GeneralRebaseRegisteredOwners263
import Yulang.GeneralRebaseMultiTrace263
import Yulang.GeneralRebaseMultiSource263
import Yulang.GeneralRebaseNormalizedExamples263
import Yulang.GeneralRebaseRegisteredPlan263
import Yulang.GeneralRebaseRegisteredSites263
import Yulang.GeneralRebaseSourceCenters263
import Yulang.GeneralRebaseUniversalBasis263
import Yulang.GeneralRebaseUniversalObserver263
import Yulang.GeneralRebaseUniversalSource263
import Yulang.GeneralRebaseTwoOwnerRegression263
import Yulang.GeneralRebaseUniversalMeaning263
import Yulang.GeneralRebaseUniversalTrace263
import Yulang.GeneralRebaseUniversalRegression263
import Yulang.GeneralRebaseSourceRepresentatives263
import Yulang.GeneralRebaseRepresentativesExample263
import Yulang.GeneralRebaseSourceMeaning263
import Yulang.GeneralRebaseSourceLocalHeads263
import Yulang.GeneralRebaseSourceLocalMeaning263
import Yulang.GeneralRebaseFiniteStates263
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralRebaseNormalizedBody263.", "Yulang.GeneralRebaseNormalizedFacts263.", "Yulang.GeneralRebaseHeadSupport263.", "Yulang.GeneralRebaseOwnerTags263.", "Yulang.GeneralRebaseOwnerTable263.", "Yulang.GeneralRebaseMultiSelection263.", "Yulang.GeneralRebaseMultiObserver263.", "Yulang.GeneralRebaseValidatedDriver263.", "Yulang.GeneralRebaseValidatedOutcome263.", "Yulang.GeneralRebaseMultiRun263.", "Yulang.GeneralRebaseRegisteredOwners263.", "Yulang.GeneralRebaseMultiTrace263.", "Yulang.GeneralRebaseMultiSource263.", "Yulang.GeneralRebaseNormalizedExamples263.", "Yulang.GeneralRebaseRegisteredPlan263.", "Yulang.GeneralRebaseRegisteredSites263.", "Yulang.GeneralRebaseSourceCenters263.", "Yulang.GeneralRebaseUniversalBasis263.", "Yulang.GeneralRebaseUniversalObserver263.", "Yulang.GeneralRebaseUniversalSource263.", "Yulang.GeneralRebaseTwoOwnerRegression263.", "Yulang.GeneralRebaseUniversalMeaning263.", "Yulang.GeneralRebaseUniversalTrace263.", "Yulang.GeneralRebaseUniversalRegression263.", "Yulang.GeneralRebaseSourceRepresentatives263.", "Yulang.GeneralRebaseRepresentativesExample263.", "Yulang.GeneralRebaseSourceMeaning263.", "Yulang.GeneralRebaseSourceLocalHeads263.", "Yulang.GeneralRebaseSourceLocalMeaning263.", "Yulang.GeneralRebaseFiniteStates263."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE263-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
