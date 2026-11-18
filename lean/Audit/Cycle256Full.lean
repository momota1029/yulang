import Yulang.GeneralNominalInputOccurrences256
import Yulang.GeneralNominalAggregateAtoms256
import Yulang.GeneralNominalSourceAggregate256
import Yulang.GeneralNominalHistoricalAggregate256
import Yulang.GeneralNominalFrameAggregate256
import Yulang.GeneralNominalInitialAggregate256
import Yulang.GeneralDictionaryReachableAggregate256
import Yulang.GeneralPresenceOrderedAppend256
import Yulang.GeneralDictionaryAggregateHistory256
import Yulang.GeneralDictionaryAggregateBasis256
import Yulang.GeneralDictionaryAggregateRows256
import Yulang.GeneralDictionaryHistoricalFields256
import Yulang.GeneralNominalSlotTypeMap256
import Yulang.GeneralDictionarySlotView256
import Yulang.GeneralNominalOrderedRawPublic256
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralNominalInputOccurrences256.", "Yulang.GeneralNominalAggregateAtoms256.", "Yulang.GeneralNominalSourceAggregate256.", "Yulang.GeneralNominalHistoricalAggregate256.", "Yulang.GeneralNominalFrameAggregate256.", "Yulang.GeneralNominalInitialAggregate256.", "Yulang.GeneralDictionaryReachableAggregate256.", "Yulang.GeneralPresenceOrderedAppend256.", "Yulang.GeneralDictionaryAggregateHistory256.", "Yulang.GeneralDictionaryAggregateBasis256.", "Yulang.GeneralDictionaryAggregateRows256.", "Yulang.GeneralDictionaryHistoricalFields256.", "Yulang.GeneralNominalSlotTypeMap256.", "Yulang.GeneralDictionarySlotView256.", "Yulang.GeneralNominalOrderedRawPublic256."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE256-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
