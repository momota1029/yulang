import Yulang.GeneralRebaseReportDecoder259
import Yulang.GeneralDictionaryObservedRebase259
import Yulang.GeneralDictionaryRebaseCertificate259
import Yulang.GeneralDictionaryRebaseRun259
import Yulang.GeneralNominalTypeObservation259
import Yulang.GeneralDictionaryRebaseCurrent259
import Yulang.GeneralVersionRowsRaw259
import Yulang.GeneralVersionRowsHead259
import Yulang.GeneralVersionRowsPacket259
import Yulang.GeneralVersionRowsStages259
import Yulang.GeneralVersionBoundaryCompletion259
import Yulang.GeneralVersionPublicProjection259
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralRebaseReportDecoder259.", "Yulang.GeneralDictionaryObservedRebase259.", "Yulang.GeneralDictionaryRebaseCertificate259.", "Yulang.GeneralDictionaryRebaseRun259.", "Yulang.GeneralNominalTypeObservation259.", "Yulang.GeneralDictionaryRebaseCurrent259.", "Yulang.GeneralVersionRowsRaw259.", "Yulang.GeneralVersionRowsHead259.", "Yulang.GeneralVersionRowsPacket259.", "Yulang.GeneralVersionRowsStages259.", "Yulang.GeneralVersionBoundaryCompletion259.", "Yulang.GeneralVersionPublicProjection259."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE259-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
