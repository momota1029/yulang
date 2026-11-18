import Yulang.GeneralDictionaryUpperHistory257
import Yulang.GeneralDictionaryFullExpansion257
import Yulang.GeneralPresenceIdempotentTree257
import Yulang.GeneralDictionaryOrdinaryShape257
import Yulang.GeneralDictionaryFullReduced257
import Yulang.GeneralDictionaryOrdinaryFinite257
import Yulang.GeneralDictionaryOrdinaryCanonical257
import Yulang.GeneralDictionaryCompactView257
import Yulang.GeneralDictionaryCompactFields257
import Yulang.GeneralDictionaryFiveSlot257
import Yulang.GeneralDictionaryInitialProjection257
import Yulang.GeneralDictionaryFiniteView257
import Yulang.GeneralDictionaryNoModelRefinement257
import Yulang.GeneralDictionaryProjectionBoundary257
import Yulang.GeneralDictionaryKnownProjection257
import Yulang.GeneralDictionaryPointProjection257
import Yulang.GeneralDictionaryReportProjection257
import Yulang.GeneralDictionaryBinderGap257
import Yulang.GeneralDictionaryHistoricalValues257
import Yulang.GeneralDictionaryBinderFact257
import Yulang.GeneralDictionaryPastRaw257
import Yulang.GeneralDictionaryPastObservations257
import Yulang.GeneralDictionaryPastPacket257
import Yulang.GeneralDictionaryJournalRepair257
import Yulang.GeneralDictionaryFiniteJournal257
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralDictionaryUpperHistory257.", "Yulang.GeneralDictionaryFullExpansion257.", "Yulang.GeneralPresenceIdempotentTree257.", "Yulang.GeneralDictionaryOrdinaryShape257.", "Yulang.GeneralDictionaryFullReduced257.", "Yulang.GeneralDictionaryOrdinaryFinite257.", "Yulang.GeneralDictionaryOrdinaryCanonical257.", "Yulang.GeneralDictionaryCompactView257.", "Yulang.GeneralDictionaryCompactFields257.", "Yulang.GeneralDictionaryFiveSlot257.", "Yulang.GeneralDictionaryInitialProjection257.", "Yulang.GeneralDictionaryFiniteView257.", "Yulang.GeneralDictionaryNoModelRefinement257.", "Yulang.GeneralDictionaryProjectionBoundary257.", "Yulang.GeneralDictionaryKnownProjection257.", "Yulang.GeneralDictionaryPointProjection257.", "Yulang.GeneralDictionaryReportProjection257.", "Yulang.GeneralDictionaryBinderGap257.", "Yulang.GeneralDictionaryHistoricalValues257.", "Yulang.GeneralDictionaryBinderFact257.", "Yulang.GeneralDictionaryPastRaw257.", "Yulang.GeneralDictionaryPastObservations257.", "Yulang.GeneralDictionaryPastPacket257.", "Yulang.GeneralDictionaryJournalRepair257.", "Yulang.GeneralDictionaryFiniteJournal257."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE257-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
