import Yulang.GeneralDictionaryHistoricalNominalCoverage
import Yulang.GeneralDictionaryHistoricalNominalRefreshExample
import Yulang.GeneralDictionaryHistoricalNominalTree
import Yulang.GeneralDictionaryHistoricalRefreshSelection
import Yulang.GeneralDictionaryMixedHistoricalCoverage
import Yulang.GeneralDictionaryMixedHistoricalExample
import Yulang.GeneralDictionaryNestedBranchTransport
import Yulang.GeneralDictionaryNestedCarrierExample
import Yulang.GeneralDictionaryNestedCurrentEvidence
import Yulang.GeneralDictionaryNestedRefinement
import Yulang.GeneralDictionaryNestedRefinementExamples
import Yulang.GeneralDictionaryNestedRefinementReplay
import Yulang.GeneralDictionaryRecordedInspectionFacts
import Yulang.GeneralDictionaryRefinedLocations
import Yulang.GeneralDictionaryReobservationRefinementGap
import Yulang.GeneralDictionaryRevisionArgumentBridge
import Yulang.GeneralDictionaryRevisionBridgeExample
import Yulang.GeneralDictionaryRevisionParameterCoverage
import Yulang.GeneralDictionaryScalarChildEvidence
import Yulang.GeneralDictionaryScalarChildExample
import Yulang.GeneralDictionaryScalarChildIntervals
import Yulang.GeneralDictionaryScalarChildReachable
import Yulang.GeneralDictionaryScalarGeneratedCoverage
import Yulang.GeneralDictionaryScalarRegistryExample
import Yulang.GeneralDictionaryScalarRegistryIntervals
import Yulang.GeneralDictionaryUnaryCurrentEvidence
import Yulang.GeneralDictionaryUnaryCurrentExample
import Yulang.GeneralDictionaryValueRecordedCoverageLimit
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryHistoricalNominalCoverage, `Yulang.GeneralDictionaryHistoricalNominalRefreshExample, `Yulang.GeneralDictionaryHistoricalNominalTree, `Yulang.GeneralDictionaryHistoricalRefreshSelection, `Yulang.GeneralDictionaryMixedHistoricalCoverage, `Yulang.GeneralDictionaryMixedHistoricalExample, `Yulang.GeneralDictionaryNestedBranchTransport, `Yulang.GeneralDictionaryNestedCarrierExample, `Yulang.GeneralDictionaryNestedCurrentEvidence, `Yulang.GeneralDictionaryNestedRefinement, `Yulang.GeneralDictionaryNestedRefinementExamples, `Yulang.GeneralDictionaryNestedRefinementReplay, `Yulang.GeneralDictionaryRecordedInspectionFacts, `Yulang.GeneralDictionaryRefinedLocations, `Yulang.GeneralDictionaryReobservationRefinementGap, `Yulang.GeneralDictionaryRevisionArgumentBridge, `Yulang.GeneralDictionaryRevisionBridgeExample, `Yulang.GeneralDictionaryRevisionParameterCoverage, `Yulang.GeneralDictionaryScalarChildEvidence, `Yulang.GeneralDictionaryScalarChildExample, `Yulang.GeneralDictionaryScalarChildIntervals, `Yulang.GeneralDictionaryScalarChildReachable, `Yulang.GeneralDictionaryScalarGeneratedCoverage, `Yulang.GeneralDictionaryScalarRegistryExample, `Yulang.GeneralDictionaryScalarRegistryIntervals, `Yulang.GeneralDictionaryUnaryCurrentEvidence, `Yulang.GeneralDictionaryUnaryCurrentExample, `Yulang.GeneralDictionaryValueRecordedCoverageLimit]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} (module {moduleName}) depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
