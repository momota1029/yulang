import Yulang.GeneralDictionaryMixedClosedBase234
import Yulang.GeneralDictionaryMixedClosedEvidence234
import Yulang.GeneralDictionaryMixedClosedFrame234
import Yulang.GeneralDictionaryMixedClosedPlan234
import Yulang.GeneralDictionaryMixedClosedRefresh234
import Yulang.GeneralDictionaryMixedClosedRegression234
import Yulang.GeneralDictionaryMixedClosedSelected234
import Yulang.GeneralDictionaryMixedClosedSemantics234
import Yulang.GeneralDictionaryMixedClosedSnapshot234
import Yulang.GeneralDictionaryMixedClosedStable234
import Yulang.GeneralDictionaryMixedClosedStep234
import Yulang.GeneralDictionaryMixedClosedTransport234
import Yulang.GeneralDictionaryMixedClosedTrust234
import Yulang.GeneralDictionaryMixedGap206Refresh234
import Yulang.GeneralDictionaryMixedGap206Snapshot234
import Yulang.GeneralDictionaryMixedGap206Trusted234
import Yulang.GeneralDictionaryVersionedGap206After234
import Yulang.GeneralDictionaryVersionedGap206AfterSelected234
import Yulang.GeneralDictionaryVersionedGap206AfterStable234
import Yulang.GeneralDictionaryVersionedGap206Feedback234
import Yulang.GeneralDictionaryVersionedGap206Selected234
import Yulang.GeneralNominalVersionedEquate234
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedClosedBase234,`Yulang.GeneralDictionaryMixedClosedEvidence234,`Yulang.GeneralDictionaryMixedClosedFrame234,`Yulang.GeneralDictionaryMixedClosedPlan234,`Yulang.GeneralDictionaryMixedClosedRefresh234,`Yulang.GeneralDictionaryMixedClosedRegression234,`Yulang.GeneralDictionaryMixedClosedSelected234,`Yulang.GeneralDictionaryMixedClosedSemantics234,`Yulang.GeneralDictionaryMixedClosedSnapshot234,`Yulang.GeneralDictionaryMixedClosedStable234,`Yulang.GeneralDictionaryMixedClosedStep234,`Yulang.GeneralDictionaryMixedClosedTransport234,`Yulang.GeneralDictionaryMixedClosedTrust234,`Yulang.GeneralDictionaryMixedGap206Refresh234,`Yulang.GeneralDictionaryMixedGap206Snapshot234,`Yulang.GeneralDictionaryMixedGap206Trusted234,`Yulang.GeneralDictionaryVersionedGap206After234,`Yulang.GeneralDictionaryVersionedGap206AfterSelected234,`Yulang.GeneralDictionaryVersionedGap206AfterStable234,`Yulang.GeneralDictionaryVersionedGap206Feedback234,`Yulang.GeneralDictionaryVersionedGap206Selected234,`Yulang.GeneralNominalVersionedEquate234]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE234-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE234-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE234-SECOND-PASS: {checked} constants in {modules.size} modules"
