import Yulang.GeneralDictionaryActualSchema
import Yulang.GeneralDictionaryActualSchemaOrigin
import Yulang.GeneralDictionaryActualSchemaOriginExample
import Yulang.GeneralDictionaryActualSchemaScope
import Yulang.GeneralDictionaryCertifiedNonpointEvidence
import Yulang.GeneralDictionaryCheckedNonpointEvidence
import Yulang.GeneralDictionaryCollapseReadiness
import Yulang.GeneralDictionaryEmissionRequestIdentity
import Yulang.GeneralDictionaryNonpointBranch
import Yulang.GeneralDictionaryNonpointCertified
import Yulang.GeneralDictionaryNonpointCertifiedOutput
import Yulang.GeneralDictionaryNonpointCollapse
import Yulang.GeneralDictionaryNonpointEvidence
import Yulang.GeneralDictionaryNonpointExample
import Yulang.GeneralDictionaryNonpointModeBoundary
import Yulang.GeneralDictionaryNonpointOperationalEvidence
import Yulang.GeneralDictionaryNonpointOutput
import Yulang.GeneralDictionaryNonpointStrict
import Yulang.GeneralDictionaryNonpointStrictEvidence
import Yulang.GeneralDictionaryNonpointStrictOutput
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryActualSchema, `Yulang.GeneralDictionaryActualSchemaOrigin, `Yulang.GeneralDictionaryActualSchemaOriginExample, `Yulang.GeneralDictionaryActualSchemaScope, `Yulang.GeneralDictionaryCertifiedNonpointEvidence, `Yulang.GeneralDictionaryCheckedNonpointEvidence, `Yulang.GeneralDictionaryCollapseReadiness, `Yulang.GeneralDictionaryEmissionRequestIdentity, `Yulang.GeneralDictionaryNonpointBranch, `Yulang.GeneralDictionaryNonpointCertified, `Yulang.GeneralDictionaryNonpointCertifiedOutput, `Yulang.GeneralDictionaryNonpointCollapse, `Yulang.GeneralDictionaryNonpointEvidence, `Yulang.GeneralDictionaryNonpointExample, `Yulang.GeneralDictionaryNonpointModeBoundary, `Yulang.GeneralDictionaryNonpointOperationalEvidence, `Yulang.GeneralDictionaryNonpointOutput, `Yulang.GeneralDictionaryNonpointStrict, `Yulang.GeneralDictionaryNonpointStrictEvidence, `Yulang.GeneralDictionaryNonpointStrictOutput]
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
