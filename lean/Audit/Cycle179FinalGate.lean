import Yulang.GeneralNominalCenteredJournalExtension179
import Yulang.GeneralDictionaryCenteredNested179
import Yulang.GeneralDictionaryCenteredNestedExample179
import Yulang.GeneralDictionaryCenteredNestedLimit179
import Yulang.GeneralDictionaryCenteredPointCandidate179
import Yulang.GeneralDictionaryCenteredPointExample179
import Yulang.GeneralDictionaryCenteredPointInstall179
import Yulang.GeneralDictionaryCenteredPointJoint179
import Yulang.GeneralDictionaryCenteredPointReadback179
import Yulang.GeneralDictionaryCenteredSharedAny179
import Yulang.GeneralDictionaryNominalSharedDiscovery179
import Yulang.GeneralDictionaryNominalSharedDiscoveryExample179
import Yulang.GeneralNominalCenteredEmptyFrame179
import Yulang.GeneralNominalCenteredFrame179
import Yulang.GeneralNominalRawFrame179
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "179" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
