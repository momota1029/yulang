import Yulang.GeneralDictionaryAliasBranch215
import Yulang.GeneralDictionaryCheckedAnchors215
import Yulang.GeneralDictionaryCheckedOrigins215
import Yulang.GeneralDictionaryCurrentBranch215
import Yulang.GeneralDictionaryCurrentProjection215
import Yulang.GeneralDictionaryCurrentPropagation215
import Yulang.GeneralDictionaryCurrentRawHead215
import Yulang.GeneralDictionaryCurrentRoots215
import Yulang.GeneralDictionaryDefaultAliasCenters215
import Yulang.GeneralDictionaryDefaultAliasConflicts215
import Yulang.GeneralDictionaryDefaultAliasProjection215
import Yulang.GeneralDictionaryDefaultAliasRawProjection215
import Yulang.GeneralDictionaryDefaultAliasReadback215
import Yulang.GeneralDictionaryDefaultChoiceObstruction215
import Yulang.GeneralDictionaryDefaultNominalFallback215
import Yulang.GeneralDictionaryDefaultNominalProjection215
import Yulang.GeneralDictionaryDefaultPreFrame215
import Yulang.GeneralDictionaryDefaultProjectionBounds215
import Yulang.GeneralDictionaryInspectionConflicts215
import Yulang.GeneralDictionaryInspectionHeads215
import Yulang.GeneralDictionaryInspectionSchema215
import Yulang.GeneralDictionaryRawProjection215
import Yulang.GeneralDictionaryRecursiveBounds215
import Yulang.GeneralDictionaryStructuralProjection215
import Yulang.GeneralDictionaryWeakReport215
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryAliasBranch215, `Yulang.GeneralDictionaryCheckedAnchors215, `Yulang.GeneralDictionaryCheckedOrigins215, `Yulang.GeneralDictionaryCurrentBranch215, `Yulang.GeneralDictionaryCurrentProjection215, `Yulang.GeneralDictionaryCurrentPropagation215, `Yulang.GeneralDictionaryCurrentRawHead215, `Yulang.GeneralDictionaryCurrentRoots215, `Yulang.GeneralDictionaryDefaultAliasCenters215, `Yulang.GeneralDictionaryDefaultAliasConflicts215, `Yulang.GeneralDictionaryDefaultAliasProjection215, `Yulang.GeneralDictionaryDefaultAliasRawProjection215, `Yulang.GeneralDictionaryDefaultAliasReadback215, `Yulang.GeneralDictionaryDefaultChoiceObstruction215, `Yulang.GeneralDictionaryDefaultNominalFallback215, `Yulang.GeneralDictionaryDefaultNominalProjection215, `Yulang.GeneralDictionaryDefaultPreFrame215, `Yulang.GeneralDictionaryDefaultProjectionBounds215, `Yulang.GeneralDictionaryInspectionConflicts215, `Yulang.GeneralDictionaryInspectionHeads215, `Yulang.GeneralDictionaryInspectionSchema215, `Yulang.GeneralDictionaryRawProjection215, `Yulang.GeneralDictionaryRecursiveBounds215, `Yulang.GeneralDictionaryStructuralProjection215, `Yulang.GeneralDictionaryWeakReport215]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE215-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE215-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE215-GATE-PASS: {checked} constants in {modules.size} modules"
