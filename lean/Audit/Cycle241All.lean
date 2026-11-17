import Yulang.GeneralDictionaryRebase230Private241
import Yulang.GeneralDictionaryRebase230Service241
import Yulang.GeneralNominalRebaseBackExtension241
import Yulang.GeneralNominalRebaseChildProduction241
import Yulang.GeneralNominalRebaseDefinitions241
import Yulang.GeneralNominalRebaseEscape241
import Yulang.GeneralNominalRebaseInline241
import Yulang.GeneralNominalRebaseInlineModels241
import Yulang.GeneralNominalRebaseInlineSyntax241
import Yulang.GeneralNominalRebaseLiveLabels241
import Yulang.GeneralNominalRebaseMachine241
import Yulang.GeneralNominalRebaseNames241
import Yulang.GeneralNominalRebaseNoop241
import Yulang.GeneralNominalRebaseOwner241
import Yulang.GeneralNominalRebaseOwnerBack241
import Yulang.GeneralNominalRebaseProgress241
import Yulang.GeneralNominalRebaseProjection241
import Yulang.GeneralNominalRebaseProtectedLive241
import Yulang.GeneralNominalRebaseStore241
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryRebase230Private241, `Yulang.GeneralDictionaryRebase230Service241, `Yulang.GeneralNominalRebaseBackExtension241, `Yulang.GeneralNominalRebaseChildProduction241, `Yulang.GeneralNominalRebaseDefinitions241, `Yulang.GeneralNominalRebaseEscape241, `Yulang.GeneralNominalRebaseInline241, `Yulang.GeneralNominalRebaseInlineModels241, `Yulang.GeneralNominalRebaseInlineSyntax241, `Yulang.GeneralNominalRebaseLiveLabels241, `Yulang.GeneralNominalRebaseMachine241, `Yulang.GeneralNominalRebaseNames241, `Yulang.GeneralNominalRebaseNoop241, `Yulang.GeneralNominalRebaseOwner241, `Yulang.GeneralNominalRebaseOwnerBack241, `Yulang.GeneralNominalRebaseProgress241, `Yulang.GeneralNominalRebaseProjection241, `Yulang.GeneralNominalRebaseProtectedLive241, `Yulang.GeneralNominalRebaseStore241]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE241-ALL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE241-ALL-FAIL: no constants checked"
  logInfo m!"CYCLE241-ALL-PASS: {checked} constants in {modules.size} modules"
