import Yulang.GeneralDictionary170NamedCoverage
import Yulang.GeneralDictionary170NamedAccessible
import Yulang.GeneralDictionary170NamedCoveragePersistence
import Lean

/-! Read-only dependency gate, including generated declarations. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionary170NamedCoverage, `Yulang.GeneralDictionary170NamedAccessible, `Yulang.GeneralDictionary170NamedCoveragePersistence]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
