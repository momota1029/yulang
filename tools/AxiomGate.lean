-- Supervisor-owned axiom gate. Run from lean/ via tools/verify-lean.sh (never edited by workers).
-- Checks EVERY constant of every non-system module imported below, independent of lean/Audit.lean.
import Yulang
import SpecExamples
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let system : List Name := [`Init, `Std, `Lean, `Lake]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      unless system.any (·.isPrefixOf moduleName) do
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} (module {moduleName}) depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
