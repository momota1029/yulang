import Yulang.GeneralDictionaryRecursive168Transport
import Lean

/-! Read-only dependency/type audit for finite-tree relocation. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : Name := `Yulang.GeneralDictionaryRecursive168Transport
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName == wanted then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"

#check @Yulang.GeneralDictionaryRecursive168Transport.children_seed
#check @Yulang.GeneralDictionaryRecursive168Transport.instance_relocated
#check @Yulang.GeneralDictionaryRecursive168Transport.indexed_relocated
#check @Yulang.GeneralDictionaryRecursive168Transport.erased_relocated
