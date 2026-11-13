import Yulang.GeneralDictionary171AssemblyPersistence
import Yulang.GeneralDictionary171AssemblySize
import Yulang.GeneralDictionary171BoundedAssembly
import Yulang.GeneralDictionary171CheckedSpine
import Yulang.GeneralDictionary171CheckedSpineExample
import Yulang.GeneralDictionary171InputDiscovery
import Yulang.GeneralDictionary171InspectionObservation
import Yulang.GeneralDictionary171LocalInspectionObservation
import Yulang.GeneralDictionary171NamedSpinePersistence
import Yulang.GeneralDictionary171RecursiveStrictness
import Yulang.GeneralDictionary171RequestChecker
import Yulang.GeneralDictionary171SelectedAssembly
import Yulang.GeneralDictionary171SpineAccessible
import Yulang.GeneralDictionary171SpineCoverage
import Yulang.GeneralDictionary171SpineDiscovery
import Yulang.GeneralDictionary171SpineDiscoveryExample
import Yulang.GeneralDictionary171SpineExample
import Yulang.GeneralDictionary171SpinePersistence
import Yulang.GeneralDictionary171SpineTree
import Lean

/-! Read-only dependency gate, including generated declarations. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionary171AssemblyPersistence, `Yulang.GeneralDictionary171AssemblySize, `Yulang.GeneralDictionary171BoundedAssembly, `Yulang.GeneralDictionary171CheckedSpine, `Yulang.GeneralDictionary171CheckedSpineExample, `Yulang.GeneralDictionary171InputDiscovery, `Yulang.GeneralDictionary171InspectionObservation, `Yulang.GeneralDictionary171LocalInspectionObservation, `Yulang.GeneralDictionary171NamedSpinePersistence, `Yulang.GeneralDictionary171RecursiveStrictness, `Yulang.GeneralDictionary171RequestChecker, `Yulang.GeneralDictionary171SelectedAssembly, `Yulang.GeneralDictionary171SpineAccessible, `Yulang.GeneralDictionary171SpineCoverage, `Yulang.GeneralDictionary171SpineDiscovery, `Yulang.GeneralDictionary171SpineDiscoveryExample, `Yulang.GeneralDictionary171SpineExample, `Yulang.GeneralDictionary171SpinePersistence, `Yulang.GeneralDictionary171SpineTree]
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
