import Yulang.GeneralDictionaryCaptureMultiplicity
import Yulang.GeneralDictionaryCaptureSemanticCollapse
import Yulang.GeneralDictionaryPositiveNestedBranch
import Yulang.GeneralDictionaryPositiveNestedInitial
import Yulang.GeneralDictionaryPositiveNestedProjection
import Yulang.GeneralDictionarySemanticCollapse
import Yulang.GeneralDictionarySemanticCollapseAllocation
import Yulang.GeneralDictionarySemanticCollapseAllocationExample
import Yulang.GeneralDictionarySemanticCollapseBranch
import Yulang.GeneralDictionarySemanticCollapseBranchExample
import Yulang.GeneralDictionarySemanticCollapseEvidenceExample
import Yulang.GeneralDictionarySemanticCollapseExample
import Yulang.GeneralDictionarySemanticCollapseOutputExample
import Yulang.GeneralDictionarySemanticCollapsePointBoundary
import Yulang.GeneralDictionarySemanticCollapseSchema
import Yulang.GeneralDictionarySemanticSchemaTransport
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryCaptureMultiplicity, `Yulang.GeneralDictionaryCaptureSemanticCollapse, `Yulang.GeneralDictionaryPositiveNestedBranch, `Yulang.GeneralDictionaryPositiveNestedInitial, `Yulang.GeneralDictionaryPositiveNestedProjection, `Yulang.GeneralDictionarySemanticCollapse, `Yulang.GeneralDictionarySemanticCollapseAllocation, `Yulang.GeneralDictionarySemanticCollapseAllocationExample, `Yulang.GeneralDictionarySemanticCollapseBranch, `Yulang.GeneralDictionarySemanticCollapseBranchExample, `Yulang.GeneralDictionarySemanticCollapseEvidenceExample, `Yulang.GeneralDictionarySemanticCollapseExample, `Yulang.GeneralDictionarySemanticCollapseOutputExample, `Yulang.GeneralDictionarySemanticCollapsePointBoundary, `Yulang.GeneralDictionarySemanticCollapseSchema, `Yulang.GeneralDictionarySemanticSchemaTransport]
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
