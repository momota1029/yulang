import Yulang.GeneralDictionaryUnaryRefinementCapture
import Yulang.GeneralDictionaryMixedCarrierRefresh
import Lean
#print axioms Yulang.GeneralDictionaryUnaryRefinementCapture.queries_preserved
#print axioms Yulang.GeneralDictionaryUnaryRefinementCapture.report_refined
#print axioms Yulang.GeneralDictionaryUnaryRefinementCapture.bindings_preserved
#print axioms Yulang.GeneralDictionaryUnaryRefinementCapture.origins_preserved
#print axioms Yulang.GeneralDictionaryUnaryRefinementCapture.recorded_schema
#print axioms Yulang.GeneralDictionaryUnaryRefinementCapture.recorded_branch

open Yulang
open GeneralDictionaryMixedCatalogExample
open GeneralDictionaryMixedCarrierRefresh
open GeneralNominalExamples (displayRoot)
example (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models refreshed.current m) :
    GeneralNominalMaterialization.Models snapshot declaration currentCapture currentReport
      (GeneralNominalRecursiveCandidates.generated registry refreshedContext displayRoot declaration checked [(0,0)]) m :=
  by
    let prior : GeneralNominalRefinements.Refines packet.context.state snapshot :=
      ⟨refines.base,refines.heads,refines.nominals,(by intro _ h; cases h),refines.known,
        (by intro _ h; cases h),(by intro _ h; cases h),rfl,rfl⟩
    exact GeneralDictionaryUnaryRefinementCapture.recorded_schema displayRoot refreshed packet
      refreshed_reachable packet_recorded prior rfl (0 : Fin 2) GeneralNominalExamples.listDescriptor
      rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query rfl m valid


open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryUnaryRefinementCapture]
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

-- A positive current model also satisfies the complete generic branch conclusion.
example : GeneralNominalRecursiveCandidates.BranchModels registry refreshedContext displayRoot
    declaration checked [(0,0)] GeneralNominalExamples.model := by
  let prior : GeneralNominalRefinements.Refines packet.context.state snapshot :=
    ⟨refines.base,refines.heads,refines.nominals,(by intro _ h; cases h),refines.known,
      (by intro _ h; cases h),(by intro _ h; cases h),rfl,rfl⟩
  exact GeneralDictionaryUnaryRefinementCapture.recorded_branch displayRoot refreshed packet
    refreshed_reachable packet_recorded prior rfl (0 : Fin 2) GeneralNominalExamples.listDescriptor
    rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query rfl rfl
    GeneralNominalExamples.model refreshed_inhabited
