import Yulang.GeneralDictionarySharedDisplayInstallation
import Yulang.GeneralDictionarySharedCurrentEvidence
import Yulang.GeneralDictionarySupportRecursiveExample

/-! A complete recursive semantic dictionary after a real certified-origin
Shared installation. The Int leaf is justified from source models, not assumed.
This is not a Stable result or proof that the leaf has a recorded packet. -/
namespace Yulang.GeneralDictionarySharedRecursiveExample
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open GeneralDeclarations GeneralNominalSaturationState
open GeneralDictionaryRecursiveEvidence
open GeneralNominalSharedExamples (packet)
open GeneralDictionarySharedDisplayInstallation (start after)

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context true) displayRoot :=
  GeneralDictionarySupportRecursiveExample.initial_source

theorem formed : GeneralNominalSharedSteps.SourceFormed registry displayRoot after :=
  .update (.initial _ initial_source) GeneralDictionarySharedDisplayInstallation.step

theorem actual_trace : B4Target.Steps (GeneralNominalSharedSteps.Step registry displayRoot) start after :=
  .tail .refl GeneralDictionarySharedDisplayInstallation.step

theorem parent_instance (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    Instance registry after.current.context model displayRoot 1 [displayChild] := by
  have result := GeneralDictionarySharedCurrentEvidence.current_instance (packet false) []
    GeneralDictionarySharedDisplayInstallation.installable model valid
  change Instance registry after.current.context model displayRoot 1 (packet false).children at result
  rw [GeneralDictionarySharedDisplayInstallation.children] at result
  exact result

theorem leaf_evidence (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    Evidence registry after.current.context model displayChild (.node 3 []) := by
  have original := ((GeneralNominalSharedSteps.install_models (state := start) (packet := packet false)
    (support := []) rfl model).mp valid).1.1
  have current := GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) after.current.context
    (GeneralDictionarySharedCurrentEvidence.private_extension (packet false) []) model valid.1 displayChild 3 []
    (GeneralDictionarySupportRecursiveExample.leaf_instance model original)
  exact evidence_node _ _ _ _ _ _ _ current .nil

theorem recursive_evidence (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    Evidence registry after.current.context model displayRoot (.node 1 [.node 3 []]) :=
  evidence_node _ _ _ _ _ _ _ (parent_instance model valid) (.cons (leaf_evidence model valid) .nil)

theorem nonvacuous_recursive_dictionary :
    GeneralNominalSharedSteps.SourceFormed registry displayRoot after ∧
    B4Target.Steps (GeneralNominalSharedSteps.Step registry displayRoot) start after ∧
    (∃ model, Models after.current model) ∧
    ∀ model, Models after.current model →
      Evidence registry after.current.context model displayRoot (.node 1 [.node 3 []]) :=
  ⟨formed,actual_trace,GeneralDictionarySharedDisplayInstallation.inhabited,recursive_evidence⟩
end Yulang.GeneralDictionarySharedRecursiveExample
