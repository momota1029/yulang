import Yulang.GeneralDictionaryActualStable173
import Yulang.GeneralNominalActualInspectionExamples
import Yulang.GeneralDictionarySharedCurrentEvidence

/-! A concrete inhabited Actual installation with a nonempty where-child.
The child dictionary and stability of the successor are NOT assumed proved. -/
namespace Yulang.GeneralDictionaryActualExample173
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralNominalSharedExamples (packet)
open GeneralDictionarySharedDisplayInstallation (start after installable novel)
open GeneralNominalSaturationState
open GeneralDictionaryRecursiveEvidence

theorem display_not_stable :
    ¬ GeneralNominalActualBoundary.Stable registry start displayRoot := by
  intro stable
  exact novel (GeneralDictionaryActualStable173.stable_committed
    (packet false) [] stable installable GeneralNominalActualInspectionExamples.display_guard)

theorem actual_inhabited_child :
    GeneralNominalActualInspectionSteps.Step registry displayRoot start after ∧
    ∃ model, Models after.current model ∧ Generated after.current displayRoot displayChild :=
  ⟨GeneralNominalActualInspectionExamples.display_step,
    by obtain ⟨model,valid⟩ := GeneralDictionarySharedDisplayInstallation.inhabited
       exact ⟨model,valid,GeneralDictionarySharedDisplayInstallation.generated_child⟩⟩

theorem current_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) :
    Instance registry after.current.context model displayRoot
      GeneralDeclarationExamples.display.id (packet false).children :=
  GeneralDictionarySharedCurrentEvidence.current_instance (packet false) [] installable model valid

/-- The parent is sound in the same final model when its actual child has
source evidence. It is not a claim that the child was executed or solved. -/
theorem current_node (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) (dictionaries : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂
      (Evidence registry after.current.context model) (packet false).children dictionaries) :
    Evidence registry after.current.context model displayRoot
      (.node GeneralDeclarationExamples.display.id dictionaries) :=
  GeneralDictionarySharedCurrentEvidence.current_evidence (packet false) [] installable model valid dictionaries children

end Yulang.GeneralDictionaryActualExample173
