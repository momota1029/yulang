import Yulang.GeneralDictionaryMatInputAssembly201
import Yulang.GeneralDictionaryMatScalarConflict200

/-! A real inhabited current journal and valid head model do not force class
output consistency. This is not a selected or stable V6 counterexample. -/
namespace Yulang.GeneralDictionaryMatInputScope201
open GeneralDictionaryMatScalarConflict200

theorem restricted : GeneralDictionaryMatInputVariables201.InputVariableClauses declaration := by
  intro clause member
  cases member

theorem no_common_head_class :
    ¬ (GeneralNominalCenteredHeadOutputs.HeadEquations plan model ∧
       GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan model) := by
  rintro ⟨head,effects⟩
  exact no_total_holds (GeneralDictionaryMatInputAssembly201.holds_of_head_class plan start.core
    frame.raw_recorded model head_model head effects restricted)

theorem current_head_not_joint :
    GeneralNominalCenteredHeadMatStepJournal.Models start model ∧
    GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(1,1)] model ∧
    GeneralNominalCenteredHeadOutputs.Frame registry start.core root 37 plan ∧
    GeneralDictionaryMatInputVariables201.InputVariableClauses declaration ∧
    ¬ (GeneralNominalCenteredHeadOutputs.HeadEquations plan model ∧
       GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan model) :=
  ⟨inhabited,head_model,frame,restricted,no_common_head_class⟩

end Yulang.GeneralDictionaryMatInputScope201
