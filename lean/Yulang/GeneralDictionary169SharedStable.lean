import Yulang.GeneralNominalSharedSteps
import Yulang.GeneralDictionaryFiniteObservedExampleClassify

/-! Shared stability from absence of enabled value actions. Installation
successors differ; this is not an At/trace conversion. -/
namespace Yulang.GeneralDictionary169SharedStable
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport

/-- A Shared action has a Value action at the same focus, not necessarily with
its successor. The full Shared installation guard implies the Value guard. -/
theorem value_action_exists (action : GeneralNominalSharedSteps.At registry before focus after) :
    ∃ next, GeneralNominalValueSteps.At registry before focus next := by
  cases action with
  | administrative focus next update => exact ⟨_,.administrative focus next update⟩
  | install packet support enabled novel guard => exact ⟨_,.install packet support enabled novel guard.1⟩
  | merge first last support one two same novel guard => exact ⟨_,.merge first last support one two same novel guard⟩

theorem of_value (stable : GeneralNominalValueSteps.Stable registry state root) :
    GeneralNominalSharedSteps.Stable registry state root := by
  intro focus generated after action
  obtain ⟨next,old⟩ := value_action_exists action
  exact stable focus generated next old

open GeneralDictionaryFiniteObservedExample GeneralDictionaryFiniteObservedExampleStable

theorem actual_stable : GeneralNominalSharedSteps.Stable registry start root :=
  of_value GeneralDictionaryFiniteObservedExampleClassify.value_stable

theorem actual_formed : GeneralNominalSharedSteps.SourceFormed registry root start :=
  .initial context initial_source

/-- Existing inhabited named-output source now certified stable under the
actual Shared action relation. No nonzero execution or new dictionary claimed. -/
theorem actual_stable_named_dictionary :
    GeneralNominalSharedSteps.SourceFormed registry root start ∧
    GeneralNominalSharedSteps.Stable registry start root ∧
    Models start.current model ∧ root.demand.outputs ≠ [] ∧
    ∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry start.current.context assignment root
        (.node declaration.id []) :=
  ⟨actual_formed,actual_stable,initial_models model state_models,named_request_present,
    fun assignment valid => full_evidence assignment valid.1⟩
end Yulang.GeneralDictionary169SharedStable
