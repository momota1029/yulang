import Yulang.GeneralDictionary171CheckedSpine
import Yulang.GeneralDictionary171SpineDiscoveryExample
import Yulang.GeneralDictionaryFiniteObservedExampleReserved

/-! Two existing actual source fixtures exercise the executable checker. A
linked reserved output is not a physical target; checker failure is not a
semantic no-dictionary or language rejection result. -/
namespace Yulang.GeneralDictionary171CheckedSpineExample
open GeneralDictionary171CheckedSpine GeneralDictionary171RequestChecker
open GeneralDictionary170NamedSpineExample
open GeneralDictionary171SpineDiscoveryExample (input)

theorem checked_true : check registry context root declaration checked input = true := by
  decide +kernel

theorem discovered : ∃ node, discover registry start root declaration (by simp) checked input = some node :=
  (discover_success_iff registry start root declaration (by simp) checked input).mpr checked_true

theorem checked_uniform_dictionary :
    GeneralNominalState.Models source GeneralDictionaryFiniteObservedExample.model ∧
    (∀ assignment, GeneralNominalState.Models source assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry context assignment root (.node declaration.id [])) :=
  ⟨GeneralDictionaryFiniteObservedExample.state_models,
    uniform_evidence registry context root declaration (by simp) checked input checked_true metadata⟩

/-- Same previous reserved-source fixture, not a new language counterexample. -/
theorem reserved_check_false :
    checkRequests GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExample.interpretation
      [GeneralDictionaryFiniteObservedExampleReserved.request] = false := by
  decide +kernel

/-- Initial-source formation and Linked do not supply a physical output slot.
The checker is sufficient, not complete for all linked demands. -/
theorem linked_without_physical_target :
    GeneralNominalSourceFormation.InitialSource GeneralDictionaryFiniteObservedExample.registry
      GeneralDictionaryFiniteObservedExampleReserved.context GeneralDictionaryFiniteObservedExampleReserved.root ∧
    GeneralNominalState.Linked GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExampleReserved.root.demand ∧
    (¬ ∃ slot : Fin GeneralDictionaryFiniteObservedExampleReserved.state.base.slots,
      GeneralDictionaryFiniteObservedExampleReserved.state.base.source slot = 2) ∧
    checkRequests GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExample.interpretation
      [GeneralDictionaryFiniteObservedExampleReserved.request] = false :=
  ⟨GeneralDictionaryFiniteObservedExampleReserved.initial_source,
    GeneralDictionaryFiniteObservedExampleReserved.initial_source.linked,
    GeneralDictionaryFiniteObservedExampleReserved.no_target_slot,reserved_check_false⟩
end Yulang.GeneralDictionary171CheckedSpineExample
