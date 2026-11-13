import Yulang.GeneralDictionary172CheckedSpineExact
import Yulang.GeneralDictionary171CheckedSpineExample

/-! Regressions for the exact conservative criterion. The reserved-source case
is initially reachable and satisfiable, but has no physical target slot. We do
not claim semantic Evidence or a language outcome for that case. -/
namespace Yulang.GeneralDictionary172CheckerRegression
open GeneralDictionary171RequestChecker
open GeneralDictionary172CheckerExact

/-- The actual successful named-spine fixture satisfies the independent test
criterion and carries a dictionary uniformly over current models. -/
theorem named_criterion_and_dictionary :
    GeneralDictionary171SpineDiscovery.RequestsFinished
      GeneralDictionary170NamedSpineExample.registry
      GeneralDictionary170NamedSpineExample.context
      GeneralDictionary170NamedSpineExample.root
      GeneralDictionary170NamedSpineExample.declaration
      GeneralDictionary170NamedSpineExample.checked
      GeneralDictionary171SpineDiscoveryExample.input ∧
    (∀ assignment, GeneralNominalState.Models GeneralDictionary170NamedSpineExample.source assignment →
      GeneralDictionaryRecursiveEvidence.Evidence GeneralDictionary170NamedSpineExample.registry
        GeneralDictionary170NamedSpineExample.context assignment GeneralDictionary170NamedSpineExample.root
        (.node GeneralDictionary170NamedSpineExample.declaration.id [])) :=
  ⟨(GeneralDictionary172CheckedSpineExact.check_iff ..).mp
    GeneralDictionary171CheckedSpineExample.checked_true,
    GeneralDictionary171CheckedSpineExample.checked_uniform_dictionary.2⟩

/-- The reason the reserved fixture fails this criterion is exact physical
identity, before Closed, Finished or PointInspection can help. -/
theorem reserved_no_certificate :
    ¬ ∃ slot, At GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExample.interpretation
      GeneralDictionaryFiniteObservedExampleReserved.request slot := by
  rintro ⟨slot,target,rest⟩
  exact GeneralDictionaryFiniteObservedExampleReserved.no_target_slot ⟨slot,target.symm⟩

/-- The Boolean false result coexists with an actual reachable initial state
and a current model. It is not interpreted here as language rejection. -/
theorem reachable_satisfiable_checker_false :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      GeneralDictionaryFiniteObservedExample.registry
      GeneralDictionaryFiniteObservedExampleReserved.root
      GeneralDictionaryFiniteObservedExampleReserved.start ∧
    GeneralNominalState.Models GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExample.model ∧
    checkRequests GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExample.interpretation
      [GeneralDictionaryFiniteObservedExampleReserved.request] = false ∧
    ¬ ∃ slot, At GeneralDictionaryFiniteObservedExampleReserved.state
      GeneralDictionaryFiniteObservedExample.interpretation
      GeneralDictionaryFiniteObservedExampleReserved.request slot :=
  ⟨GeneralDictionaryFiniteObservedExampleReserved.initial_reachable,
    GeneralDictionaryFiniteObservedExampleReserved.source_models,
    GeneralDictionary171CheckedSpineExample.reserved_check_false,
    reserved_no_certificate⟩
end Yulang.GeneralDictionary172CheckerRegression
