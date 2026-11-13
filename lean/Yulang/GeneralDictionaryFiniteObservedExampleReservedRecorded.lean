import Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive
import Yulang.GeneralDictionaryRecordedRequestModels

/-! An actual reserved-target installation derives its current request semantics
from the recorded packet, without an initial target slot or Observed premise. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleReservedRecorded
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration interpretation)
open GeneralNominalMaterialization

theorem recorded_request_models (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report installed.current.context.state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models installed.current assignment) :
    Models installed.current.context.state declaration capture report
      (generated installed.current.context.state installed.current.context.interpretation [request]) assignment := by
  have closed : (generated packet.context.state packet.context.interpretation
      (rootRequests packet.declaration packet.site.occurrence)).variables = [] := by
    change (generated state interpretation [request]).variables = []
    simp [generated,request,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.normalizeArgs,interpretation,
      GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
      GeneralDictionaryFiniteObservedExample.constructors,schema,schemas,Schema.append]
  exact GeneralDictionaryRecordedRequestModels.reachable_root_requests registry root installed
    value_reachable packet packet_recorded closed declaration capture report assignment valid

theorem reserved_install_regression :
    (¬ ∃ slot : Fin state.base.slots, state.base.source slot = 2) ∧
    (¬ GeneralDictionaryObservedFiniteRequests.Observed state interpretation [request]) ∧
    GeneralNominalValueSteps.Step registry root start installed ∧
    GeneralNominalSaturationState.Models installed.current positive ∧
    installed.current.packets ≠ [] :=
  ⟨no_target_slot,not_observed,value_install_step,installed_models,journal_nonempty⟩
end Yulang.GeneralDictionaryFiniteObservedExampleReservedRecorded
