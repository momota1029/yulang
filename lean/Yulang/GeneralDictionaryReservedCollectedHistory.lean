import Yulang.GeneralDictionaryCollectedRequests
import Yulang.GeneralDictionaryReservedRefreshedEvidence

/-! Actual source observation, reserved-output installation, equality feedback
and carrier-changing refresh collected by the operational history interface.
No final Supported premise is used. -/
namespace Yulang.GeneralDictionaryReservedCollectedHistory
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration interpretation checked)
open GeneralDictionaryReservedMixedProvenance (original batch source_observed)
open GeneralDictionaryReservedEqualityStep (after equality_step)
open GeneralDictionaryReservedNominalRefresh (refreshed refresh_step refreshed_inhabited)
open GeneralDictionaryCollectedRequests
open GeneralNominalMaterialization

theorem installed_requests : requests packet.context.state packet.registry packet.site.occurrence
    packet.declaration packet.checked packet.bindings = [request] := actual_requests_exact _

theorem installed_closed : (GeneralNominalPacketSupport.namedSchema packet).variables = [] := by
  change (generated state interpretation (requests state registry root declaration checked _)).variables = []
  rw [actual_requests_exact]
  simp [generated,request,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.normalizeArgs,interpretation,
    GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
    GeneralDictionaryFiniteObservedExample.constructors,schema,schemas,Schema.append]

theorem installed_history : Collected registry root installed batch := by
  have initial : Collected registry root start [] := .initial context initial_source
  have observed : Collected registry root start [original] := by
    simpa using Collected.observe initial [original] source_observed
  have result := Collected.install observed packet [] value_install_step installed_closed
  change Collected registry root installed ([original] ++ requests packet.context.state packet.registry
    packet.site.occurrence packet.declaration packet.checked packet.bindings) at result
  rw [installed_requests] at result
  exact result

theorem refreshed_history : Collected registry root refreshed batch :=
  .advance (.advance installed_history equality_step) refresh_step

/-- An old observed source and a newly allocated output remain jointly valid
through equality feedback and a genuine carrier extension. -/
theorem refreshed_batch_models (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report refreshed.current.context.state)
    (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models refreshed.current assignment) :
    Models refreshed.current.context.state declaration capture report
      (generated refreshed.current.context.state refreshed.current.context.interpretation batch) assignment :=
  GeneralDictionaryCollectedRequests.models refreshed_history batch (fun _ member => member)
    declaration capture report assignment valid

theorem nonvacuous_history :
    (¬ GeneralDictionaryObservedFiniteRequests.Observed state interpretation [request]) ∧
    Collected registry root refreshed batch ∧
    GeneralNominalSaturationState.Models refreshed.current positive :=
  ⟨not_observed,refreshed_history,refreshed_inhabited⟩
end Yulang.GeneralDictionaryReservedCollectedHistory
