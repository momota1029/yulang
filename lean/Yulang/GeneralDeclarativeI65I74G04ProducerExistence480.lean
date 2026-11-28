import Yulang.GeneralDeclarativeI65I74EventwiseG04Producer480
import Yulang.GeneralDeclarativeI65I74G04PreviouslyRecorded480
import Yulang.GeneralDeclarativeI65I74MissingSourceOrder480

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479

/-- The declarative input and its exact same-phase basis suffice in
each of the three cases. An actual implementation of a supplier is
not part of this existence result. -/
theorem every_qualified_event_has_a_faithful_finite_wire480 :
    EventwiseG04Producer := by
  intro n p gd positions relations basis event valid
  cases kind : event.backing with
  | source trueSource =>
    cases retained : basis.recordedReads with
    | none =>
      exact a_source_without_recorded_order_still_has_a_faithful_finite_wire480
        event valid trueSource kind retained
    | some previous =>
      exact a_recorded_pre_erasure_source_order_has_a_faithful_finite_replay480
        event valid trueSource kind retained
  | released owner phase write origin asOutput settled active =>
    exact a_bound_released_fact_has_faithful_replay_without_issuing_it480
      event valid asOutput settled active kind

theorem g04_producer_proved_scoped480 : G04Producer :=
  g04_producer_iff_eventwise_exists480.mpr every_qualified_event_has_a_faithful_finite_wire480

end Yulang.GeneralDeclarativeI65.I72.Producer479
