import Yulang.GeneralDictionaryOutputMergeContextComplete

/-! Two administrative rule families are disabled at the concrete refreshed
journal. This is not full Stable: other update families require separate proof. -/
namespace Yulang.GeneralDictionaryOutputMergeObservationClosure
open GeneralDictionaryOutputMergeRefresh
open GeneralNominalReobservationSteps

/-- The sole nominal descriptor already has point-valued parameters. -/
theorem point_closed : PointClosed snapshot := by
  intro slot d recorded
  change (if slot = 0 then some descriptor else none) = some d at recorded
  split at recorded
  · cases Option.some.inj recorded
    intro parameter member
    have same := List.mem_singleton.mp member
    subst parameter
    rfl
  · cases recorded

/-- No certified or uncertified descriptor revision can meet Improves. -/
theorem no_reobservation (revision : Revision refreshed.current) : ¬ Improves revision :=
  pointClosed_no_revision point_closed revision

/-- Raw entailment now matches journal entailment, so equality novelty fails
for every source pair, without even needing the registered-source premises. -/
theorem no_fresh_equality (first last : Nat)
    (equal : GeneralNominalFeedbackK2.Equal refreshed.current first last) :
    ¬ (¬ GeneralNominalFeedbackSteps.RawEqual refreshed.current first last) :=
  fun novel => novel ((GeneralDictionaryOutputMergeContextComplete.equality_exact first last).mp equal)

end Yulang.GeneralDictionaryOutputMergeObservationClosure
