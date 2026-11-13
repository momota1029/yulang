import Yulang.GeneralDictionaryReservedClassifierSoundness

/-! What the actual equality successor has closed, and what it has not.
Raw equality is fed back, but no carrier slot for the reserved output has been
created. These facts do not establish Stable: certified refresh and arbitrary
packet-installation obligations still require separate analysis. -/
namespace Yulang.GeneralDictionaryReservedSuccessorBoundary
set_option backward.isDefEq.respectTransparency false
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry descriptor)
open GeneralDictionaryReservedEqualityStep
open GeneralNominalReobservationSteps

theorem raw_equal : GeneralNominalFeedbackSteps.RawEqual after.current 2 0 :=
  GeneralNominalFeedbackSteps.equate_feedback installed.current 2 0

theorem no_target_slot : ¬ ∃ slot : Fin after.current.context.state.base.slots,
    after.current.context.state.base.source slot = 2 := by
  rintro ⟨slot,equal⟩
  have bound := slot.isLt
  change slot.val = 2 at equal
  change slot.val < 2 at bound
  omega

theorem output_not_known : ¬ GeneralNominalState.Known after.current.context.state 2 := by
  rintro ⟨slot,equal,_⟩
  exact no_target_slot ⟨slot,equal⟩

theorem point_closed : PointClosed after.current.context.state := by
  change PointClosed state
  intro slot desc recorded
  change (if slot = (0 : Fin 2) then some descriptor else none) = some desc at recorded
  split at recorded
  · have same := Option.some.inj recorded
    subst desc
    intro parameter member
    change parameter ∈ [.type (1,1),.type (1,1),.type (1,1)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst parameter
    rfl
  · cases recorded

theorem no_reobservation (revision : Revision after.current) : ¬ Improves revision :=
  pointClosed_no_revision point_closed revision

/-- Any claimed terminality must in particular exclude a certified observation
refresh for source 2; ordinary equality feedback did not make that source Known. -/
theorem stable_excludes_output_refresh
    (stable : GeneralNominalValueSteps.Stable registry after root)
    (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh after.current next) :
    ¬ GeneralNominalState.Known next.state 2 := by
  intro known
  apply stable root .root _ (.administrative root _ (.refresh root next certificate 2 ?_ output_not_known known))
  apply List.mem_append_left
  apply List.mem_append_right
  change 2 ∈ [2]
  exact List.mem_singleton_self _

end Yulang.GeneralDictionaryReservedSuccessorBoundary
