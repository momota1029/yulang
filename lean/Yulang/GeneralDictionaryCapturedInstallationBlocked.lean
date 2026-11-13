import Yulang.GeneralDictionaryCapturedInputCountermodel

/-! Relate the actual trusted-readiness obstruction to installation premises.
Administrative observations and future source-supported states are not ruled out. -/
namespace Yulang.GeneralDictionaryCapturedInstallationBlocked
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport

theorem installable_guard_current {roles : Roles.RoleDecls} {registry : Registry}
    {state : Tracked roles} {packet : Packet roles} {support : List (Occurrence roles)}
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : GeneralNominalSharedSteps.PacketGuard state packet support) :
    GeneralNominalSharedSupport.DecisionGuard registry state packet.site.occurrence := by
  have result := guard.2.1
  rw [enabled.1.1,enabled.1.2.1] at result
  exact result

open GeneralDictionarySharedCapturedResumption GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedModel
open GeneralDeclarationExamples (roles)

theorem consumer_packet_guard_absent (packet : Packet roles)
    (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry observed.current packet)
    (focus : packet.site.occurrence = consumer) :
    ¬ GeneralNominalSharedSteps.PacketGuard observed packet support := by
  intro guard
  have current := installable_guard_current enabled guard
  rw [focus] at current
  exact GeneralDictionaryCapturedInputCountermodel.consumer_decision_guard_absent current

theorem no_guarded_consumer_installation :
    ¬ ∃ packet : Packet roles, ∃ support : List (Occurrence roles),
      packet.site.occurrence = consumer ∧
      GeneralNominalFeedbackSteps.Installable registry observed.current packet ∧
      GeneralNominalSharedSteps.PacketGuard observed packet support := by
  rintro ⟨packet,support,focus,enabled,guard⟩
  exact consumer_packet_guard_absent packet support enabled focus guard
end Yulang.GeneralDictionaryCapturedInstallationBlocked
