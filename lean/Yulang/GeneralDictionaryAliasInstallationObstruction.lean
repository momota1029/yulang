import Yulang.GeneralDictionarySelectedAliasConflict

/-! Actual conflicting current alias keys block installation, not every step.
The theorem assumes actual selections; it is not a reachable counterexample. -/
namespace Yulang.GeneralDictionaryAliasInstallationObstruction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- Necessary installation coherence at one actual focus, with no recorded
packet or scheduling assumption. All non-install rules remain outside scope. -/
theorem different_selected_not_installable (registry : Registry)
    (state : GeneralNominalSupport.Tracked roles) (focus : Occurrence roles)
    (firstKey lastKey : Nat) (firstChildren lastChildren : List (Occurrence roles))
    (first : GeneralNominalSupportBoundary.Local registry state focus (.selected firstKey firstChildren))
    (site : GeneralNominalDemandMerging.Site roles) (related : Related state.current focus site)
    (last : GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected lastKey lastChildren))
    (different : firstKey ≠ lastKey) (packet : Packet roles)
    (atFocus : packet.site.occurrence = focus) :
    ¬ GeneralNominalFeedbackSteps.Installable registry state.current packet := by
  intro enabled
  have joint := GeneralNominalCycleSteps.installable_joint enabled.1
  rw [atFocus] at joint
  exact GeneralDictionarySelectedAliasConflict.support_different_selected_no_joint
    registry state focus firstKey lastKey firstChildren lastChildren first site related last different
    packet.declaration.id joint
end Yulang.GeneralDictionaryAliasInstallationObstruction
