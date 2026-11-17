import Yulang.GeneralNominalVersionedInstallStep232
import Yulang.GeneralNominalVersionedReplayEffects232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedCommitted232
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalVersionedInstall232 GeneralNominalVersionedInstallStep232
open GeneralNominalVersionedInstallation231

theorem replay_committed (state : State roles) (effect : Effect roles) :
    Committed (install state effect) (replayPlan effect.plan) := by
  constructor
  · intro model valid
    have previous := (installed_committed state effect).1 model valid
    refine ⟨(replay_holds_iff effect.plan model).mpr previous.1,?_⟩
    exact (GeneralNominalVersionedReplayEffects232.replay_class_effects_iff
      (install state effect).core effect.plan.packet.site.occurrence effect.plan model).mpr previous.2
  · intro child member
    rw [replay_children] at member
    exact installed_child member

theorem no_replay_reinstall :
    ¬ (¬ Committed (install state effect) (replayPlan effect.plan)) :=
  fun novel => novel (replay_committed state effect)

end Yulang.GeneralNominalVersionedCommitted232
