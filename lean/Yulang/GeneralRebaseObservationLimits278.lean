import Yulang.GeneralRebaseHistoryOrder278
import Yulang.GeneralRebaseVersionAbsorb278
import Yulang.GeneralRebaseLooseAbsorb278

namespace Yulang.GeneralRebaseObservationLimits278
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseHistoryOrder278 (observationKey)
open GeneralRebaseTerminalAbsorb278 (InstallTransition)

def VersionInstallAvailable (t : Tick) : Prop :=
  ∃ target, InstallTransition GeneralDictionaryVersionLoopSource237.registry
    GeneralDictionaryVersionLoopSource237.root (GeneralRebaseVersionMicro278.raw t) target

def LooseInstallAvailable (t : Tick) : Prop :=
  ∃ target, InstallTransition GeneralDictionaryLooseLoopSource240.registry
    GeneralDictionaryLooseLoopSource240.root (GeneralRebaseLooseMicro278.raw t) target

theorem version_collision (n : Nat) :
    observationKey ⟨n,.refreshed⟩ = observationKey ⟨n+1,.enter⟩ ∧
    ¬ VersionInstallAvailable ⟨n,.refreshed⟩ ∧ VersionInstallAvailable ⟨n+1,.enter⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨target,step⟩
    exact GeneralRebaseVersionAbsorb278.refreshed_absorbs n target step
  · exact ⟨_,(GeneralRebaseVersionAbsorb278.enter_install (n+1) _).mpr rfl⟩

theorem loose_collision (n : Nat) :
    observationKey ⟨n,.refreshed⟩ = observationKey ⟨n+1,.enter⟩ ∧
    ¬ LooseInstallAvailable ⟨n,.refreshed⟩ ∧ LooseInstallAvailable ⟨n+1,.enter⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨target,step⟩
    exact GeneralRebaseLooseAbsorb278.refreshed_absorbs n target step
  · exact ⟨_,(GeneralRebaseLooseAbsorb278.enter_install (n+1) _).mpr rfl⟩

theorem version_no_key_install_test :
    ¬ ∃ test : Nat × Nat → Prop, ∀ t, VersionInstallAvailable t ↔ test (observationKey t) := by
  rintro ⟨test,h⟩
  have ⟨same,absent,present⟩ := version_collision 0
  exact absent ((h ⟨0,.refreshed⟩).mpr (same ▸ (h ⟨1,.enter⟩).mp present))

theorem loose_no_key_install_test :
    ¬ ∃ test : Nat × Nat → Prop, ∀ t, LooseInstallAvailable t ↔ test (observationKey t) := by
  rintro ⟨test,h⟩
  have ⟨same,absent,present⟩ := loose_collision 0
  exact absent ((h ⟨0,.refreshed⟩).mpr (same ▸ (h ⟨1,.enter⟩).mp present))

end Yulang.GeneralRebaseObservationLimits278
