import Yulang.GeneralNominalVersionedInstall232
import Yulang.GeneralNominalCenteredHeadMatStepTrustedGrowth
set_option backward.isDefEq.respectTransparency false

/-! Versioned installation retains inherited legacy trusted-slice cache
certificates. No new effect is admitted as a trusted source by this theorem;
completeness of cache justification using versioned effects remains open. -/
namespace Yulang.GeneralNominalVersionedCache232
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedInstall232
open GeneralNominalCenteredHeadMatStepObservations
open GeneralCanonicalObservations (Recorded)

theorem install_growth (context : plan.packet.context = legacy.core.erased.current.context) :
    GeneralNominalCenteredHeadMatStepTrustedGrowth.Growth legacy (installLegacy legacy plan) := by
  refine ⟨rfl,rfl,fun _ h => List.mem_append_left _ h,fun _ h => h,fun _ h => h,
    fun _ h => List.mem_append_left _ h,fun _ h => List.mem_cons_of_mem _ h,fun _ h => h,?_⟩
  intro atom member
  have old : atom ∈ plan.packet.context.state.ordinary := context.symm ▸ member
  exact List.mem_append_left _ old

theorem recorded_replay (plan : GeneralNominalCenters.Plan roles)
    (recorded : Recorded (GeneralNominalVersionedInstallation231.replayPlan plan).packet.context.state observation) :
    Recorded plan.packet.context.state observation := by
  cases recorded with
  | scalar slot base same => exact Recorded.scalar (snapshot := plan.packet.context.state) slot base same
  | structural slot kind children same => exact Recorded.structural (snapshot := plan.packet.context.state) slot kind children same
  | nominal slot descriptor same => exact Recorded.nominal (snapshot := plan.packet.context.state) slot descriptor same

theorem install_cache (context : plan.packet.context = legacy.core.erased.current.context)
    (valid : CacheSound legacy legacy.core.erased.current.context.state) :
    CacheSound (installLegacy legacy plan) (installLegacy legacy plan).core.erased.current.context.state := by
  apply GeneralNominalCenteredHeadMatStepTrustedGrowth.cache (install_growth context)
  intro observation recorded
  exact valid observation (context ▸ recorded_replay plan recorded)

theorem installed_cache (snapshot : effect.snapshot = state.core)
    (valid : CacheSound state.legacy state.core.erased.current.context.state) :
    CacheSound (install state effect).legacy (install state effect).core.erased.current.context.state :=
  install_cache (effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)) valid

end Yulang.GeneralNominalVersionedCache232
