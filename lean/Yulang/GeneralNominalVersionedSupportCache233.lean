import Yulang.GeneralNominalVersionedSupportGrowth233
set_option backward.isDefEq.respectTransparency false
/-! Current-snapshot cache transport for versioned installation and the new
observation certificates. These auxiliary laws do not change Kernel232's
legacy-certificate rules or assert observation availability. -/
namespace Yulang.GeneralNominalVersionedSupportCache233
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedGrowth233 (Monotone)
open GeneralNominalVersionedObservations233 (CacheSound)
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

theorem install_growth (snapshot : effect.snapshot = state.core) :
    Monotone state (GeneralNominalVersionedInstall232.install state effect) := by
  have context := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
  refine ⟨GeneralNominalVersionedCache232.install_growth context,
    fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_cons_of_mem _ h,
    fun _ h => List.mem_append_left _ h,?_,?_,?_⟩
  · change effect.plan.packet.context.state.seed = state.core.erased.current.context.state.seed
    rw [context]
  · change effect.plan.packet.context.state.constructors = state.core.erased.current.context.state.constructors
    rw [context]
  · change effect.plan.packet.context.interpretation = state.core.erased.current.context.interpretation
    rw [context]

theorem install_cache (snapshot : effect.snapshot = state.core)
    (valid : CacheSound state state.core.erased.current.context.state) :
    CacheSound (GeneralNominalVersionedInstall232.install state effect)
      (GeneralNominalVersionedInstall232.install state effect).core.erased.current.context.state := by
  apply GeneralNominalVersionedSupportGrowth233.cache (install_growth snapshot)
  intro observation recorded
  have context := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
  exact valid observation (context ▸ GeneralNominalVersionedCache232.recorded_replay effect.plan recorded)

theorem refresh_growth (certificate : GeneralNominalVersionedObservations233.Refresh state context) :
    Monotone state (GeneralNominalVersionedRefresh232.refresh state context) :=
  ⟨⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
    fun _ h => h,fun _ h => certificate.refines.ordinary _ h⟩,
    fun _ h => h,fun _ h => h,fun _ h => h,
    certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩

theorem refresh_cache (certificate : GeneralNominalVersionedObservations233.Refresh state context) :
    CacheSound (GeneralNominalVersionedRefresh232.refresh state context) context.state :=
  GeneralNominalVersionedSupportGrowth233.cache (refresh_growth certificate) certificate.cache

theorem reobserve_growth (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    Monotone state (GeneralNominalVersionedRefresh232.reobserve state revision) :=
  ⟨⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
    fun _ h => h,fun _ h => h⟩,fun _ h => h,fun _ h => h,fun _ h => h,rfl,rfl,rfl⟩

theorem reobserve_cache {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}
    (certificate : GeneralNominalVersionedObservations233.Reobserve state revision) :
    CacheSound (GeneralNominalVersionedRefresh232.reobserve state revision) revision.snapshot :=
  GeneralNominalVersionedSupportGrowth233.cache (reobserve_growth revision) certificate.cache

end Yulang.GeneralNominalVersionedSupportCache233
