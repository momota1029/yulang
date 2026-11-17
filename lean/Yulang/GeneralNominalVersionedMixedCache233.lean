import Yulang.GeneralNominalVersionedMixedObservations233
import Yulang.GeneralNominalVersionedSupportCache233
set_option backward.isDefEq.respectTransparency false
/-! Joint legacy/versioned justification transport. Fixed-snapshot preservation
and current-snapshot installation/new-certificate laws are distinguished. -/
namespace Yulang.GeneralNominalVersionedMixedCache233
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedGrowth233 (Monotone)
open GeneralNominalVersionedMixedObservations233
variable {roles : Roles.RoleDecls} {before after state : State roles} {effect : Effect roles}

theorem justified (growth : Monotone before after) (given : Justified before observation) : Justified after observation := by
  obtain ⟨oldFacts,newFacts,oldTrusted,newTrusted,sound⟩ := given
  exact ⟨oldFacts,newFacts,GeneralNominalCenteredHeadMatStepTrustedGrowth.trusted growth.legacy oldTrusted,
    GeneralNominalVersionedSupportGrowth233.trusted growth newTrusted,
    fun model old current => sound model
      ((GeneralNominalCenteredHeadMatStepTrustedGrowth.slice_models growth.legacy).mp old)
      ((GeneralNominalVersionedSupportGrowth233.slice_models growth).mp current)⟩

theorem cache (growth : Monotone before after) (given : CacheSound before snapshot) : CacheSound after snapshot :=
  fun observation recorded => justified growth (given observation recorded)

theorem install_cache (snapshot : effect.snapshot = state.core)
    (valid : CacheSound state state.core.erased.current.context.state) :
    CacheSound (GeneralNominalVersionedInstall232.install state effect)
      (GeneralNominalVersionedInstall232.install state effect).core.erased.current.context.state := by
  apply cache (GeneralNominalVersionedSupportCache233.install_growth snapshot)
  intro observation recorded
  have context := effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
  exact valid observation (context ▸ GeneralNominalVersionedCache232.recorded_replay effect.plan recorded)

theorem refresh_growth (certificate : Refresh state context) :
    Monotone state (GeneralNominalVersionedRefresh232.refresh state context) :=
  ⟨⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
    fun _ h => h,fun _ h => certificate.refines.ordinary _ h⟩,
    fun _ h => h,fun _ h => h,fun _ h => h,
    certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩

theorem refresh_cache (certificate : Refresh state context) :
    CacheSound (GeneralNominalVersionedRefresh232.refresh state context) context.state :=
  cache (refresh_growth certificate) certificate.cache

theorem reobserve_cache {revision : GeneralNominalReobservationSteps.Revision state.core.erased.current}
    (certificate : Reobserve state revision) :
    CacheSound (GeneralNominalVersionedRefresh232.reobserve state revision) revision.snapshot :=
  cache (GeneralNominalVersionedSupportCache233.reobserve_growth revision) certificate.cache

theorem legacy_kernel_step (action : GeneralNominalVersionedKernel232.Step registry root before after)
    (given : CacheSound before snapshot) : CacheSound after snapshot :=
  cache (GeneralNominalVersionedGrowth233.step action) given

theorem legacy_kernel_steps (path : B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root) before after)
    (given : CacheSound before snapshot) : CacheSound after snapshot :=
  cache (GeneralNominalVersionedGrowth233.steps path) given

end Yulang.GeneralNominalVersionedMixedCache233
