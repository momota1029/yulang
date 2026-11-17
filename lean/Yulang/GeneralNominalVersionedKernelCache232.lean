import Yulang.GeneralNominalVersionedCache232
import Yulang.GeneralNominalVersionedBoundary232
import Yulang.GeneralDictionaryDefaultCache208
set_option backward.isDefEq.respectTransparency false

/-! Inherited trusted cache validity along the full versioned kernel.
This proves preservation of existing observation justifications, not
completeness of new-effect-based trusted slices. -/
namespace Yulang.GeneralNominalVersionedKernelCache232
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedKernel232
open GeneralNominalCenteredHeadMatStepObservations
open GeneralNominalCenteredHeadMatStepTrustedGrowth (Growth)

def Valid (state : State roles) : Prop := CacheSound state.legacy state.core.erased.current.context.state

theorem administrative_growth (action : Administrative before focus after) : Growth before.legacy after.legacy := by
  cases action with
  | enqueue =>
    exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h,
      fun _ h => h,fun _ h => h,fun _ h => h⟩
  | refresh context certificate source member unknown known =>
    exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
      fun _ h => h,fun _ h => h,fun _ h => certificate.refines.ordinary _ h⟩
  | equate =>
    exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
      fun _ h => h,fun _ h => h,fun _ h => List.mem_append_left _ h⟩
  | reobserve =>
    exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
      fun _ h => h,fun _ h => h,fun _ h => h⟩

theorem at_growth (action : At registry before focus after) : Growth before.legacy after.legacy := by
  cases action with
  | administrative action => exact administrative_growth action
  | refresh focus context certificate source member unknown known =>
    exact administrative_growth (.refresh focus context certificate source member unknown known)
  | install effect enabled novel =>
    exact GeneralNominalVersionedCache232.install_growth
      (effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) enabled.snapshot_eq))
  | merge =>
    exact ⟨rfl,rfl,fun _ h => h,fun _ h => h,fun _ h => h,fun _ h => h,
      fun _ h => h,fun _ h => List.mem_cons_of_mem _ h,fun _ h => List.mem_append_left _ h⟩

theorem administrative_cache (action : Administrative before focus after) (valid : Valid before) : Valid after := by
  apply GeneralNominalCenteredHeadMatStepTrustedGrowth.cache (administrative_growth action)
  cases action with
  | enqueue => exact valid
  | refresh context certificate source member unknown known => exact certificate.cache
  | reobserve revision certificate improved => exact certificate.cache
  | equate => exact fun observation recorded => valid observation (GeneralDictionaryDefaultCache208.recorded_extend recorded)

theorem at_cache (action : At registry before focus after) (valid : Valid before) : Valid after := by
  cases action with
  | administrative action => exact administrative_cache action valid
  | refresh focus context certificate source member unknown known =>
    exact administrative_cache (.refresh focus context certificate source member unknown known) valid
  | install effect enabled novel =>
    exact GeneralNominalVersionedCache232.installed_cache enabled.snapshot_eq valid
  | merge first last one two same novel =>
    apply GeneralNominalCenteredHeadMatStepTrustedGrowth.cache
      (at_growth (registry := registry) (.merge first last one two same novel))
    exact fun observation recorded => valid observation
      (GeneralDictionaryDefaultCache208.recorded_extend recorded)

theorem step_cache (action : Step registry root before after) (valid : Valid before) : Valid after :=
  at_cache action.choose_spec.2 valid

theorem steps_cache (path : B4Target.Steps (Step registry root) before after) (valid : Valid before) : Valid after := by
  induction path with
  | refl => exact valid
  | tail _ action ih => exact step_cache action ih

theorem reachable_cache
    (path : B4TargetV8.Reachable (GeneralNominalVersionedBoundary232.boundary roles) registry root state) : Valid state := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  exact steps_cache path (GeneralDictionaryDefaultCache208.initial_valid context root)

end Yulang.GeneralNominalVersionedKernelCache232
