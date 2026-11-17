import Yulang.GeneralNominalVersionedMixedGrowth234
import Yulang.GeneralNominalVersionedMixedBoundary234
import Yulang.GeneralDictionaryDefaultCache208
set_option backward.isDefEq.respectTransparency false

/-! Inherited trusted cache validity along the full versioned kernel.
This proves preservation of existing observation justifications, not
completeness of new-effect-based trusted slices. -/
namespace Yulang.GeneralNominalVersionedMixedKernelCache234
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedMixedObservations233
open GeneralNominalVersionedMixedGrowth234
open GeneralNominalCenteredHeadMatStepTrustedGrowth (Growth)

def Valid (state : State roles) : Prop := CacheSound state state.core.erased.current.context.state

theorem administrative_cache (action : Administrative before focus after) (valid : Valid before) : Valid after := by
  apply GeneralNominalVersionedMixedCache233.cache (administrative action)
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
    exact GeneralNominalVersionedMixedCache233.install_cache enabled.snapshot_eq valid
  | merge first last one two same novel =>
    apply GeneralNominalVersionedMixedCache233.cache
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
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedBoundary234.boundary roles) registry root state) : Valid state := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  exact steps_cache path (legacy_cache (GeneralDictionaryDefaultCache208.initial_valid context root))

end Yulang.GeneralNominalVersionedMixedKernelCache234
