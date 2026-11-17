import Yulang.GeneralNominalRebaseLiveLabels241
import Yulang.GeneralNominalRebaseOwnerBack241
namespace Yulang.GeneralNominalRebaseProtectedLive241
open GeneralNominalCenters
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseLiveLabels241
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {sites : List (Site roles)} {pool : List Nat}
variable {oldModels newModels : Assignment → Prop}

theorem centers (centerSupport : ∀ site ∈ sites, ∀ index, site.center index ∈ pool)
 (same : Agree pool first last) : CentersAgree sites first last := by
 intro site member index
 rw [same (site.center index) (centerSupport site member index)]
 exact ⟨subtype_refl _,subtype_refl _⟩

theorem back_extension
 (centerSupport : ∀ site ∈ sites, ∀ index, site.center index ∈ pool)
 (extension : ∀ newModel : Assignment, newModels newModel →
   ∃ oldModel, oldModels oldModel ∧ Agree pool oldModel newModel) :
 BackExtension sites oldModels newModels := by
 intro model valid
 obtain ⟨previous,oldValid,same⟩ := extension model valid
 exact ⟨previous,oldValid,centers centerSupport same⟩

theorem bounded_models
 (centerSupport : ∀ site ∈ sites, ∀ index, site.center index ∈ pool)
 (extension : ∀ newModel : Assignment, newModels newModel →
   ∃ oldModel, oldModels oldModel ∧ Agree pool oldModel newModel)
 (known : ∀ oldModel, oldModels oldModel → Bounded registry seed root budget semantics sites oldModel) :
 ∀ newModel, newModels newModel → Bounded registry seed root budget semantics sites newModel :=
 all_models (back_extension centerSupport extension) known
end Yulang.GeneralNominalRebaseProtectedLive241
