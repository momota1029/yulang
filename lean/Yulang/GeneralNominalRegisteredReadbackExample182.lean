import Yulang.GeneralNominalRegisteredReadback182
import Yulang.GeneralNominalSiteOrigin182
import Yulang.GeneralNominalCenteredInstallExample

/-! An actual guarded installation exercises both child and named schema
readback. This source has an unknown child; ground-boundary membership is not
asserted. The path and the common model are supplied by checked constructions. -/
namespace Yulang.GeneralNominalRegisteredReadbackExample182
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredInstallExample
open GeneralNominalRegisteredReadback182

 theorem path : B4Target.Steps (Step registry root) initialState afterP :=
  .tail .refl stepP

 theorem registered : planP ∈ afterP.plans := List.mem_cons_self ..

 theorem modeled : Models afterP witness :=
  (install_models (state := initialState) (plan := planP) (support := []) rfl witness).mpr
    ⟨(point_initial_models context root (fun _ => rfl) witness).mpr witness_source,planP_holds⟩

 theorem emitted_registered : emittedChild ∈ afterP.sites := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨⟨childR,List.mem_singleton_self _⟩,by simp,rfl⟩

 theorem actual_origin :
    emittedChild = rootSite context.state.seed root ∨
      ∃ plan ∈ afterP.plans, emittedChild ∈ plan.emitted :=
  GeneralNominalSiteOrigin182.initial_site_origin path emittedChild emitted_registered

 theorem generated_witness : ∃ plan ∈ afterP.plans, emittedChild ∈ plan.emitted := by
  refine ⟨planP,registered,?_⟩
  exact List.mem_map.mpr ⟨⟨childR,List.mem_singleton_self _⟩,by simp,rfl⟩

 theorem child_readback :
    GeneralNominalOriginTerms.Same witness (.source 2) (.source (planP.binder 1)) := by
  apply registered_actual planP registered modeled (.child childR (List.mem_singleton_self _) childSignature)
    (⟨1,.source 2,.actual⟩ : GeneralNominalMaterialization.Use)
  · rw [childP_schema]
    exact List.mem_singleton_self _
  · rfl

 theorem named_readback :
    GeneralNominalOriginTerms.Same witness (.source 2) (.source (planP.binder 2)) := by
  apply registered_actual planP registered modeled .named
    (⟨2,.source 2,.actual⟩ : GeneralNominalMaterialization.Use)
  · rw [schemaP_exact]
    exact List.mem_cons_self ..
  · rfl

 theorem child_bounded : ∀ index,
    GeneralNominalCaptureMerges.Fits witness (emittedChild.occurrence.demand.arguments index)
      (witness (emittedChild.center index)).1 :=
  fun index => registered_site_fits emittedChild emitted_registered modeled index

end Yulang.GeneralNominalRegisteredReadbackExample182
