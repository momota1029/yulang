import Yulang.GeneralNominalCenteredHeadStepProgress

/-! Configuration and registration along the successor relation. -/
namespace Yulang.GeneralNominalCenteredHeadStepTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel GeneralNominalCenteredHeadStepProgress
open GeneralNominalCenteredTrace (clauseChild_mem)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
theorem configuration_step (step : Step registry root before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
    | enqueue | equate | reobserve => exact ⟨rfl,rfl,rfl⟩
  | refresh focus context certificate source member unknown known =>
    exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
  | merge => exact ⟨rfl,rfl,rfl⟩
  | install plan support enabled novel =>
    change plan.packet.context.state.seed = before.core.erased.current.context.state.seed ∧
      plan.packet.context.state.constructors = before.core.erased.current.context.state.constructors ∧
      plan.packet.context.interpretation = before.core.erased.current.context.interpretation
    rw [enabled.frame.context_eq]
    exact ⟨rfl,rfl,rfl⟩

theorem configuration_trace (path : B4Target.Steps (Step registry root) before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail path step ih =>
    have next := configuration_step step
    exact ⟨next.1.trans ih.1,next.2.1.trans ih.2.1,next.2.2.trans ih.2.2⟩


theorem centered_site_registered
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.sites, ∃ raw ∈ state.core.erased.current.sites, raw.occurrence = site.occurrence := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨_,List.mem_singleton_self _,rfl⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      intro site member
      obtain ⟨raw,registered,same⟩ := ih site member
      exact ⟨raw,(GeneralNominalReobservationSteps.at_extends
        (GeneralNominalSupportSteps.administrative_old action)).journal.sites raw registered,same⟩
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro site member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨raw,registered,same⟩ := ih site old
        exact ⟨raw,List.mem_append_left _ registered,same⟩
      · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
        refine ⟨GeneralNominalSharedEmission.childSite plan.packet _,List.mem_append_right _ ?_,rfl⟩
        apply List.mem_map.mpr
        refine ⟨_,?_,rfl⟩
        exact clauseChild_mem plan.packet clause.val clause.property _


end Yulang.GeneralNominalCenteredHeadStepTrace
