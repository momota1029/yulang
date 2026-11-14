import Yulang.GeneralNominalCenteredHeadStepProduction
import Yulang.GeneralNominalCenteredHeadStepTrace

/-! Retrospective center labels bound the depth of successor installations. -/
namespace Yulang.GeneralNominalCenteredHeadStepAncestry
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel GeneralNominalCenteredHeadStepProgress
open GeneralNominalCenteredHeadStepTrace
open GeneralNominalCenteredTrace (clauseChild_mem)
open GeneralNominalInvocationAncestry (AtDepth frontier bounded_enumerated child_identity allocationPool allocation_member)
open GeneralNominalGroundAccessibility (Inputs GroundRoots root_inputs)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
def InstalledDepthBound (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (limit : Nat) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state →
    ∀ plan : Plan roles, ∀ support,
      GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence →
      Installable registry state plan support →
      ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet →
      ∃ depth, depth ≤ limit ∧ AtDepth registry context.state.seed root.identity depth plan.packet.site.occurrence.identity

theorem sites_bounded
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels)
    (steps : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ model, Models state model → ∀ site ∈ state.core.sites,
      ∃ depth labels, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        Inputs context model site.observed labels ∧ depth + mass labels ≤ mass rootLabels := by
  induction steps with
  | refl =>
    intro model valid site member
    cases List.mem_singleton.mp member
    refine ⟨0,rootLabels,.root,?_,by omega⟩
    change Inputs context model (rootSite context.state.seed root).observed rootLabels
    rw [GeneralNominalCenteredPointSource.point_observed (rootSite context.state.seed root) point (point_center _ _)]
    exact root_inputs ground point model valid.1.1.1
  | @tail before after steps step ih =>
    have restrict := stepModels step
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := generated_registered steps generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve =>
        intro model valid site member
        exact ih model (restrict model valid) site member
    | refresh | merge =>
      intro model valid site member
      exact ih model (restrict model valid) site member
    | install plan support enabled novel =>
      intro model valid site member
      have oldValid := restrict model valid
      have config := configuration_trace steps
      have branch := ((install_models enabled model).mp valid).2.1
      obtain ⟨depth,labels,parent,parentInputs,bounded⟩ := ih model oldValid plan.input enabled.frame.center_recorded
      change site ∈ before.core.sites ++ plan.emitted at member
      rcases List.mem_append.mp member with old | added
      · exact ih model oldValid site old
      · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
        have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
          simpa only [enabled.frame.registry_eq] using enabled.frame.visible
        have seed : plan.packet.context.state.seed = context.state.seed := by
          rw [enabled.frame.context_eq]; exact config.1
        have successor := child_identity plan.packet _ (clauseChild_mem plan.packet clause.val clause.property
          (plan.packet.checked.signature.2.2.2 clause.val clause.property)) visible
        simp only [enabled.frame.registry_eq,seed] at successor
        have nonempty : plan.packet.declaration.requirements ≠ [] := by
          exact List.ne_nil_of_mem clause.property
        obtain ⟨capture,headBound,children⟩ := GeneralNominalCenteredHeadStepProduction.production before plan enabled
          (by rw [enabled.frame.context_eq]; exact config.2.1) (by rw [enabled.frame.context_eq]; exact config.2.2)
          nonempty oldValid branch parentInputs
        rw [plan.input_exact] at parent
        refine ⟨depth+1,substArgs capture (normalizeArgs clause.val.arguments),.child parent successor,
          children clause.val clause.property _,?_⟩
        have strict := GeneralPatternConservativeSubstitution.checked_normalized_descent
            plan.packet.checked clause.val clause.property capture
        change mass (substArgs capture (normalizeArgs clause.val.arguments)) <
          mass (substArgs capture (normalizeArgs plan.packet.declaration.head)) at strict
        omega

theorem installed_depth_bound
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels) :
    InstalledDepthBound registry context root (mass rootLabels) := by
  intro state steps plan support generated enabled novel
  obtain ⟨model,valid,_⟩ := enabled.common
  obtain ⟨depth,labels,ancestry,_,bounded⟩ := sites_bounded point ground steps model valid plan.input enabled.frame.center_recorded
  refine ⟨depth,by omega,?_⟩
  simpa only [plan.input_exact] using ancestry

theorem installed_parents_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
    (enabled : Installable registry state plan support)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet)
    :
    plan.packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity limit := by
  obtain ⟨depth,small,ancestry⟩ := bound state path plan support generated enabled novel
  exact bounded_enumerated ancestry small

theorem reservations_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
    (enabled : Installable registry state plan support)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet)
    :
    GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity ⊆
      allocationPool registry context.state.seed (frontier registry context.state.seed root.identity limit) := by
  intro identity member
  obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
  have seed : plan.packet.context.state.seed = context.state.seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) enabled.frame.context_eq).trans
    (configuration_trace path).1
  simpa only [GeneralNominalAllocation.source,seed,enabled.frame.registry_eq] using
    allocation_member (seed := context.state.seed) _ (installed_parents_finite bound path generated enabled novel)
      key (enabled.frame.registry_eq ▸ present)

end Yulang.GeneralNominalCenteredHeadStepAncestry
