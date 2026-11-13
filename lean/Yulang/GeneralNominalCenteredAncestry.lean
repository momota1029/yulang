import Yulang.GeneralNominalCenteredProduction
import Yulang.GeneralNominalCenteredTrace
import Yulang.GeneralNominalCenteredPointSource

/-! Retrospective finite labels bound the birth depth of every centered site.
The witness model includes the center ledger, including at future installs. -/
namespace Yulang.GeneralNominalCenteredAncestry
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalCenteredTrace
open GeneralNominalInvocationAncestry (AtDepth frontier bounded_enumerated child_identity allocationPool allocation_member)
open GeneralNominalGroundAccessibility (Inputs GroundRoots root_inputs)
open GeneralNominalPatersonLineage (mass)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def InstalledDepthBound (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (limit : Nat) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state →
    ∀ plan : Plan roles, ∀ support,
      GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet → PacketGuard state plan support →
      ∃ depth, depth ≤ limit ∧ AtDepth registry context.state.seed root.identity depth plan.packet.site.occurrence.identity

theorem sites_bounded
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels)
    (steps : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ model, Models state model → ∀ site ∈ state.sites,
      ∃ depth labels, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        Inputs context model site.observed labels ∧ depth + mass labels ≤ mass rootLabels := by
  induction steps with
  | refl =>
    intro model valid site member
    cases List.mem_singleton.mp member
    refine ⟨0,rootLabels,.root,?_,by omega⟩
    change Inputs context model (rootSite context.state.seed root).observed rootLabels
    rw [GeneralNominalCenteredPointSource.point_observed (rootSite context.state.seed root) point (point_center _ _)]
    exact root_inputs ground point model valid.1.1
  | @tail before after steps step ih =>
    have restrict := step_models step
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
    | install plan support enabled novel guard =>
      intro model valid site member
      have oldValid := restrict model valid
      have config := configuration_trace steps
      have branch := ((install_models (support := support) enabled.1.2.1 model).mp valid).2
      obtain ⟨depth,labels,parent,parentInputs,bounded⟩ := ih model oldValid plan.input guard.1
      change site ∈ before.sites ++ plan.emitted at member
      rcases List.mem_append.mp member with old | added
      · exact ih model oldValid site old
      · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
        have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
          simpa only [enabled.1.1] using enabled.1.2.2.2.1
        have seed : plan.packet.context.state.seed = context.state.seed := by
          rw [enabled.1.2.1]; exact config.1
        have successor := child_identity plan.packet _ (clauseChild_mem plan.packet clause.val clause.property
          (plan.packet.checked.signature.2.2.2 clause.val clause.property)) visible
        simp only [enabled.1.1,seed] at successor
        have nonempty : plan.packet.declaration.requirements ≠ [] := by
          exact List.ne_nil_of_mem clause.property
        obtain ⟨capture,headBound,children⟩ := GeneralNominalCenteredProduction.production before.erased.current plan enabled
          (by rw [enabled.1.2.1]; exact config.2.1) (by rw [enabled.1.2.1]; exact config.2.2)
          nonempty oldValid.1 branch parentInputs
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
  intro state steps plan support generated enabled novel guard
  obtain ⟨model,valid,_⟩ := guard.2.2.2.2.2.2
  obtain ⟨depth,labels,ancestry,_,bounded⟩ := sites_bounded point ground steps model valid plan.input guard.1
  refine ⟨depth,by omega,?_⟩
  simpa only [plan.input_exact] using ancestry

theorem installed_parents_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet)
    (guard : PacketGuard state plan support) :
    plan.packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity limit := by
  obtain ⟨depth,small,ancestry⟩ := bound state path plan support generated enabled novel guard
  exact bounded_enumerated ancestry small

theorem reservations_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet)
    (guard : PacketGuard state plan support) :
    GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity ⊆
      allocationPool registry context.state.seed (frontier registry context.state.seed root.identity limit) := by
  intro identity member
  obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
  have seed : plan.packet.context.state.seed = context.state.seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) enabled.1.2.1).trans
    (configuration_trace path).1
  simpa only [GeneralNominalAllocation.source,seed,enabled.1.1] using
    allocation_member (seed := context.state.seed) _ (installed_parents_finite bound path generated enabled novel guard)
      key (enabled.1.1 ▸ present)

end Yulang.GeneralNominalCenteredAncestry
