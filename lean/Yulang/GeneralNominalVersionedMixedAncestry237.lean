import Yulang.GeneralNominalVersionedChildLabels237
import Yulang.GeneralNominalVersionedMixedTrace235
import Yulang.GeneralDictionaryDefaultAncestry208
set_option backward.isDefEq.respectTransparency false
/-! Retrospective ground-label mass bounds on actual mixed installations.
This bounds invocation ancestry, not the number of content-addressed versions. -/
namespace Yulang.GeneralNominalVersionedMixedAncestry237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234 GeneralNominalVersionedInstall232
open GeneralNominalCenteredHeadMatSemanticLabels
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalInvocationAncestry (AtDepth child_identity)
open GeneralNominalCenteredTrace (clauseChild_mem)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}
theorem frame (enabled : Installable registry state effect) :
    GeneralNominalVersionedEvidence231.Frame registry state.core effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id effect.plan :=
  enabled.snapshot_eq ▸ enabled.registry_eq ▸ effect.frame

theorem configuration_step (step : Step registry root before after) :
    after.core.erased.current.context.state.seed = before.core.erased.current.context.state.seed ∧
    after.core.erased.current.context.state.constructors = before.core.erased.current.context.state.constructors ∧
    after.core.erased.current.context.interpretation = before.core.erased.current.context.interpretation := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
    | enqueue | equate | reobserve => exact ⟨rfl,rfl,rfl⟩
  | refresh focus context certificate source member unknown known =>
    exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
  | merge => exact ⟨rfl,rfl,rfl⟩
  | install effect enabled novel =>
    change effect.plan.packet.context.state.seed = before.core.erased.current.context.state.seed ∧
      effect.plan.packet.context.state.constructors = before.core.erased.current.context.state.constructors ∧
      effect.plan.packet.context.interpretation = before.core.erased.current.context.interpretation
    rw [(frame enabled).context_eq]
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

def InstalledDepthBound (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (limit : Nat) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state → ∀ effect,
    GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
    Installable registry state effect → ¬ Committed state effect.plan →
    ∃ depth, depth ≤ limit ∧ AtDepth registry context.state.seed root.identity depth effect.plan.packet.site.occurrence.identity

theorem sites_bounded
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ model, Models state model → ∀ site ∈ state.core.sites,
      ∃ depth labels, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        Inputs (algebra registry.constructors context.interpretation) model site labels ∧
        depth + mass labels ≤ mass rootLabels := by
  induction path with
  | refl =>
      intro model valid site member
      cases List.mem_singleton.mp member
      refine ⟨0,rootLabels,.root,?_,by omega⟩
      rw [source.metadata.1]
      exact GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs point ground valid.1.1
  | @tail before after path step ih =>
      have restrict : ∀ model, Models after model → Models before model := fun _ valid => step_models step valid
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
                (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
              exact False.elim (absent site member same)
          | refresh | equate | reobserve =>
              intro model valid site member
              exact ih model (restrict model valid) site member
      | refresh | merge =>
          intro model valid site member
          exact ih model (restrict model valid) site member
      | install effect enabled novel =>
          intro model valid site member
          have old := restrict model valid
          have current := frame enabled
          have config := configuration_trace path
          have interpretation : before.core.erased.current.context.interpretation = context.interpretation := config.2.2
          have branch := ((install_models enabled.snapshot_eq).mp valid).2.1
          obtain ⟨depth,parentLabels,parent,parentInputs,bounded⟩ := ih model old effect.plan.input current.center_recorded
          change site ∈ before.core.sites ++ GeneralNominalVersionedChildren232.emitted effect.plan at member
          rcases List.mem_append.mp member with prior | added
          · exact ih model old site prior
          · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
            have clauseMember := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
            have visible : effect.plan.packet.declaration ∈ effect.plan.packet.registry.declarations :=
              current.registry_eq ▸ current.visible
            have seed : effect.plan.packet.context.state.seed = context.state.seed := by
              rw [current.context_eq]
              exact config.1
            have successor := child_identity effect.plan.packet _
              (clauseChild_mem effect.plan.packet clause.val clauseMember
                (effect.plan.packet.checked.signature.2.2.2 clause.val clauseMember)) visible
            simp only [current.registry_eq,seed] at successor
            obtain ⟨capture,captures,headBound⟩ := GeneralNominalVersionedHeadReadback237.readback current
              (List.ne_nil_of_mem clauseMember) branch (by simpa only [current.registry_eq,current.context_eq,interpretation] using parentInputs)
            have covered := (coverage.1 effect.plan.packet.declaration current.visible).2.1 clause.val clauseMember |>.1
            have childCoverage : GeneralNominalCenteredHeadWFSource.PatternsCovered effect.plan.packet.registry.constructors
                effect.plan.packet.context.interpretation clause.val.arguments := by
              rw [current.registry_eq,current.context_eq,interpretation]
              exact covered
            have child := GeneralNominalVersionedChildLabels237.child_inputs branch captures clauseMember
              (effect.plan.packet.checked.signature.2.2.2 clause.val clauseMember) childCoverage
            simp only [current.registry_eq,current.context_eq,interpretation] at child
            rw [effect.plan.input_exact] at parent
            refine ⟨depth+1,labels capture clause.val,.child parent successor,child,?_⟩
            have strict := bounded_label_descent effect.plan.packet.checked clauseMember capture headBound
            omega

theorem installed_depth_bound
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    InstalledDepthBound registry context root (mass rootLabels) := by
  intro state path effect _ enabled _
  obtain ⟨model,valid,_⟩ := enabled.common
  obtain ⟨depth,labels,ancestry,_,bounded⟩ := sites_bounded source point ground coverage path
    model valid effect.plan.input (frame enabled).center_recorded
  exact ⟨depth,by omega,by simpa only [effect.plan.input_exact] using ancestry⟩


end Yulang.GeneralNominalVersionedMixedAncestry237
