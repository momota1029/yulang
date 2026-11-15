import Yulang.GeneralNominalCenteredHeadMatHeadReadback
import Yulang.GeneralDictionaryDefaultEnumeration208

/-! Retrospective ancestry for the unrestricted total-materialization Step.
The remaining producer is local head readback; no trace bound is assumed. -/
namespace Yulang.GeneralDictionaryDefaultAncestry208
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208
open GeneralNominalCenteredHeadMatSemanticLabels
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalInvocationAncestry (AtDepth child_identity)
open GeneralNominalCenteredTrace (clauseChild_mem)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}

/-- A local producer for the actual enabled installation. Its conclusion
contains finite captured meanings and a head comparison, with no ancestry. -/
def EnabledHeadReadback (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state →
    ∀ effect, Installable registry state effect → effect.plan.packet.declaration.requirements ≠ [] →
    ∀ model, Models state model → GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model →
    ∀ parentLabels, Inputs (algebra registry.constructors context.interpretation) model effect.plan.input parentLabels →
      ∃ capture, Captures effect.plan model capture ∧
        mass (substArgs (images capture) (normalizeArgs effect.plan.packet.declaration.head)) ≤ mass parentLabels

theorem sites_bounded
    (production : EnabledHeadReadback registry context root)
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
      exact GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs point ground valid.1
  | @tail before after path step ih =>
      have restrict : ∀ model, Models after model → Models before model := fun _ valid => stepModels step valid
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,member,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
                (GeneralDictionaryDefaultTrace208.registered_trace path) generated
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
          have branch := ((install_models enabled.snapshot_eq).mp valid).2.1
          obtain ⟨depth,parentLabels,parent,parentInputs,bounded⟩ := ih model old effect.plan.input current.center_recorded
          change site ∈ before.core.sites ++ effect.plan.emitted at member
          rcases List.mem_append.mp member with prior | added
          · exact ih model old site prior
          · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
            have visible : effect.plan.packet.declaration ∈ effect.plan.packet.registry.declarations :=
              current.registry_eq ▸ current.visible
            have seed : effect.plan.packet.context.state.seed = context.state.seed := by
              rw [current.context_eq]
              exact config.1
            have successor := child_identity effect.plan.packet _
              (clauseChild_mem effect.plan.packet clause.val clause.property
                (effect.plan.packet.checked.signature.2.2.2 clause.val clause.property)) visible
            simp only [current.registry_eq,seed] at successor
            obtain ⟨capture,captures,headBound⟩ := production before path effect enabled
              (List.ne_nil_of_mem clause.property) model old branch parentLabels parentInputs
            have covered := (coverage.1 effect.plan.packet.declaration current.visible).2.1 clause.val clause.property |>.1
            have childCoverage : GeneralNominalCenteredHeadWFSource.PatternsCovered effect.plan.packet.registry.constructors
                effect.plan.packet.context.interpretation clause.val.arguments := by
              rw [current.registry_eq,current.context_eq,config.2.2]
              exact covered
            have child := child_inputs branch captures clause.property
              (effect.plan.packet.checked.signature.2.2.2 clause.val clause.property) childCoverage
            simp only [current.registry_eq,current.context_eq,config.2.2] at child
            rw [effect.plan.input_exact] at parent
            refine ⟨depth+1,labels capture clause.val,.child parent successor,child,?_⟩
            have strict := bounded_label_descent effect.plan.packet.checked clause.property capture headBound
            omega

theorem installed_depth_bound
    (production : EnabledHeadReadback registry context root)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    InstalledDepthBound registry context root (mass rootLabels) := by
  intro state path effect _ enabled _
  obtain ⟨model,valid,_⟩ := enabled.common
  obtain ⟨depth,labels,ancestry,_,bounded⟩ := sites_bounded production source point ground coverage path
    model valid effect.plan.input (frame enabled).center_recorded
  exact ⟨depth,by omega,by simpa only [effect.plan.input_exact] using ancestry⟩

theorem head_readback : EnabledHeadReadback registry context root := by
  intro state path effect enabled nonempty model _valid branch labels known
  have current := frame enabled
  have configured := configuration_trace path
  have interpretation : effect.plan.packet.context.interpretation = context.interpretation := by
    rw [current.context_eq]; exact configured.2.2
  apply GeneralNominalCenteredHeadMatHeadReadback.readback current nonempty branch
  simpa only [current.registry_eq,interpretation] using known

theorem ground_depth_bound
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    InstalledDepthBound registry context root (mass rootLabels) :=
  installed_depth_bound head_readback source point ground coverage

end Yulang.GeneralDictionaryDefaultAncestry208
