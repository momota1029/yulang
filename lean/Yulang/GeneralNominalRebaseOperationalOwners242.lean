import Yulang.GeneralNominalRebaseOperational242
import Yulang.GeneralNominalRebaseGround242
import Yulang.GeneralNominalPointErasure240
import Yulang.GeneralNominalPointSourceBoundary240
namespace Yulang.GeneralNominalRebaseOperationalOwners242
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseGenealogy242 GeneralNominalRebaseInstall242
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {after : Journal.State roles}

theorem initial_bounded
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels) :
 BoundedState registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels)
   (algebra registry.constructors context.interpretation)
   (view (GeneralNominalVersionedJournal232.initial context root)) := by
 have known : ∀ model, GeneralNominalVersionedJournal232.Models
     (GeneralNominalVersionedJournal232.initial context root) model →
     GeneralNominalCenteredHeadMatSemanticLabels.Inputs
       (algebra registry.constructors context.interpretation) model (rootSite context.state.seed root) labels := by
   intro model valid
   rw [metadata]
   exact GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs point ground
     ((GeneralNominalVersionedJournal232.initial_models context root model).mp valid).1
 exact root_bounded labels known

theorem mixed_bounded
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) after) :
 BoundedState registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels)
   (algebra registry.constructors context.interpretation) (view after) :=
 trace_bounded (GeneralNominalRebaseOperational242.trace context covered path) (initial_bounded metadata point ground)

theorem point_owners
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) after)
 (inhabited : ∃ model, GeneralNominalVersionedJournal232.Models after model) :
 ∀ site ∈ after.core.sites, ∀ declaration ∈ registry.declarations,
   (site.occurrence.identity,declaration.id) ∈ GeneralNominalRebaseOwnerUniverse242.owners registry context.state.seed
     root.identity (GeneralNominalPatersonLineage.mass labels) := by
 intro site member declaration visible
 exact GeneralNominalRebaseOwnerUniverse242.trace_owner
   (GeneralNominalRebaseOperational242.trace context covered (GeneralNominalPointErasure240.steps_old path))
   (initial_bounded metadata point ground) inhabited member visible

theorem source_owners
 (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root after)
 (inhabited : ∃ model, GeneralNominalVersionedJournal232.Models after model) :
 ∃ context labels, GeneralNominalSourceFormation.InitialSource registry context root ∧
   GeneralNominalGroundAccessibility.GroundRoots context root labels ∧
   ∀ site ∈ after.core.sites, ∀ declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   (site.occurrence.identity,declaration.id) ∈ GeneralNominalRebaseOwnerUniverse242.owners
     (GeneralNominalCenteredHeadAllocEncoding.registry registry) context.state.seed
     root.identity (GeneralNominalPatersonLineage.mass labels) := by
 obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
 subst first
 subst legacy
 refine ⟨context,labels,source,ground,?_⟩
 exact point_owners source.metadata.1 point ground (GeneralNominalCenteredHeadAllocEncoding.coverage coverage) path inhabited
end Yulang.GeneralNominalRebaseOperationalOwners242
