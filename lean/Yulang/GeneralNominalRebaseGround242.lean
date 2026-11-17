import Yulang.GeneralNominalRebaseOwnerUniverse242
import Yulang.GeneralNominalCenteredHeadMatSourceLabels
namespace Yulang.GeneralNominalRebaseGround242
open GeneralDeclarations GeneralNominalCenters GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRebaseGenealogy242
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)

theorem initial_bounded {roles : Roles.RoleDecls} {root : Occurrence roles}
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels) :
 BoundedState registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels)
   (algebra context.state.constructors context.interpretation)
   ⟨[rootSite context.state.seed root],GeneralNominalState.Models context.state⟩ :=
 root_bounded labels (fun _ valid => GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs point ground valid)

theorem trace_bounded_ground {roles : Roles.RoleDecls} {root : Occurrence roles} {after : State roles}
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (path : B4Target.Steps (Step registry context.state.seed (algebra context.state.constructors context.interpretation))
   (⟨[rootSite context.state.seed root],GeneralNominalState.Models context.state⟩ : State roles) after) :
 BoundedState registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels)
   (algebra context.state.constructors context.interpretation) after :=
 trace_bounded path (initial_bounded point ground)

theorem owner_ground {roles : Roles.RoleDecls} {root : Occurrence roles} {after : State roles} {site : Site roles}
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (path : B4Target.Steps (Step registry context.state.seed (algebra context.state.constructors context.interpretation))
   (⟨[rootSite context.state.seed root],GeneralNominalState.Models context.state⟩ : State roles) after)
 (inhabited : ∃ model, after.models model)
 (member : site ∈ after.sites) (visible : declaration ∈ registry.declarations) :
 (site.occurrence.identity,declaration.id) ∈ GeneralNominalRebaseOwnerUniverse242.owners registry context.state.seed
   root.identity (GeneralNominalPatersonLineage.mass labels) :=
 GeneralNominalRebaseOwnerUniverse242.trace_owner path (initial_bounded point ground) inhabited member visible
end Yulang.GeneralNominalRebaseGround242
