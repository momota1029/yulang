import Yulang.GeneralNominalRebaseGenealogy242
import Yulang.GeneralNominalRebaseStore241
namespace Yulang.GeneralNominalRebaseOwnerUniverse242
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalRebaseGenealogy242
open GeneralNominalRebaseStore241 (Owner)

def owners (registry : Registry) (seed root budget : Nat) : List Owner :=
 (GeneralNominalInvocationAncestry.frontier registry seed root budget).flatMap
   (fun identity => registry.declarations.map (fun declaration => (identity,declaration.id)))

theorem mem_owners
 (identity : occurrence ∈ GeneralNominalInvocationAncestry.frontier registry seed root budget)
 (visible : declaration ∈ registry.declarations) :
 (occurrence,declaration.id) ∈ owners registry seed root budget :=
 List.mem_flatMap.mpr ⟨occurrence,identity,List.mem_map.mpr ⟨declaration,visible,rfl⟩⟩

theorem trace_owner
 (path : B4Target.Steps (Step registry seed semantics) before after)
 (known : BoundedState registry seed root budget semantics before)
 (inhabited : ∃ model, after.models model)
 (member : site ∈ after.sites) (visible : declaration ∈ registry.declarations) :
 (site.occurrence.identity,declaration.id) ∈ owners registry seed root budget :=
 mem_owners (enumerated path known inhabited site member) visible

theorem plan_owner {roles : Roles.RoleDecls} {before after : State roles}
 (path : B4Target.Steps (Step registry seed semantics) before after)
 (known : BoundedState registry seed root budget semantics before)
 (inhabited : ∃ model, after.models model)
 (plan : Plan roles)
 (member : plan.input ∈ after.sites) (visible : plan.packet.declaration ∈ registry.declarations) :
 (plan.input.occurrence.identity,plan.packet.declaration.id) ∈ owners registry seed root budget :=
 trace_owner path known inhabited member visible

theorem root_trace_owner
 (path : B4Target.Steps (Step registry seed semantics) (⟨[initialSite],models⟩ : State roles) after)
 (known : ∀ model, models model → GeneralNominalCenteredHeadMatSemanticLabels.Inputs semantics model initialSite labels)
 (inhabited : ∃ model, after.models model)
 (member : site ∈ after.sites) (visible : declaration ∈ registry.declarations) :
 (site.occurrence.identity,declaration.id) ∈ owners registry seed initialSite.occurrence.identity
   (GeneralNominalPatersonLineage.mass labels) :=
 trace_owner path (root_bounded labels known) inhabited member visible
end Yulang.GeneralNominalRebaseOwnerUniverse242
