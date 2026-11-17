import Yulang.GeneralNominalRebaseOperationalOwners242
namespace Yulang.GeneralNominalRebaseBirthWitness242
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseGenealogy242 GeneralNominalRebaseInstall242
open GeneralNominalRebaseOperational242
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
variable {roles : Roles.RoleDecls} {before after : Journal.State roles}

def Enumerated (registry : Registry) (seed root budget : Nat) (state : Journal.State roles) : Prop :=
 ∀ site ∈ state.core.sites, site.occurrence.identity ∈ GeneralNominalInvocationAncestry.frontier registry seed root budget

theorem step_enumerated
 (recorded : GeneralNominalVersionedMixedTrace235.Registered before root)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry before.core.erased.current.context.interpretation)
 (seed_eq : before.core.erased.current.context.state.seed = seed)
 (interpretation_eq : before.core.erased.current.context.interpretation = interpretation)
 (bounded : BoundedState registry seed root.identity budget (algebra registry.constructors interpretation) (view before))
 (known : Enumerated registry seed root.identity budget before)
 (action : Kernel.Step registry root before after) : Enumerated registry seed root.identity budget after := by
 have simulated := step_trace recorded covered seed_eq interpretation_eq action
 obtain ⟨focus,generated,action⟩ := action
 cases action with
 | administrative action =>
   cases action with
   | enqueue linked absent =>
     obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered recorded generated
     exact False.elim (absent site member same)
   | equate | refresh | reobserve => exact known
 | refresh | merge => exact known
 | install effect enabled novel =>
   obtain ⟨model,common⟩ := enabled.common
   have valid := (GeneralNominalVersionedInstall232.install_models enabled.snapshot_eq).mpr common
   exact enumerated simulated bounded ⟨model,valid⟩

theorem trace_enumerated {root : Occurrence roles}
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Kernel.Step registry root) (GeneralNominalVersionedJournal232.initial context root) after) :
 Enumerated registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels) after := by
 induction path with
 | refl =>
   intro site member
   have eq : site = rootSite context.state.seed root := List.mem_singleton.mp member
   subst site
   exact GeneralNominalInvocationAncestry.bounded_enumerated .root (Nat.zero_le _)
 | @tail before after path action ih =>
   have growth := GeneralNominalVersionedMixedGrowth234.steps path
   have ready := GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path
   have coverage : GeneralNominalCenteredHeadWFSource.Coverage registry before.core.erased.current.context.interpretation := by
     rw [growth.interpretation]
     exact covered
   exact step_enumerated ready.1 coverage growth.seed growth.interpretation
     (GeneralNominalRebaseOperationalOwners242.mixed_bounded metadata point ground covered path) ih action

theorem source_owners
 (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root after) :
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
 have all := trace_enumerated (registry := GeneralNominalCenteredHeadAllocEncoding.registry registry) source.metadata.1 point ground (GeneralNominalCenteredHeadAllocEncoding.coverage coverage)
   (GeneralNominalPointErasure240.steps_old path)
 intro site member declaration visible
 exact GeneralNominalRebaseOwnerUniverse242.mem_owners (all site member) visible
end Yulang.GeneralNominalRebaseBirthWitness242
