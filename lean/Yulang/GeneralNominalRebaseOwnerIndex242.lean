import Yulang.GeneralNominalRebaseBirthWitness242
namespace Yulang.GeneralNominalRebaseOwnerIndex242
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseInstall242
open GeneralNominalRebaseOwnerUniverse242 (owners)
open GeneralNominalRebaseStore241 (Owner)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : Journal.State roles}

def ownerAt (registry : Registry) (seed root budget : Nat) (index : Fin (owners registry seed root budget).length) : Owner :=
 (owners registry seed root budget).get index

theorem indexed (member : owner ∈ owners registry seed rootIdentity budget) :
 ∃ index, ownerAt registry seed rootIdentity budget index = owner := List.get_of_mem member

theorem source_generated
 (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 ∃ context labels, GeneralNominalSourceFormation.InitialSource registry context root ∧
   GeneralNominalGroundAccessibility.GroundRoots context root labels ∧
   ∀ focus, GeneralNominalSaturationState.Generated state.core.erased.current root focus →
   ∀ declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∃ index, ownerAt (GeneralNominalCenteredHeadAllocEncoding.registry registry) context.state.seed
     root.identity (GeneralNominalPatersonLineage.mass labels) index = (focus.identity,declaration.id) := by
 obtain ⟨context,labels,source,ground,contained⟩ := GeneralNominalRebaseBirthWitness242.source_owners path
 have oldPath : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state := by
   obtain ⟨start,initial,steps⟩ := path
   exact ⟨start,initial,GeneralNominalPointErasure240.steps_old steps⟩
 refine ⟨context,labels,source,ground,?_⟩
 intro focus generated declaration visible
 obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_center oldPath generated
 have found := indexed (contained site member declaration visible)
 simpa only [same] using found

theorem fixed_generated
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (visible : declaration ∈ registry.declarations) :
 ∃ index, ownerAt registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels) index =
   (focus.identity,declaration.id) := by
 have old := GeneralNominalPointErasure240.steps_old path
 have invariant := GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) old
 obtain ⟨raw,present,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered invariant.1 generated
 obtain ⟨center,member,equal⟩ := invariant.2.2 raw present
 have bounded := GeneralNominalRebaseBirthWitness242.trace_enumerated metadata point ground covered old
 have found := indexed (GeneralNominalRebaseOwnerUniverse242.mem_owners (bounded center member) visible)
 have identity : center.occurrence.identity = focus.identity := congrArg Occurrence.identity (equal.trans same)
 simpa only [identity] using found
end Yulang.GeneralNominalRebaseOwnerIndex242
