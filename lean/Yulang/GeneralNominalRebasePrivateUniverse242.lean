import Yulang.GeneralNominalRebaseDistinctOwners242
import Yulang.GeneralNominalRebaseNames241
import Yulang.GeneralNominalRebaseDefinitions241
namespace Yulang.GeneralNominalRebasePrivateUniverse242
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseInstall242
open GeneralNominalRebaseDefinitions241 (entries)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : Journal.State roles}

def names (registry : Registry) : List Nat := registry.declarations.flatMap Declaration.inputNames

def domain (registry : Registry) (seed root budget : Nat) : List Nat :=
 GeneralNominalRebaseNames241.domain seed (GeneralNominalRebaseDistinctOwners242.owners registry seed root budget) (names registry)

theorem name_mem (visible : declaration ∈ registry.declarations) (named : name ∈ declaration.inputNames) :
 name ∈ names registry := List.mem_flatMap.mpr ⟨declaration,visible,named⟩

theorem target_mem
 (owner : (invocation,declaration.id) ∈ GeneralNominalRebaseDistinctOwners242.owners registry seed rootIdentity budget)
 (visible : declaration ∈ registry.declarations)
 (member : entry ∈ entries seed invocation declaration.id bindings declaration.inputNames) :
 entry.1 ∈ domain registry seed rootIdentity budget := by
 obtain ⟨name,named,_,equal⟩ := (GeneralNominalRebaseDefinitions241.member_iff seed invocation declaration.id bindings declaration.inputNames).mp member
 rcases equal with rfl | rfl
 · exact GeneralNominalRebaseNames241.mem_universe (upper := false) owner (name_mem visible named)
 · exact GeneralNominalRebaseNames241.mem_universe (upper := true) owner (name_mem visible named)

theorem domain_length (registry : Registry) (seed root budget : Nat) :
 (domain registry seed root budget).length =
 (GeneralNominalRebaseDistinctOwners242.owners registry seed root budget).length * ((names registry).length * 2) :=
 GeneralNominalRebaseNames241.universe_length _ _ _

theorem fixed_targets
 (metadata : registry.constructors = context.state.constructors)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels)
 (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (visible : declaration ∈ registry.declarations)
 (member : entry ∈ entries context.state.seed focus.identity declaration.id bindings declaration.inputNames) :
 entry.1 ∈ domain registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass labels) := by
 obtain ⟨index,equal⟩ := GeneralNominalRebaseDistinctOwners242.fixed_generated metadata point ground covered path generated visible
 apply target_mem _ visible member
 rw [← equal]
 exact List.get_mem _ index

theorem source_targets
 (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 ∃ context labels, GeneralNominalSourceFormation.InitialSource registry context root ∧
   GeneralNominalGroundAccessibility.GroundRoots context root labels ∧
   ∀ focus, GeneralNominalSaturationState.Generated state.core.erased.current root focus →
   ∀ declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∀ bindings entry, entry ∈ entries context.state.seed focus.identity declaration.id bindings declaration.inputNames →
   entry.1 ∈ domain (GeneralNominalCenteredHeadAllocEncoding.registry registry) context.state.seed
     root.identity (GeneralNominalPatersonLineage.mass labels) := by
 obtain ⟨context,labels,source,ground,all⟩ := GeneralNominalRebaseDistinctOwners242.source_generated path
 refine ⟨context,labels,source,ground,?_⟩
 intro focus generated declaration visible bindings entry member
 obtain ⟨index,equal⟩ := all focus generated declaration visible
 apply target_mem _ visible member
 rw [← equal]
 exact List.get_mem _ index
end Yulang.GeneralNominalRebasePrivateUniverse242
