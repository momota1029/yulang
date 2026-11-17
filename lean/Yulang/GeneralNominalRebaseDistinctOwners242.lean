import Yulang.GeneralNominalRebaseOwnerIndex242
namespace Yulang.GeneralNominalRebaseDistinctOwners242
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRebaseInstall242
open GeneralNominalRebaseStore241 (Owner)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : Journal.State roles}

theorem dedup_nodup (pool : List Owner) : pool.eraseDups.Nodup := by
 cases pool with
 | nil => exact List.nodup_nil
 | cons first rest =>
   rw [List.eraseDups_cons]
   apply List.nodup_cons.mpr
   exact ⟨by simp,dedup_nodup (rest.filter (fun owner => !owner == first))⟩
termination_by pool.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

def owners (registry : Registry) (seed root budget : Nat) : List Owner :=
 (GeneralNominalRebaseOwnerUniverse242.owners registry seed root budget).eraseDups

theorem mem_owners : owner ∈ owners registry seed rootIdentity budget ↔
 owner ∈ GeneralNominalRebaseOwnerUniverse242.owners registry seed rootIdentity budget := List.mem_eraseDups

theorem nodup (registry : Registry) (seed root budget : Nat) : (owners registry seed root budget).Nodup := dedup_nodup _

def ownerAt (registry : Registry) (seed root budget : Nat) (index : Fin (owners registry seed root budget).length) : Owner :=
 (owners registry seed root budget).get index

theorem injective (registry : Registry) (seed root budget : Nat)
 (first last : Fin (owners registry seed root budget).length)
 (same : ownerAt registry seed root budget first = ownerAt registry seed root budget last) : first = last := by
 apply Fin.ext
 exact (nodup registry seed root budget).getElem_inj.mp same

theorem indexed (member : owner ∈ GeneralNominalRebaseOwnerUniverse242.owners registry seed rootIdentity budget) :
 ∃ index, ownerAt registry seed rootIdentity budget index = owner := List.get_of_mem (mem_owners.mpr member)

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
 obtain ⟨index,equal⟩ := GeneralNominalRebaseOwnerIndex242.fixed_generated metadata point ground covered path generated visible
 apply indexed
 rw [← equal]
 exact List.get_mem _ index

theorem source_generated
 (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 ∃ context labels, GeneralNominalSourceFormation.InitialSource registry context root ∧
   GeneralNominalGroundAccessibility.GroundRoots context root labels ∧
   ∀ focus, GeneralNominalSaturationState.Generated state.core.erased.current root focus →
   ∀ declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry registry).declarations,
   ∃ index, ownerAt (GeneralNominalCenteredHeadAllocEncoding.registry registry) context.state.seed
     root.identity (GeneralNominalPatersonLineage.mass labels) index = (focus.identity,declaration.id) := by
 obtain ⟨context,labels,source,ground,all⟩ := GeneralNominalRebaseOwnerIndex242.source_generated path
 refine ⟨context,labels,source,ground,?_⟩
 intro focus generated declaration visible
 obtain ⟨index,equal⟩ := all focus generated declaration visible
 apply indexed
 rw [← equal]
 exact List.get_mem _ index
end Yulang.GeneralNominalRebaseDistinctOwners242
