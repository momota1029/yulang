import Yulang.GeneralNominalVersionedMixedAncestry237
namespace Yulang.GeneralNominalOwnerCandidates252
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234 GeneralNominalVersionedInstall232
open GeneralNominalInvocationAncestry (frontier bounded_enumerated)
open GeneralNominalPatersonLineage (mass)

def owners (registry : Registry) (seed root limit : Nat) : List (Nat × Nat) :=
 (frontier registry seed root limit).flatMap fun parent => registry.declarations.map fun declaration => (parent,declaration.id)

theorem owner_mem (registry : Registry) (seed root limit parent declarationId : Nat) :
 (parent,declarationId) ∈ owners registry seed root limit ↔
 parent ∈ frontier registry seed root limit ∧ ∃ declaration ∈ registry.declarations, declaration.id = declarationId := by
 constructor
 · intro member
   obtain ⟨p,present,entry⟩ := List.mem_flatMap.mp member
   obtain ⟨declaration,visible,same⟩ := List.mem_map.mp entry
   obtain ⟨one,two⟩ := Prod.mk.inj same
   subst parent
   subst declarationId
   exact ⟨present,declaration,visible,rfl⟩
 · rintro ⟨present,declaration,visible,rfl⟩
   exact List.mem_flatMap.mpr ⟨parent,present,List.mem_map.mpr ⟨declaration,visible,rfl⟩⟩

theorem owners_count (registry : Registry) (seed root limit : Nat) :
 (owners registry seed root limit).length = (frontier registry seed root limit).length * registry.declarations.length := by
 have count (parents : List Nat) :
 (parents.flatMap fun parent => registry.declarations.map fun declaration => (parent,declaration.id)).length =
 parents.length * registry.declarations.length := by
   induction parents with
   | nil => simp
   | cons parent rest ih =>
     simp only [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
     omega
 exact count _

theorem installed_owner_enumerated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan) :
 (effect.plan.packet.site.occurrence.identity,effect.plan.packet.declaration.id) ∈
 owners registry context.state.seed root.identity (mass rootLabels) := by
 obtain ⟨depth,small,ancestry⟩ :=
   GeneralNominalVersionedMixedAncestry237.installed_depth_bound source point ground coverage state path effect generated enabled novel
 apply (owner_mem ..).mpr
 have frame := GeneralNominalVersionedMixedAncestry237.frame enabled
 exact ⟨bounded_enumerated ancestry small,effect.plan.packet.declaration,frame.visible,rfl⟩

theorem modeled_sites_enumerated
 (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state assignment) (site : Site roles) (member : site ∈ state.core.sites) :
 site.occurrence.identity ∈ frontier registry context.state.seed root.identity (mass rootLabels) := by
 obtain ⟨depth,labels,ancestry,_,bound⟩ :=
   GeneralNominalVersionedMixedAncestry237.sites_bounded source point ground coverage path assignment valid site member
 exact bounded_enumerated ancestry (by omega)

def branching (registry : Registry) : Nat :=
 registry.declarations.foldr (fun declaration rest => declaration.requirements.length + rest) 0

theorem successors_count (registry : Registry) (seed parent : Nat) :
 (GeneralNominalInvocationAncestry.successors registry seed parent).length = branching registry := by
 have count (declarations : List Declaration) :
 (declarations.flatMap fun declaration => declaration.requirements.map fun clause =>
   GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 6 clause.id 0)).length =
 declarations.foldr (fun declaration rest => declaration.requirements.length + rest) 0 := by
   induction declarations with
   | nil => rfl
   | cons first rest ih => simp only [List.flatMap_cons,List.length_append,List.length_map,List.foldr_cons,ih]
 exact count _

theorem frontier_count (registry : Registry) (seed root depth : Nat) :
 (frontier registry seed root depth).length = (1 + branching registry) ^ depth := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   have children (parents : List Nat) :
   (parents.flatMap (GeneralNominalInvocationAncestry.successors registry seed)).length = parents.length * branching registry := by
     induction parents with
     | nil => simp
     | cons first rest ih =>
       simp only [List.flatMap_cons,List.length_append,successors_count,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
       omega
   rw [frontier,List.length_append,children,ih,Nat.pow_succ,Nat.mul_add,Nat.mul_one]

theorem owner_count_explicit (registry : Registry) (seed root limit : Nat) :
 (owners registry seed root limit).length = (1 + branching registry) ^ limit * registry.declarations.length := by
 rw [owners_count,frontier_count]
end Yulang.GeneralNominalOwnerCandidates252
