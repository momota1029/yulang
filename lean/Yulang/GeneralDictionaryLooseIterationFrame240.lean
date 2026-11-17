import Yulang.GeneralDictionaryLooseIterationBook240
import Yulang.GeneralNominalVersionedFrameFunctional232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationFrame240
open GeneralDictionaryLooseLoopSource240 (roles registry declaration declaration_checked checked root model)
open GeneralDictionaryLooseIterationBook240
open GeneralDictionaryLooseFamilyBase240 (original pair)
open GeneralNominalVersionedCandidates231 GeneralNominalCenters

theorem located (n) : GeneralNominalRecursiveCandidates.arguments (context n) root = some [(original n 3,original n 3)] := by
 have found : GeneralDictionaryBinderLocations.sourceSlot (context n).state.base 3 = some (original n 3) :=
   (GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr (GeneralDictionaryLooseFamilyBase240.source_original n 3)
 unfold GeneralNominalRecursiveCandidates.arguments GeneralNominalCandidates.arguments GeneralCandidateBoundaryParts.locate
 simp [List.ofFn_succ,found]

theorem metadata (n) : GeneralNominalRecursiveCandidates.Metadata registry (context n) := GeneralDictionaryLooseLoopSource240.metadata
theorem linked (n) : GeneralNominalState.Linked (context n).state root.demand := by
 constructor
 · intro index
   constructor <;> (simp only [GeneralNominalState.sources,List.mem_append]; exact Or.inl (Or.inl (Or.inl
     (List.mem_ofFn.mpr ⟨original n 3,GeneralDictionaryLooseFamilyBase240.source_original n 3⟩))))
 · intro _ member; cases member

theorem prepared (n) (fresh : GeneralNominalVersionedAllocation231.Fresh (context n).state registry root.identity (packet n).bindings) :
 Prepared registry (context n) root declaration := by
 refine ⟨metadata n,linked n,[(original n 3,original n 3)],located n,fresh,?_,model,?_⟩
 · rw [GeneralDictionaryLooseFamilyPacket240.report_exact]
   exact ⟨rfl,rfl,rfl⟩
 · exact GeneralDictionaryLooseFamilyHead240.head_model n _ _ _ (atoms_valid n)

theorem known (n) : ¬ GeneralNominalState.RootPending (context n).state root.demand := by
 rintro ⟨index,unknown⟩
 exact unknown ⟨original n 3,GeneralDictionaryLooseFamilyBase240.source_original n 3,Or.inr ⟨pair n,rfl⟩⟩
theorem children_empty (n) : GeneralNominalVersionedFrame231.children (packet n) = [] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
 simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll]
theorem emitted_empty (n) : GeneralNominalVersionedChildren232.emitted (plan n) = [] := by
 simp [GeneralNominalVersionedChildren232.emitted,GeneralCanonicalChildOrder.canonicalRequirements]
theorem raw_children_empty (n) : GeneralNominalVersionedChildren232.rawSites (plan n) = [] := by
 rw [GeneralNominalVersionedChildren232.rawSites,emitted_empty]; rfl

theorem unique (n) (fresh : GeneralNominalVersionedAllocation231.Fresh (context n).state registry root.identity (packet n).bindings) :
 Unique registry (context n) root 0 [] := by
 have survivor : Survivor registry (context n) root 0 [] :=
   ⟨known n,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(original n 3,original n 3)],
   located n,prepared n fresh,(children_empty n).symm⟩
 refine ⟨survivor,?_⟩
 intro key kids found
 have copy := found
 obtain ⟨_,d,visible,_,identity,_⟩ := found
 cases List.mem_singleton.mp visible
 cases identity
 exact ⟨rfl,survivor_children_functional checked copy survivor⟩

structure Shape (journal : GeneralNominalVersionedJournal232.State roles) (n : Nat) : Prop where
 current : journal.core.erased.current.context = context n
 source : journal.core.erased.source.state = GeneralDictionaryLooseLoopSource240.snapshot
 rawSites : journal.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]
 centers : journal.core.sites = [rootSite 4 root]
 choice : ∀ prior ∈ journal.core.erased.current.packets, prior.declaration.id = 0

theorem frame (shape : Shape journal n)
 (fresh : GeneralNominalVersionedAllocation231.Fresh (context n).state registry root.identity (packet n).bindings) :
 GeneralNominalVersionedEvidence231.Frame registry journal.core root 0 (plan n) :=
 ⟨rfl,shape.current.symm,rfl,rfl,(by rw [shape.rawSites]; exact List.mem_singleton_self _),
 (by rw [shape.centers]; exact List.mem_singleton_self _),List.mem_singleton_self _,rfl,located n,shape.current ▸ prepared n fresh⟩

theorem requests_empty (shape : Shape journal n) : GeneralNominalCenteredHeadOutputs.requests journal.core root = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro output member
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 cases List.mem_singleton.mp (shape.rawSites ▸ present)
 cases within

theorem ready (shape : Shape journal n) : GeneralNominalCenteredHeadMatEffects.Ready journal.core root (plan n) := by
 intro output member
 simp [requests_empty shape] at member

noncomputable def effect (shape : Shape journal n)
 (fresh : GeneralNominalVersionedAllocation231.Fresh (context n).state registry root.identity (packet n).bindings) :
 GeneralNominalVersionedJournal232.Effect roles :=
 ⟨registry,journal.core,plan n,frame shape fresh,children_empty n ▸ (shape.current ▸ unique n fresh),ready shape⟩
end Yulang.GeneralDictionaryLooseIterationFrame240
