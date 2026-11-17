import Yulang.GeneralDictionaryVersionLoopSecondPacket238
import Yulang.GeneralDictionaryVersionLoopFresh238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopSecondFrame238
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopSecondPacket238
open GeneralDictionaryVersionLoopNext237 (current report_exact bindings_exact)
open GeneralDictionaryVersionLoopRetarget237 (retargeted revision retarget)
open GeneralNominalVersionedCandidates231 GeneralNominalCenters


theorem metadata : GeneralNominalRecursiveCandidates.Metadata registry current := GeneralDictionaryVersionLoopSource237.metadata
theorem linked : GeneralNominalState.Linked current.state root.demand := by
 constructor
 · intro index
   constructor <;> (simp only [GeneralNominalState.sources,List.mem_append]; exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(3 : Fin 5),rfl⟩))))
 · intro _ member; cases member

theorem prepared : Prepared registry current root declaration := by
 refine ⟨metadata,linked,[((3 : Fin 5),(3 : Fin 5))],rfl,GeneralDictionaryVersionLoopFresh238.fresh,?_,model,head_model⟩
 rw [report_exact]
 exact ⟨rfl,rfl,rfl⟩
theorem raw_sites : retargeted.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
 change [_] ++ GeneralNominalVersionedChildren232.rawSites GeneralDictionaryVersionLoopPacket237.plan = _
 simp [GeneralNominalVersionedChildren232.rawSites,GeneralNominalVersionedChildren232.emitted,
   GeneralCanonicalChildOrder.canonicalRequirements]
 rfl
theorem centers : retargeted.core.sites = [rootSite 3 root] := by
 change [_] ++ GeneralNominalVersionedChildren232.emitted GeneralDictionaryVersionLoopPacket237.plan = _
 simp [GeneralNominalVersionedChildren232.emitted,
   GeneralCanonicalChildOrder.canonicalRequirements]

theorem frame : GeneralNominalVersionedEvidence231.Frame registry retargeted.core root 0 plan :=
 ⟨rfl,rfl,rfl,rfl,(by rw [raw_sites]; exact List.mem_singleton_self _),(by rw [centers]; exact List.mem_singleton_self _),
 List.mem_singleton_self _,rfl,rfl,prepared⟩
theorem known : ¬ GeneralNominalState.RootPending current.state root.demand := by
 rintro ⟨index,unknown⟩
 exact unknown ⟨(3 : Fin 5),rfl,Or.inr ⟨retarget,rfl⟩⟩
theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
 simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll]
theorem survivor : Survivor registry current root 0 [] :=
 ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[((3 : Fin 5),(3 : Fin 5))],
   rfl,prepared,children_empty.symm⟩
theorem unique : Unique registry current root 0 [] := by
 refine ⟨survivor,?_⟩
 intro key kids found
 have copy := found
 obtain ⟨_,d,visible,_,identity,_⟩ := found
 cases List.mem_singleton.mp visible
 cases identity
 exact ⟨rfl,survivor_children_functional checked copy (survivor)⟩
theorem requests_empty : GeneralNominalCenteredHeadOutputs.requests retargeted.core root = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro output member
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 cases List.mem_singleton.mp (raw_sites ▸ present)
 cases within
theorem ready : GeneralNominalCenteredHeadMatEffects.Ready retargeted.core root plan := by
 intro output member
 simp [requests_empty] at member
noncomputable def effect : GeneralNominalVersionedJournal232.Effect roles :=
 ⟨registry,retargeted.core,plan,frame,children_empty ▸ unique,ready⟩
end Yulang.GeneralDictionaryVersionLoopSecondFrame238
