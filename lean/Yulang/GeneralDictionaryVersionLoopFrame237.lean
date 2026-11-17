import Yulang.GeneralDictionaryVersionLoopPacket237
import Yulang.GeneralNominalVersionedSupport233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopFrame237
open GeneralDictionaryVersionLoopSource237 GeneralDictionaryVersionLoopPacket237
open GeneralNominalVersionedCandidates231 GeneralNominalCenters

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
 rw [bindings_exact]
 intro key member collision
 have below := source.below_seed _ collision
 change GeneralNominalIdentities.source snapshot.seed key ≤ snapshot.seed at below
 have above := GeneralNominalIdentities.source_above_seed snapshot.seed key
 omega

theorem prepared : Prepared registry context root declaration := by
 refine ⟨metadata,⟨source.linked.1,by intro output member; cases member⟩,
   [(3,3)],by decide +kernel,fresh,?_,model,head_model⟩
 rw [report_exact]
 exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry initial.core root 0 plan :=
 ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,
   by decide +kernel,prepared⟩

theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
 rintro ⟨index,unknown⟩
 exact unknown ⟨3,rfl,Or.inr ⟨pair,rfl⟩⟩

theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
 simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll]

theorem survivor : Survivor registry context root 0 [] :=
 ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(3,3)],
   by decide +kernel,prepared,children_empty.symm⟩

theorem unique : Unique registry context root 0 [] := by
 refine ⟨survivor,?_⟩
 intro key kids found
 have copy := found
 obtain ⟨_,d,visible,_,identity,_⟩ := found
 cases List.mem_singleton.mp visible
 cases identity
 exact ⟨rfl,survivor_children_functional checked copy survivor⟩

theorem requests_empty : GeneralNominalCenteredHeadOutputs.requests initial.core root = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro output member
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 cases List.mem_singleton.mp present
 cases within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready initial.core root plan := by
 intro output member
 simp [requests_empty] at member

noncomputable def effect : GeneralNominalVersionedJournal232.Effect roles :=
 ⟨registry,initial.core,plan,frame,children_empty ▸ unique,ready⟩
noncomputable def installed := GeneralNominalVersionedInstall232.install initial effect

theorem input_trusted : GeneralNominalVersionedSupport233.Trusted installed [.input plan] := by
 apply GeneralNominalVersionedSupport233.Trusted.input plan .source List.mem_cons_self
 intro slot member test observation head assignment valid
 exact GeneralCanonicalObservations.recorded_sound _ _ valid.1 (GeneralNominalSupport.head_recorded head)
end Yulang.GeneralDictionaryVersionLoopFrame237
