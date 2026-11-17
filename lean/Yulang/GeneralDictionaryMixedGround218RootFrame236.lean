import Yulang.GeneralDictionaryMixedGround218FinalPending235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218RootFrame236
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration declaration_checked model parent_only)
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryMixedGround218FinalRegression235 (sites)
open GeneralNominalCenters
noncomputable abbrev plan := GeneralDictionaryGroundCopy218SaturatedParent.planFor allocated reserved ordinary
noncomputable abbrev packet := plan.packet

theorem fresh : GeneralNominalVersionedAllocation231.Fresh packet.context.state registry root.identity
    [(0,4,4),(1,5,5)] := by
  intro key member _
  change key ∈ GeneralDictionaryMixedGround218PointPacket235.packet.context.state.allocated ++
    GeneralNominalVersionedInstallation231.allocated GeneralDictionaryMixedGround218PointPacket235.packet
  apply List.mem_append_right
  change key ∈ GeneralNominalVersionedAllocation231.keys registry root.identity
    GeneralDictionaryMixedGround218PointPacket235.packet.bindings
  rw [GeneralDictionaryMixedGround218PointPacket235.bindings_exact]
  exact member

theorem held : GeneralNominalVersionedPlans231.Holds plan model := by
 have raw := final_model.1.1
 rw [final_context] at raw
 exact GeneralDictionaryMixedGround218PointUniform235.packet_holds model raw

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry packet.context root declaration := by
 refine ⟨source.metadata,?_,[(6,6)],rfl,?_,?_,model,GeneralNominalVersionedPlans231.head_models held⟩
 · constructor
   · intro i; constructor <;>
       exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨6,rfl⟩)))
   · intro output member; cases member
 · rw [GeneralDictionaryGroundCopy218SaturatedParent.report_exact]; exact fresh
 · rw [GeneralDictionaryGroundCopy218SaturatedParent.report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry finalState.core root 0 plan := by
 refine ⟨rfl,final_context.symm,rfl,rfl,?_,?_,List.mem_cons_self,rfl,rfl,?_⟩
 · rw [sites.2.1]; exact List.mem_cons_self
 · rw [sites.1]; exact List.mem_cons_self
 · rw [final_context]; exact prepared

theorem known : ¬ GeneralNominalState.RootPending finalState.core.erased.current.context.state root.demand := by
 rintro ⟨index,unknown⟩
 rw [final_context] at unknown
 exact unknown ⟨6,rfl,Or.inr ⟨exactCopy,rfl⟩⟩

theorem unique : GeneralNominalVersionedCandidates231.Unique registry finalState.core.erased.current.context root 0
 (GeneralNominalVersionedFrame231.children packet) := by
 have survivor := GeneralNominalVersionedMixedFrameSelection235.frame_survivor frame known
 refine ⟨survivor,?_⟩
 intro key kids found
 have copy := found
 obtain ⟨_,d,visible,_,identity,role,_⟩ := found
 cases parent_only visible role
 cases identity
 exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem children_eq : GeneralNominalVersionedFrame231.children packet =
 [GeneralDictionaryGroundCopy218Reinstall.newChild.occurrence] := by
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
   GeneralCanonicalChildOrder.canonicalEmit
 simp only [GeneralDictionaryGroundCopy218Install.canonical_declaration]
 change [GeneralNominalVersionedFrame231.clauseChild packet GeneralDictionaryGroundCopy218Install.clause _] = _
 apply congrArg List.singleton
 apply congrArg (fun arguments : Fin 2 → GeneralSourceState.Interval =>
   (⟨GeneralNominalCenters.fresh 7 0 0 6 0 0,⟨1,arguments,[],by intro _ h; cases h⟩⟩ : GeneralSourceDictionaries.Occurrence roles))
 funext i
 change Fin 2 at i
 have cases : i=0 ∨ i=1 := by omega
 rcases cases with rfl | rfl
 · change (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (GeneralNominalPacketSupport.capture GeneralDictionaryGroundCopy218Reinstall.newPacket).inputs 0
   rw [GeneralDictionaryMixedGround218PointUniform235.capture 0 (Or.inl rfl),GeneralDictionaryGroundCopy218Reinstall.capture_zero]
   rfl
 · change (GeneralNominalVersionedFrame231.capture packet).inputs 1 = (GeneralNominalPacketSupport.capture GeneralDictionaryGroundCopy218Reinstall.newPacket).inputs 1
   rw [GeneralDictionaryMixedGround218PointUniform235.capture 1 (Or.inr rfl),GeneralDictionaryGroundCopy218Reinstall.capture_one]
   rfl
end Yulang.GeneralDictionaryMixedGround218RootFrame236
