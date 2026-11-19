import Yulang.GeneralRebaseDisplayPacket276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDisplayFrame276
open GeneralNominalNonleafPlan193 (plan packet declaration bindings raw_report)
open GeneralNominalNonleafLocal193 (known)
open GeneralRebaseDisplayPacket276 (children holds emitted)
open GeneralNominalExamples (registry context state displayRoot displayChild model state_models intDisplay registry_checked)
open GeneralDeclarationExamples (roles display_checked)
open GeneralNominalVersionedCandidates231 (Prepared Survivor Unique survivor_children_functional)
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters

noncomputable abbrev before := initial (context true) displayRoot

theorem source_ids : ∀ id ∈ GeneralNominalState.sources (state true), id ≤ 1 := by decide +kernel

theorem fresh :
 GeneralNominalVersionedAllocation231.Fresh (state true) registry displayRoot.identity packet.bindings := by
 intro key _ overlap
 have huge : 1 < GeneralNominalIdentities.source (state true).seed key :=
   GeneralNominalIdentities.source_above_seed _ _
 have small := source_ids _ overlap
 omega

theorem prepared : Prepared registry (context true) displayRoot declaration := by
 have old := GeneralNominalNonleafLocal193.prepared
 refine ⟨old.1,old.2.1,[(0,0)],rfl,fresh,?_,model,?_⟩
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report packet)
   rw [raw_report]
   exact ⟨rfl,rfl,rfl⟩
 · exact GeneralNominalVersionedPlans231.head_models (holds model (state_models true))

theorem frame : GeneralNominalVersionedEvidence231.Frame registry before.core displayRoot 1 plan :=
 ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,by simp,rfl,rfl,prepared⟩

theorem survivor : Survivor registry (context true) displayRoot 1 [displayChild] :=
 ⟨known,declaration,by simp,display_checked,rfl,rfl,[(0,0)],rfl,prepared,children.symm⟩

theorem wrong_not_prepared : ¬ Prepared registry (context true) displayRoot intDisplay := by
 rintro ⟨_,_,bounds,loc,_,finished,_⟩
 have same : bounds = [((0 : Fin 2),(0 : Fin 2))] := Option.some.inj loc.symm
 subst bounds
 exact (by decide +kernel : (GeneralNominalRecursiveCandidates.report (context true) intDisplay [(0,0)]).conflicts ≠ []) finished.2.1

theorem unique : Unique registry (context true) displayRoot 1 [displayChild] := by
 refine ⟨survivor,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,check,identity,role,bounds,loc,ready,_⟩ := other
 simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
 rcases visible with rfl|rfl|rfl
 · exact False.elim (wrong_not_prepared ready)
 · have eq : key = 1 := identity.symm
   subst key
   exact ⟨rfl,survivor_children_functional registry_checked copy survivor⟩
 · contradiction

theorem requests_empty : GeneralNominalCenteredHeadOutputs.requests before.core displayRoot = [] :=
 GeneralNominalNonleafLocal193.requests_empty

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready before.core displayRoot plan := by
 intro output member
 rw [requests_empty] at member
 cases member

noncomputable def effect : Effect roles :=
 ⟨registry,before.core,plan,frame,children ▸ unique,ready⟩

noncomputable def after := GeneralNominalVersionedInstall232.install before effect

theorem emitted_site : GeneralNominalVersionedChildren232.emitted plan = [GeneralNominalNonleafPlan193.centerSite] := by
 have length : (GeneralNominalVersionedChildren232.emitted plan).length = 1 :=
   GeneralNominalVersionedChildren232.emitted_length _
 have present : GeneralNominalNonleafPlan193.centerSite ∈ GeneralNominalVersionedChildren232.emitted plan := by
   unfold GeneralNominalVersionedChildren232.emitted
   have recorded : GeneralDeclarationExamples.displayChild ∈
       GeneralCanonicalChildOrder.canonicalRequirements plan.packet.declaration.requirements :=
     (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
   exact List.mem_map.mpr ⟨⟨_,recorded⟩,List.mem_attach _ _,GeneralRebaseDisplayPacket276.child_site⟩
 obtain ⟨element,equal⟩ := List.length_eq_one_iff.mp length
 rw [equal] at present ⊢
 cases List.mem_singleton.mp present
 rfl

theorem actual_edges : after.core.erased.current.edges = [(displayRoot,displayChild)] := by
 change [] ++ GeneralNominalVersionedChildren232.edges plan = _
 unfold GeneralNominalVersionedChildren232.edges
 rw [children]
 rfl

theorem generated : GeneralNominalSaturationState.Generated after.core.erased.current displayRoot displayChild :=
 .child .root (actual_edges ▸ List.mem_singleton_self _)

theorem no_new_request (focus : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalCenteredHeadOutputs.requests after.core focus = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro output member
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 change site ∈ [GeneralNominalDemandMerging.pointSite displayRoot] ++ GeneralNominalVersionedChildren232.rawSites plan at present
 rw [GeneralNominalVersionedChildren232.rawSites,emitted_site] at present
 simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at present
 rcases present with rfl|rfl <;> cases within

theorem classes_empty {core : GeneralNominalCenteredSteps.State roles} {focus : GeneralSourceDictionaries.Occurrence roles}
 (empty : GeneralNominalCenteredHeadOutputs.requests core focus = []) (p : Plan roles) (m : Assignment) :
 GeneralNominalVersionedEffects231.ClassEffects core focus p m := by
 constructor
 · intro output member
   rw [empty] at member
   cases member
 · intro one member
   rw [empty] at member
   cases member

theorem installation (m : Assignment) (valid : GeneralNominalState.Models (state true) m) :
 GeneralNominalVersionedInstall232.InstallationModels before effect m := by
 have holding := holds m valid
 refine ⟨(initial_models _ _ _).mpr ⟨valid,point_root_holds _ _ (fun _ => rfl) _⟩,
   holding,⟨GeneralNominalVersionedPlans231.head_models holding,classes_empty requests_empty plan m⟩,
   classes_empty (no_new_request displayRoot) plan m,?_,?_⟩
 all_goals intro _ h; cases h

theorem after_models (m : Assignment) :
 Models after m ↔ GeneralNominalState.Models (state true) m := by
 constructor
 · intro valid
   exact ((initial_models _ _ _).mp ((GeneralNominalVersionedInstall232.install_models rfl).mp valid).1).1
 · intro valid
   exact (GeneralNominalVersionedInstall232.install_models rfl).mpr (installation m valid)

end Yulang.GeneralRebaseDisplayFrame276
