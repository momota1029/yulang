import Yulang.GeneralRebaseDisplayEndpoint276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27300
set_option maxHeartbeats 9500000
namespace Yulang.GeneralRebaseDisplaySelection276
open GeneralNominalExamples (registry state model displayRoot displayChild intDisplay int_display_checked registry_checked)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseDisplayEvidence276 (center_sites raw_sites ready)
open GeneralRebaseDisplayFrame276 (after no_new_request classes_empty)
open GeneralRebaseDisplayChild276 (context)
open GeneralRebaseDisplaySafety276 (after_model raw_acyclic semantic)
open GeneralRebaseDisplayEndpoint276 (centers_for root_distinct bad_parent bad_child known_zero known_one)

noncomputable abbrev parent := replayPlan GeneralNominalNonleafPlan193.plan
noncomputable abbrev child := GeneralRebaseDisplayChild276.plan

theorem parent_frame : GeneralNominalVersionedEvidence231.Frame registry after.core displayRoot 1 parent :=
 GeneralNominalVersionedInstalledEvidence233.frame rfl after_model

theorem child_frame : GeneralNominalVersionedEvidence231.Frame registry after.core displayChild 3 child :=
 GeneralRebaseDisplayEvidence276.child_frame model after_model

theorem parent_children : GeneralNominalVersionedFrame231.children parent.packet = [displayChild] :=
 (GeneralNominalVersionedInstallation231.replay_children _).trans GeneralRebaseDisplayPacket276.children

theorem known_parent : ¬ GeneralNominalState.RootPending context.state displayRoot.demand := by
 rintro ⟨index,unknown⟩
 exact unknown known_zero

theorem known_child : ¬ GeneralNominalState.RootPending context.state displayChild.demand := by
 rintro ⟨index,unknown⟩
 exact unknown known_one

theorem parent_survivor : Survivor registry context displayRoot 1 [displayChild] := by
 refine ⟨known_parent,display,by simp,display_checked,rfl,rfl,[((0 : Fin 2),(0 : Fin 2))],rfl,parent_frame.prepared,?_⟩
 exact parent_children.symm

theorem child_survivor : Survivor registry context displayChild 3 [] := by
 refine ⟨known_child,intDisplay,by simp,int_display_checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],rfl,child_frame.prepared,?_⟩
 exact GeneralRebaseDisplayChild276.no_children.symm

theorem unique_parent : Unique registry context displayRoot 1 [displayChild] := by
 refine ⟨parent_survivor,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,check,identity,role,bounds,located,prepared,_⟩ := other
 simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
 rcases visible with rfl|rfl|rfl
 · exact False.elim (GeneralRebaseDisplayEndpoint276.wrong_parent_prepared prepared)
 · have same : key = 1 := identity.symm
   subst key
   exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional registry_checked copy parent_survivor⟩
 · cases role

theorem unique_child : Unique registry context displayChild 3 [] := by
 refine ⟨child_survivor,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,check,identity,role,bounds,located,prepared,_⟩ := other
 simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
 rcases visible with rfl|rfl|rfl
 · have same : key = 3 := identity.symm
   subst key
   exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional registry_checked copy child_survivor⟩
 · exact False.elim (GeneralRebaseDisplayEndpoint276.wrong_child_prepared prepared)
 · cases role

theorem same_center_value {a b : Site roles} (same : SameInputs (Models after) a b)
 {first last : Nat} (left : a.observed.inputs = [some (.source first)])
 (right : b.observed.inputs = [some (.source last)]) :
 CommonNominalFullCarrier.Equivalent (model first).1 (model last).1 := by
 have aSeen : GeneralNominalDemandMerging.Denotes model a.observed [(model first).1] := by
   unfold GeneralNominalDemandMerging.Denotes
   rw [left]
   exact .cons ⟨_,rfl,.source first⟩ .nil
 have bSeen : GeneralNominalDemandMerging.Denotes model b.observed [(model last).1] := by
   unfold GeneralNominalDemandMerging.Denotes
   rw [right]
   exact .cons ⟨_,rfl,.source last⟩ .nil
 have paired := GeneralNominalDemandMerging.same_inputs_denote _ _ _ same model after_model _ _ aSeen bSeen
 cases paired with
 | cons equal _ => exact equal

theorem no_cross_merge : ¬ SameInputs (Models after) (rootSite (state true).seed displayRoot) centerSite := by
 intro present
 have eq := same_center_value present (first := 0) (last := 1) rfl rfl
 exact GeneralNominalNonleafSafety193.center_distinct ⟨⟨_,.source 0⟩,⟨_,.source 1⟩,by
   intro _ _ a b; cases a; cases b; exact eq⟩

theorem no_reverse_merge : ¬ SameInputs (Models after) centerSite (rootSite (state true).seed displayRoot) := by
 intro present
 have eq := same_center_value present (first := 1) (last := 0) rfl rfl
 exact GeneralNominalNonleafSafety193.center_distinct ⟨⟨_,.source 0⟩,⟨_,.source 1⟩,by
   intro _ _ a b; cases a; cases b; exact ⟨eq.2,eq.1⟩⟩

theorem administrative {focus : Occurrence roles} (scope : focus = displayRoot ∨ focus = displayChild) :
 GeneralNominalVersionedDiagnostic232.AdministrativeReady after focus := by
 constructor
 · rcases scope with rfl|rfl
   · exact ⟨_,center_sites ▸ List.mem_cons_self,rfl⟩
   · exact ⟨centerSite,center_sites ▸ List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
 · intro a first _ b last same
   rw [center_sites] at first last
   simp only [List.mem_cons,List.not_mem_nil,or_false] at first last
   rcases first with rfl|rfl <;> rcases last with rfl|rfl
   · exact .refl _
   · exact False.elim (no_cross_merge same)
   · exact False.elim (no_reverse_merge same)
   · exact .refl _

theorem safe {focus : Occurrence roles} (scope : focus = displayRoot ∨ focus = displayChild) :
 B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry after focus := by
 refine ⟨?_,?_,?_,?_⟩
 · rcases scope with rfl|rfl
   · exact known_parent
   · exact known_child
 · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
   · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
     exact raw_acyclic context.state rfl after_model.1.1 slot cyclic
   · exact semantic after_model _ cyclic
   · exact semantic after_model _ cyclic
 · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
     exact raw_acyclic context.state rfl after_model.1.1 visited.1 cyclic
   · exact semantic after_model _ cyclic
 · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | pending)
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
     rcases scope with rfl|rfl <;> rcases visible with rfl|rfl|rfl
     · exact notFailed bad_parent
     · exact notPrepared parent_frame.prepared
     · cases role
     · exact notPrepared child_frame.prepared
     · exact notFailed bad_child
     · cases role
   · exact pending (administrative scope)

theorem no_merge_conflict {focus : Occurrence roles} :
 ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict after focus := by
 apply GeneralNominalVersionedMergedConflict232.models_exclude_conflict after_model
 · intro target _ x seen
   rw [no_new_request] at seen
   cases seen
 · intro x seen
   rw [no_new_request] at seen
   cases seen

theorem picked_parent :
 GeneralNominalVersionedMixedBoundary234.Local registry after displayRoot (.selected 1 [displayChild]) := by
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe (Or.inl rfl)) unique_parent after_model
  parent_frame (ready parent) (GeneralNominalVersionedInstalledEvidence233.replay_holds after_model)
  (classes_empty (no_new_request displayRoot) parent model) no_merge_conflict

theorem picked_child :
 GeneralNominalVersionedMixedBoundary234.Local registry after displayChild (.selected 3 []) := by
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe (Or.inr rfl)) unique_child after_model
  child_frame (ready child) (GeneralRebaseDisplayChild276.holds model after_model)
  (classes_empty (no_new_request displayChild) child model) no_merge_conflict

end Yulang.GeneralRebaseDisplaySelection276
