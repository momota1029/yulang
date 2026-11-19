import Yulang.GeneralRebaseCompiledEndpoint277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27300
set_option maxHeartbeats 9500000
namespace Yulang.GeneralRebaseCompiledSelection277
open GeneralNominalExamples (registry state model displayRoot displayChild intDisplay int_display_checked registry_checked)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseCompiledEvidence277 (center_sites raw_sites ready)
open GeneralRebaseDisplayFrame276 (classes_empty)
open GeneralRebaseCompiledDisplay277 (compiled compiled_checked after)
open GeneralRebaseCompiledInstall277 (no_new_request direct_models models)
open GeneralRebaseCompiledChild277 (context)
open GeneralRebaseDisplaySafety276 (raw_acyclic semantic)
open GeneralRebaseCompiledEndpoint277 (centers_for root_distinct bad_parent bad_child known_zero known_one)

noncomputable abbrev parent := replayPlan GeneralRebaseCompiledDisplay277.parent
noncomputable abbrev child := GeneralRebaseCompiledChild277.plan

theorem after_model : Models after model := (models _).mpr GeneralRebaseDisplaySafety276.before_model

theorem parent_frame : GeneralNominalVersionedEvidence231.Frame compiled after.core displayRoot 1 parent :=
 GeneralNominalVersionedInstalledEvidence233.frame rfl after_model

theorem child_frame : GeneralNominalVersionedEvidence231.Frame compiled after.core displayChild 3 child :=
 GeneralRebaseCompiledEvidence277.child_frame model after_model

theorem parent_children : GeneralNominalVersionedFrame231.children parent.packet = [displayChild] :=
 (GeneralNominalVersionedInstallation231.replay_children _).trans GeneralRebaseCompiledDisplay277.children

theorem known_parent : ¬ GeneralNominalState.RootPending context.state displayRoot.demand := by
 rintro ⟨index,unknown⟩
 exact unknown known_zero

theorem known_child : ¬ GeneralNominalState.RootPending context.state displayChild.demand := by
 rintro ⟨index,unknown⟩
 exact unknown known_one

theorem parent_survivor : Survivor compiled context displayRoot 1 [displayChild] := by
 refine ⟨known_parent,display,(by exact List.mem_cons_of_mem _ (List.mem_cons_self ..)),display_checked,rfl,rfl,[((0 : Fin 2),(0 : Fin 2))],rfl,parent_frame.prepared,?_⟩
 exact parent_children.symm

theorem child_survivor : Survivor compiled context displayChild 3 [] := by
 refine ⟨known_child,intDisplay,(by exact List.mem_cons_self ..),int_display_checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],rfl,child_frame.prepared,?_⟩
 exact GeneralRebaseCompiledChild277.no_children.symm

theorem unique_parent : Unique compiled context displayRoot 1 [displayChild] := by
 refine ⟨parent_survivor,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,check,identity,role,bounds,located,prepared,_⟩ := other
 rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
 · exact False.elim (GeneralRebaseCompiledEndpoint277.wrong_parent_prepared prepared)
 · have same : key = 1 := identity.symm
   subst key
   exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional compiled_checked copy parent_survivor⟩

theorem unique_child : Unique compiled context displayChild 3 [] := by
 refine ⟨child_survivor,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,check,identity,role,bounds,located,prepared,_⟩ := other
 rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
 · have same : key = 3 := identity.symm
   subst key
   exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional compiled_checked copy child_survivor⟩
 · exact False.elim (GeneralRebaseCompiledEndpoint277.wrong_child_prepared prepared)

theorem no_cross_merge : ¬ SameInputs (Models after) (rootSite (state true).seed displayRoot) centerSite := by
  have same : Models after = Models GeneralRebaseDisplayFrame276.after :=
    funext fun m => propext (direct_models m)
  rw [same]
  exact GeneralRebaseDisplaySelection276.no_cross_merge

theorem no_reverse_merge : ¬ SameInputs (Models after) centerSite (rootSite (state true).seed displayRoot) := by
  have same : Models after = Models GeneralRebaseDisplayFrame276.after :=
    funext fun m => propext (direct_models m)
  rw [same]
  exact GeneralRebaseDisplaySelection276.no_reverse_merge

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
 B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled after focus := by
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
   · rcases scope with rfl|rfl <;>
        rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
     · exact notFailed bad_parent
     · exact notPrepared parent_frame.prepared
     · exact notPrepared child_frame.prepared
     · exact notFailed bad_child
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
 GeneralNominalVersionedMixedSourceBoundary234.Local registry after displayRoot (.selected 1 [displayChild]) := by
 apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe (Or.inl rfl)) unique_parent after_model
  parent_frame (ready parent) (GeneralNominalVersionedInstalledEvidence233.replay_holds after_model)
  (classes_empty (no_new_request displayRoot) parent model) no_merge_conflict

theorem picked_child :
 GeneralNominalVersionedMixedSourceBoundary234.Local registry after displayChild (.selected 3 []) := by
 apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe (Or.inr rfl)) unique_child after_model
  child_frame (ready child) (GeneralRebaseCompiledChild277.holds model after_model)
  (classes_empty (no_new_request displayChild) child model) no_merge_conflict

end Yulang.GeneralRebaseCompiledSelection277
