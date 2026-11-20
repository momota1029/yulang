import Yulang.GeneralDepthTwoFinalNodes300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDepthTwoFinalSelection300
open GeneralGeneratedNestedSource299 (root model)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoSecondInstall300 (final final_requests)
open GeneralDepthTwoTerminalPlan300 (env)
open GeneralDepthTwoTerminalFrame300 (final_model res1 res2 source_support)
open GeneralDepthTwoFinalNodes300
open GeneralNominalExamples (registry intDisplay int_display_checked)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalIdentities (source_above_seed source_identity)
open GeneralRebaseDisplayFrame276 (classes_empty)
open GeneralDeclarations

theorem fresh_at_final (owner : Nat) (bs) :
    GeneralNominalVersionedAllocation231.Fresh env.state compiled owner bs := by
  intro key _ collision
  rcases source_support _ collision with small|one|two
  · have high : 2 < GeneralNominalIdentities.source env.state.seed key := source_above_seed _ _
    exact False.elim (Nat.not_lt_of_ge small high)
  · obtain ⟨prior,seen,eq⟩ := List.mem_map.mp one
    cases (source_identity env.state.seed _ _).mp eq
    exact List.mem_append_left _ seen
  · obtain ⟨prior,seen,eq⟩ := List.mem_map.mp two
    cases (source_identity env.state.seed _ _).mp eq
    exact List.mem_append_right _ seen

theorem options (n : Node) {d : Declaration} (visible : d ∈ compiled.declarations)
    (atRole : d.role = (demand n).demand.role) : d = family n ∨ d = other n := by
  have h := GeneralRebaseCompiledDisplay277.compiled_members visible (atRole.trans (role n))
  cases n
  · exact h.symm
  · exact h.symm
  · exact h

theorem wrong_failed (n : Node) : Failed compiled env (demand n) (other n) := by
  refine ⟨⟨rfl,GeneralDepthTwoRootFrame300.metadata.2⟩,[(source n,source n)],located n,
    fresh_at_final _ _,?_,?_,Or.inl ?_⟩
  all_goals cases n <;> decide +kernel

theorem wrong_unprepared (n : Node) : ¬ Prepared compiled env (demand n) (other n) := by
  rintro ⟨_,_,bounds,loc,_,done,_⟩
  cases Option.some.inj (loc.symm.trans (located n))
  have conflict : (GeneralNominalRecursiveCandidates.report env (other n) [(source n,source n)]).conflicts ≠ [] := by
    cases n <;> decide +kernel
  exact conflict done.2.1

theorem own_prepared (n : Node) : Prepared compiled env (demand n) (family n) := by
  have held := (frame n model final_model).prepared
  rw [declaration] at held
  exact held

theorem safe (n : Node) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled final (demand n) := by
  refine ⟨not_pending n,?_,?_,?_⟩
  · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic env.state rfl final_model.1.1 slot cyclic
    · exact GeneralDepthTwoSafety300.semantic final_model _ cyclic
    · exact GeneralDepthTwoSafety300.semantic final_model _ cyclic
  · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic env.state rfl final_model.1.1 visited.1 cyclic
    · exact GeneralDepthTwoSafety300.semantic final_model _ cyclic
  · rintro (⟨_,d,visible,atRole,notFailed,notPrepared⟩ | pending)
    · rcases options n visible atRole with eq|eq
      · rw [eq] at notPrepared
        exact notPrepared (own_prepared n)
      · rw [eq] at notFailed
        exact notFailed (wrong_failed n)
    · exact pending (administrative n)

theorem root_candidates :
    children compiled env root display display_checked [((0 : Fin 3),(0 : Fin 3))] = [middle] :=
  GeneralDepthTwoFinalParents300.root_children

theorem middle_candidates :
    children compiled env middle display display_checked [((1 : Fin 3),(1 : Fin 3))] = [terminal] := by
  unfold children
  rw [GeneralDepthTwoMiddleFrame300.point_inputs]
  exact GeneralDepthTwoFinalParents300.middle_children

theorem leaf_candidates :
    children compiled env terminal intDisplay int_display_checked [((2 : Fin 3),(2 : Fin 3))] = [] := by
  unfold children GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show intDisplay.requirements = [] from rfl)]
  rfl

theorem survivor (n : Node) : Survivor compiled env (demand n) (code n) ((childNodes n).map demand) := by
  cases n
  · exact ⟨not_pending .outer,display,List.mem_cons_of_mem _ (List.mem_cons_self ..),
      display_checked,rfl,rfl,[(source .outer,source .outer)],located .outer,own_prepared .outer,root_candidates.symm⟩
  · exact ⟨not_pending .inner,display,List.mem_cons_of_mem _ (List.mem_cons_self ..),
      display_checked,rfl,(role .inner).symm,[(source .inner,source .inner)],
      located .inner,own_prepared .inner,middle_candidates.symm⟩
  · exact ⟨not_pending .leaf,intDisplay,List.mem_cons_self ..,int_display_checked,rfl,
      (role .leaf).symm,[(source .leaf,source .leaf)],located .leaf,own_prepared .leaf,leaf_candidates.symm⟩

theorem unique (n : Node) : Unique compiled env (demand n) (code n) ((childNodes n).map demand) := by
  refine ⟨survivor n,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,id,atRole,_,_,ready,_⟩ := found
  rcases options n visible atRole with eq|eq
  · have sameKey : key = code n := id.symm.trans (eq ▸ exact_code n)
    rw [sameKey] at copy
    exact ⟨sameKey,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked copy (survivor n)⟩
  · exact False.elim (wrong_unprepared n (eq ▸ ready))

theorem ready (n : Node) : GeneralNominalCenteredHeadMatEffects.Ready final.core (demand n) (plan n) := by
  intro out taken
  rw [final_requests] at taken
  cases taken

theorem not_merged (n : Node) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict final (demand n) := by
  apply GeneralNominalVersionedMergedConflict232.models_exclude_conflict final_model
  · intro target _ out taken
    rw [final_requests] at taken
    cases taken
  · intro out taken
    rw [final_requests] at taken
    cases taken

theorem selected (n : Node) :
    GeneralNominalVersionedMixedSourceBoundary234.Local registry final (demand n)
      (.selected (code n) ((childNodes n).map demand)) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model
    (safe n) (unique n) final_model (frame n model final_model) (ready n)
    (plan_holds n model final_model) (classes_empty (final_requests (demand n)) (plan n) model)
    (not_merged n)

end Yulang.GeneralDepthTwoFinalSelection300
