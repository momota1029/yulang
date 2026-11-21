import Yulang.GeneralWhereVersionSnapshot317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 36000000
/-! Concrete isolated successor transaction. The current kernel and its
historical packets remain unchanged. This transaction appends the real
corrected descriptor and edge, and a separate corrected-compiler record;
an old packet cannot be asserted for that record. -/
namespace Yulang.GeneralWhereVersionCommit317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundPost316 (raw aliases_after)
open GeneralWhereVersionCase317
open GeneralWhereVersionSnapshot317 (snap context constrained)
open GeneralWhereVersionWitness317 (ParentHolds both_values)
open GeneralWhereVersionCompiler317 (children schema)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

theorem ports (m : Assignment) (valid : ParentHolds m) :
    Equivalent (m lower).1 (variant 0 (m 2).1) ∧ Equivalent (m upper).1 (variant 0 (m 2).1) := by
  have a : lowerRow ∈ (schema rootPlan).equations := rows.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have b : upperRow ∈ (schema rootPlan).equations := rows.symm ▸ List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact both_values m valid.1 valid.2.1 (valid.2.2.2.2 _ a) (valid.2.2.2.2 _ b)

theorem new_snapshot (m : Assignment) (valid : ParentHolds m) : GeneralNominalState.Models snap m :=
  constrained m valid.1.1.1 (ports m valid).1 (ports m valid).2

theorem corrected_site (m : Assignment) (valid : ParentHolds m) : site.Holds m := by
  intro i
  have index : i = 0 := Fin.ext (by
    have h : i.val < 1 := i.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
  subst i
  change GeneralNominalCaptureMerges.Fits m (occ.demand.arguments 0) (m (site.center 0)).1
  rw [descriptor,centers_preserved]
  have original := GeneralLiveCompoundPostFeedback316.old_valid m valid.1
  have center := GeneralMixedCompoundChildEquality307.historical_child_center m
    (GeneralMixedCompoundUpperSupport307.child_history m original)
  exact ⟨subtype_trans (ports m valid).1.1 center.2,subtype_trans center.1 (ports m valid).2.2⟩

noncomputable def core : GeneralNominalCenteredSteps.State roles :=
  { after.core with
    erased := { after.core.erased with current := { after.core.erased.current with
      context := context
      sites := after.core.erased.current.sites ++ [site.observed]
      edges := after.core.erased.current.edges ++ (children rootPlan).map (fun d => (root,d)) } }
    sites := after.core.sites ++ [site]
    sourceRecorded := fun s h => List.mem_append_left _ (after.core.sourceRecorded s h) }

noncomputable def framedState : State roles :=
  ⟨⟨core,after.legacy.effects⟩,after.plans,after.effects⟩

theorem raw_aliases : core.erased.current.aliases = [] := aliases_after

theorem terminal_outputs : occ.demand.outputs = [] := rfl

theorem requests_iff (focus : Occurrence roles) (out : GeneralSourceState.Output) :
    out ∈ requests core focus ↔ out ∈ requests after.core focus := by
  simp only [GeneralNominalCenteredHeadOutputs.mem_requests_iff]
  constructor
  · rintro ⟨rawSite,seen,alias,present⟩
    change rawSite ∈ after.core.erased.current.sites ++ [site.observed] at seen
    rcases List.mem_append.mp seen with old|recent
    · have ids := GeneralLiveCompoundAdmin316.alias_eq (s := framedState) raw_aliases alias
      exact ⟨rawSite,old,ids ▸ Alias.refl _,present⟩
    · cases List.mem_singleton.mp recent
      change out ∈ occ.demand.outputs at present
      rw [terminal_outputs] at present
      cases present
  · rintro ⟨rawSite,seen,alias,present⟩
    have same := GeneralLiveCompoundAdmin316.alias_eq aliases_after alias
    exact ⟨rawSite,List.mem_append_left _ seen,same ▸ Alias.refl _,present⟩

theorem compiled_models (m : Assignment) (valid : ParentHolds m) : Models framedState m := by
  have old := valid.1
  refine ⟨⟨new_snapshot m valid,old.1.2.1,?_,?_,old.1.2.2.2.2.1,?_⟩,old.2.1,?_⟩
  · intro x h
    change x ∈ after.core.erased.current.sites ++ [site.observed] at h
    rcases List.mem_append.mp h with before|recent
    · exact old.1.2.2.1 x before
    · cases List.mem_singleton.mp recent
      exact observed_holds site m (corrected_site m valid)
  · intro x h
    change x ∈ after.core.sites ++ [site] at h
    rcases List.mem_append.mp h with before|recent
    · exact old.1.2.2.2.1 x before
    · cases List.mem_singleton.mp recent
      exact corrected_site m valid
  · intro effect h
    have held := old.1.2.2.2.2.2 effect h
    exact ⟨held.1,GeneralNominalCenteredHeadMatEffects.restrict
      (fun out present => (requests_iff _ _).mp present) held.2⟩
  · intro effect h
    have held := old.2.2 effect h
    exact ⟨held.1,GeneralNominalVersionedJournal232.live_restrict
      (fun out present => (requests_iff _ _).mp present) held.2⟩

theorem produced : Generated core.erased.current root occ := by
  refine .child .root ?_
  change (root,occ) ∈ after.core.erased.current.edges ++ (children rootPlan).map _
  rw [ordered_children]
  exact List.mem_append_right _ (List.mem_singleton_self _)

end Yulang.GeneralWhereVersionCommit317
