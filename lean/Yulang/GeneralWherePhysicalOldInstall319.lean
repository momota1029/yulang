import Yulang.GeneralWherePhysicalOldModel319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralWherePhysicalOldInstall319
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleModel318 (previousLo previousHi two_writes older_absent)
open GeneralWhereOriginSingleCells318 (loOld hi sig oldChild)
open GeneralWherePhysicalPast319 (layout extra loose looseCtx loose_models firstLo savedHi low_id high_id)
open GeneralWherePhysicalDeferred319 (deferred noAdded)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalOldHead319 (before start frame)
open GeneralWherePhysicalOldPick319 (selected all_requests)
open GeneralWherePhysicalOldModel319 (m private_head full actual_m)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot context root_point)
open GeneralWhereVersionInstall317 (Journal Models InstallStep install emitted)
open GeneralWhereOriginTrace318 (Trace)
open GeneralWhereOriginDelta318 (Delta High)
open GeneralWhereOriginSuccessor318 (with_parent SilentChildren)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCenters
open CommonNominalFullCarrier
open GeneralLiveCompoundLeafProof316 (w)

abbrev installed : Journal roles := install before looseCtx oldPlan

theorem legacy_trace : Trace sourceRegistry before := by
  apply Trace.legacy start
  intro i bad
  exact older_absent _ bad (GeneralNominalAllocationSupport.slot_source snapshot i)

def prior_delta : Delta snapshot loose oldPlan where
  refinement := GeneralWherePhysicalNominal319.refinement snapshot layout extra
    (deferred snapshot 2) (noAdded (s := snapshot) layout extra)
  current := rfl
  cells := [previousLo,previousHi]
  absent := by
    intro c listed
    rcases List.mem_cons.mp listed with rfl|tail
    · exact older_absent _ (previousLo.high rfl)
    · cases List.mem_singleton.mp tail
      exact older_absent _ (previousHi.high rfl)
  fresh_slot := by
    intro c listed
    rcases List.mem_cons.mp listed with rfl|tail
    · exact ⟨firstLo,low_id⟩
    · cases List.mem_singleton.mp tail
      exact ⟨savedHi,high_id⟩
  split_slot := by
    intro i _
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact .inl ⟨j,GeneralWherePhysicalBase319.source_old layout j⟩
    · have two : j = 0 ∨ j = 1 := by omega
      rcases two with rfl|rfl
      · exact .inr ⟨previousLo,List.mem_cons_self,low_id⟩
      · exact .inr ⟨previousHi,List.mem_cons_of_mem _ (List.mem_singleton_self _),high_id⟩

theorem silent : SilentChildren oldPlan := by
  intro s member
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
  have seen := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have found := List.mem_singleton.mp seen
  rcases clause with ⟨d,h⟩
  change d = GeneralLiveCompoundRegistry316.otherChild at found
  subst d
  rfl

theorem prior_model : Models before m :=
  ⟨(GeneralNominalVersionedJournal232.initial_models context root m).mpr
    ⟨((GeneralNominalVersionedPlans231.private_models_iff ..).mp private_head.1).1,
      point_root_holds _ _ root_point _⟩,fun _ impossible => by cases impossible⟩

theorem old_raw : GeneralNominalState.Models loose m := by
  have four : w 4 = m 4 := GeneralWherePhysicalOldModel319.source_value (4 : Fin 5)
  have two : w 2 = m 2 := GeneralWherePhysicalOldModel319.source_value (2 : Fin 5)
  have ep := two_writes w
  change Equivalent (m loOld).1 (variant 0 (w 4).1) ∧ Equivalent (m hi).1 (variant 0 (w 2).1) at ep
  rw [four,two] at ep
  exact (loose_models m).mpr ⟨((GeneralNominalVersionedPlans231.private_models_iff older m).mp private_head.1).1,ep⟩

theorem old_class : ClassEffects start.core root oldPlan m := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro out used body resolved
    cases all_requests root out used
    have expected : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ :=
      Option.some.inj resolved |>.symm
    subst body
    intro row member
    cases List.mem_singleton.mp member
    exact actual_m
  · intro a h b i _
    cases all_requests root a h
    cases all_requests root b i
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem old_installed_model : Models installed m :=
  with_parent prior_model old_raw full old_class silent

theorem step : InstallStep sourceRegistry before installed :=
  .whereRow looseCtx oldPlan boundary_checked frame selected (by intro _ absent; cases absent)
    prior_delta.refinement rfl ⟨m,prior_model,old_installed_model⟩

theorem origin_trace : Trace sourceRegistry installed :=
  .placed looseCtx oldPlan legacy_trace step prior_delta

theorem produced : GeneralNominalSaturationState.Generated
    installed.mixed.core.erased.current root oldChild.occurrence := by
  apply GeneralWhereOriginInstall318.generated_append
  unfold GeneralWhereVersionCompiler317.children
  rw [GeneralWherePhysicalOldModel319.compiled_emission]
  exact List.mem_cons_self

end Yulang.GeneralWherePhysicalOldInstall319
