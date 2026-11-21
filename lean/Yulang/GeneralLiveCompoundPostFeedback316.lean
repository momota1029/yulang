import Yulang.GeneralLiveCompoundPostSupport316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 33000000
namespace Yulang.GeneralLiveCompoundPostFeedback316
open GeneralLiveCompoundPost316 (raw raw_models known_iff)
open GeneralLiveCompoundLeafInstall316 (after models setValue after_model)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundUpperRefresh316 (old_models)
open GeneralLiveCompoundPostSupport316
open GeneralMixedCompoundUpperSupport307 (identity lower child_history lower_read)
open GeneralMixedCompoundUpperTypes307 (kind meaning equiv_kind)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalState (sources Known)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Test)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

theorem old_valid (m : Assignment) (valid : Models after m) :
    Models GeneralMixedCompoundUpperRefresh307.upperState m :=
  (old_models m).mp ((models m).mp valid).1

theorem pointwise_headless (n : Nat) (present : n ∈ sources raw) (unknown : ¬ Known raw n) :
    ∃ m, Models after m ∧ ∀ test : Test, ¬ test.Holds (m n).1 := by
  rcases extra_raw n present with prior|⟨fresh,_,binder⟩
  · let m := setValue w identity .top
    have valid := patch_after w after_model identity .top identity_outside identity_binder
    have original := old_valid m valid
    refine ⟨m,valid,?_⟩
    intro test seen
    have oldUnknown : ¬ Known GeneralMixedCompoundUpperSnapshot307.snap n := unknown
    rcases GeneralMixedCompoundUpperSupport307.unknown_cases n (base_supported prior) oldUnknown with rfl|rfl|rfl|rfl
    · exact GeneralDictionaryGroundCopy218Refresh.top_no_head test
        ((GeneralNominalOriginCongruence238.test_iff
          (GeneralDictionaryJournalRefinement228Source.top_three m (child_history m original).1) test).mp seen)
    · exact GeneralDictionaryOptionalOutput229.no_test test
        ((GeneralNominalOriginCongruence238.test_iff
          (GeneralDictionaryCompoundObstruction238.associated_value m (child_history m original)) test).mp seen)
    · exact GeneralDictionaryOptionalOutput229.no_test test
        ((GeneralNominalOriginCongruence238.test_iff (lower_read m original) test).mp seen)
    · exact GeneralDictionaryGroundCopy218Refresh.top_no_head test (by simpa only [m,setValue,ite_true] using seen)
  · refine ⟨setValue w n .top,patch_after w after_model n .top fresh binder,?_⟩
    intro test seen
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head test (by simpa only [setValue,ite_true] using seen)

theorem no_refresh (ctx : GeneralNominalCandidates.Context)
    (cert : GeneralNominalVersionedMixedObservations233.Refresh after ctx)
    (n : Nat) (present : n ∈ sources raw) (unknown : ¬ Known raw n) : ¬ Known ctx.state n := by
  intro known
  obtain ⟨m,valid,cannot⟩ := pointwise_headless n present unknown
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have next := (GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr valid
  exact cannot test (GeneralNominalCenteredHeadAllocMergeStable.head_holds head
    (GeneralCanonicalObservations.recorded_sound ctx.state m next.1.1
      (GeneralNominalSupport.head_recorded head)))

noncomputable abbrev classifier := setValue w identity (.base .int)

theorem classifier_valid : Models after classifier :=
  patch_after w after_model identity _ identity_outside identity_binder

theorem classify_value (n : Nat) (within : n ∈ basePool) :
    Equivalent (classifier n).1 (meaning (kind n)) := by
  by_cases same : n = identity
  · subst n
    change Equivalent (classifier identity).1 (.base .int)
    simp only [classifier,setValue,ite_true]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · exact GeneralMixedCompoundUpperTypes307.at_known classifier (old_valid _ classifier_valid) n
      (base_supported within) same

theorem extra_cannot_equal {a b : Nat} (fresh : a ∉ oldPool)
    (binder : a ≠ GeneralLiveCompoundLeafProof316.binderId) (distinct : a ≠ b) :
    ¬ GeneralNominalVersionedMixedKernel234.Equal after a b := by
  intro eq
  have top := eq _ (patch_after w after_model a .top fresh binder)
  have scalar := eq _ (patch_after w after_model a (.base .int) fresh binder)
  simp only [setValue,ite_true,ite_eq_right distinct] at top scalar
  have impossible : GeneralMixedCompoundUpperTypes307.Kind.top = .index :=
    equiv_kind (equivalent_trans top ⟨scalar.2,scalar.1⟩)
  cases impossible

theorem closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed after := by
  intro a b one two equal
  by_cases same : a = b
  · subst b; intro m _; exact ⟨subtype_refl _,subtype_refl _⟩
  rcases extra_raw a one with before|⟨extra,_,binder⟩
  · rcases extra_raw b two with before'|⟨extra',_,binder'⟩
    · have aValue := classify_value a before
      have bValue := classify_value b before'
      have eq := equiv_kind (equivalent_trans ⟨aValue.2,aValue.1⟩
        (equivalent_trans (equal _ classifier_valid) bValue))
      have sameRaw := GeneralMixedCompoundUpperEqClosed307.related_raw
        (GeneralMixedCompoundUpperEqClosed307.classify a before b before' eq)
      intro m rawHeld
      exact sameRaw m ((raw_models m).mp rawHeld)
    · exact False.elim (extra_cannot_equal extra' binder' (Ne.symm same)
        (fun m live => ⟨(equal m live).2,(equal m live).1⟩))
  · exact False.elim (extra_cannot_equal extra binder same equal)

end Yulang.GeneralLiveCompoundPostFeedback316
