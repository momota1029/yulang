import Yulang.GeneralDictionaryVersionedNames231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedMerge231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step
open GeneralDictionaryVersionedNames231
open CommonNominalFullCarrier

theorem capture_exact :
    (GeneralNominalVersionedAllocation231.capture extendedSnapshot registry root.identity declaration.id newBindings).inputs 0 =
      (freshName 0,freshName 1) := rfl

theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model extended
    (GeneralNominalVersionedAllocation231.merges extendedSnapshot registry root.identity declaration newBindings) := by
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model extended
      (GeneralNominalAllocation.equations (freshName 0) (.union (.var 2) (.var 2)) ++
        GeneralNominalAllocation.equations (freshName 1) (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (extended (names 0)).1 (.union (extended 2).1 (extended 2).1) ∧
      Equivalent (extended (names 1)).1 (.inter (extended 2).1 (extended 2).1)
    rw [fresh_value 0,fresh_value 1,two_retained]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model extended (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem compatible : GeneralNominalAllocation.Compatible newBindings extended := by
  intro first one last two _
  rcases List.mem_cons.mp one with rfl | one
  all_goals first | cases List.mem_singleton.mp one | skip
  all_goals rcases List.mem_cons.mp two with rfl | two
  all_goals first | cases List.mem_singleton.mp two | skip
  all_goals exact subtype_refl _

theorem propagated_model : GeneralNominalState.Models
    (GeneralNominalVersionedAllocation231.propagate extendedSnapshot registry root.identity declaration newBindings) extended :=
  (GeneralNominalVersionedAllocation231.propagate_models ..).mpr
    ⟨retains_journal.1,compatible,merge_model⟩

theorem actual_fits : GeneralNominalCaptureMerges.Fits extended
    ((GeneralNominalVersionedAllocation231.capture extendedSnapshot registry root.identity declaration.id newBindings).inputs 0)
    (extended actual).1 := by
  rw [capture_exact]
  change Subtype (extended (names 0)).1 (extended actual).1 ∧ Subtype (extended actual).1 (extended (names 1)).1
  rw [fresh_value 0,fresh_value 1,actual_retained]
  exact ⟨subtype_refl _,subtype_refl _⟩

/-- The old journal and the recomputed versioned aggregate equations have one
common model. This does not yet assert a successor boundary or EvidenceAt. -/
theorem common_model :
    ∃ m, GeneralNominalCenteredHeadMatStepJournal.Models after m ∧
      GeneralNominalState.Models
        (GeneralNominalVersionedAllocation231.propagate extendedSnapshot registry root.identity declaration newBindings) m ∧
      (m lo).1 = GeneralDictionaryOptionalOutput229.value ∧
      (m (freshName 0)).1 = .emptyRecord ∧ (m actual).1 = .emptyRecord :=
  ⟨extended,retains_journal,propagated_model,lower_retained,fresh_value 0,actual_retained⟩
end Yulang.GeneralDictionaryVersionedMerge231
