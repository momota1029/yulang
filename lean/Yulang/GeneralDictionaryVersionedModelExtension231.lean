import Yulang.GeneralDictionaryVersionedFinal231
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
/-! Every old full journal model has a reconstructed model preserving every
old journal source, not just the exhibited concrete model. -/
namespace Yulang.GeneralDictionaryVersionedModelExtension231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryUpper230Step
open GeneralDictionaryVersionedNames231
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

noncomputable def extend (m : Assignment) :=
  GeneralNominalCenteredModelExtension.assign m names (fun _ => (m 2).1)

theorem retains (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m) :
    GeneralNominalCenteredHeadMatStepJournal.Models after (extend m) :=
  GeneralDictionaryDefaultJournalSupport213.models_assign after names (fun _ => (m 2).1)
    (fun index => outside_journal index.val) valid

theorem value (m : Assignment) (index : Fin 2) :
    ((extend m) (names index)).1 = (m 2).1 :=
  GeneralNominalCenteredModelExtension.assign_value m names (fun _ => (m 2).1)
    (by intro _ _ _; rfl) index

theorem outside (m : Assignment) (source : Nat)
    (absent : ∀ index : Fin 2, names index ≠ source) : extend m source = m source :=
  GeneralNominalCenteredModelExtension.assign_outside m names (fun _ => (m 2).1) absent

theorem source_preserved (m : Assignment) (source : Nat)
    (present : source ∈ GeneralDictionaryDefaultJournalSupport213.journalSources after) :
    extend m source = m source := by
  apply outside
  intro index same
  apply outside_journal index.val
  change names index ∈ GeneralDictionaryDefaultJournalSupport213.journalSources after
  rw [same]
  exact present

theorem two (m : Assignment) : extend m 2 = m 2 := by
  apply outside
  intro index same
  have bound := fresh_above index.val
  change freshName index.val = 2 at same
  omega

theorem merges (m : Assignment) : GeneralDictionaryVersionedCompletion231.NewMerges (extend m) := by
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model (extend m)
      (GeneralNominalAllocation.equations (freshName 0) (.union (.var 2) (.var 2)) ++
        GeneralNominalAllocation.equations (freshName 1) (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent ((extend m) (names 0)).1 (.union ((extend m) 2).1 ((extend m) 2).1) ∧
      Equivalent ((extend m) (names 1)).1 (.inter ((extend m) 2).1 ((extend m) 2).1)
    rw [value m 0,value m 1,two]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model (extend m) (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem reconstructed_model (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m) :
    GeneralNominalCenteredHeadMatStepJournal.Models
      GeneralDictionaryVersionedReconstruction231.reconstructed (extend m) :=
  (GeneralDictionaryVersionedReconstruction231.models_iff _).mpr ⟨retains valid,merges m⟩

theorem every_model_extends (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m) :
    ∃ n, GeneralNominalCenteredHeadMatStepJournal.Models
      GeneralDictionaryVersionedReconstruction231.reconstructed n ∧
      (∀ source ∈ GeneralDictionaryDefaultJournalSupport213.journalSources after, n source = m source) ∧
      GeneralNominalVersionedEvidence231.Evidence registry
        GeneralDictionaryVersionedReconstruction231.reconstructed.core n root (.node declaration.id []) :=
  ⟨extend m,reconstructed_model valid,source_preserved m,
    GeneralDictionaryVersionedFinal231.evidence (reconstructed_model valid)⟩
end Yulang.GeneralDictionaryVersionedModelExtension231
