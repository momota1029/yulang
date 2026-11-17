import Yulang.GeneralDictionaryOptionalExpression229
namespace Yulang.GeneralDictionaryOptionalSource229
open GeneralDictionaryJournalRefinement228Source
open GeneralSourceState (equationAtoms)
open CommonNominalFullCarrier

def modelLow : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 ∨ source = 1 then foo else if source = 2 then .emptyRecord
    else if source = 3 then .top else GeneralDictionaryOptionalOutput229.value,Common.rowEmpty)

theorem source_models : GeneralNominalState.Models state modelLow := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    simp only [base,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | rfl
    all_goals first | exact subtype_refl _ | exact GeneralDictionaryOptionalOutput229.below_width
  · intro slot term recorded
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj recorded.symm
      subst term; exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [state,base,two,GeneralSourceState.Head.equation] at recorded
  · intro pair member; cases member
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot
      cases Option.some.inj recorded
      refine ⟨[.inl .emptyRecord,.inl .emptyRecord],.cons ?_ (.cons ?_ .nil),subtype_refl _,subtype_refl _⟩
      all_goals exact ⟨GeneralDictionaryOptionalOutput229.below_width,subtype_refl _⟩
    · by_cases one : slot = 1
      · subst slot
        cases Option.some.inj recorded
        exact ⟨[.inl .emptyRecord,.inl .emptyRecord],.cons ⟨subtype_refl _,subtype_refl _⟩
          (.cons ⟨subtype_refl _,subtype_refl _⟩ .nil),subtype_refl _,subtype_refl _⟩
      · simp [state,zero,one] at recorded


theorem lower_value : (modelLow 4).1 = GeneralDictionaryOptionalOutput229.value := rfl

theorem variation : GeneralNominalState.Models snapshot modelLow ∧
    GeneralNominalState.Models snapshot modelHigh ∧ ¬ Equivalent (modelLow 4).1 (modelHigh 4).1 :=
  ⟨source_models,GeneralDictionaryJournalRefinement228Source.source_models true,
    GeneralDictionaryOptionalOutput229.not_width⟩

end Yulang.GeneralDictionaryOptionalSource229
