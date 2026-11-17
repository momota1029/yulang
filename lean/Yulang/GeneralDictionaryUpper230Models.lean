import Yulang.GeneralDictionaryUpper230Step
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Models
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Reobserve
open GeneralDictionaryOptionalInstall229 (hi)
open GeneralDictionaryOptionalStage229
open GeneralDictionaryUpper230Base GeneralDictionaryUpper230Snapshot
open CommonNominalFullCarrier

theorem extend_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models stage.core.erased.current.context.state m)
    (upper : Equivalent (m hi).1 .emptyRecord) : GeneralNominalState.Models extendedSnapshot m := by
  have transport := assignment_transport m
  refine ⟨⟨?_,?_,?_⟩,?_,valid.2.2⟩
  · apply (PresenceNormalForm.all_append ..).mpr
    constructor
    · rw [PresenceNormalForm.all_rename,transport]
      exact valid.1.1
    · intro atom member
      simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact upper.1
      · exact upper.2
  · intro slot term found
    change Fin 6 at slot
    change (heads slot).equation = some term at found
    by_cases two : slot = 2
    · subst slot
      have same : term = .emptyRecord := Option.some.inj found.symm
      subst term
      exact valid.1.2.1 (2 : Fin 5) .emptyRecord rfl
    · by_cases five : slot = 5
      · subst slot
        have same : term = .emptyRecord := Option.some.inj found.symm
        subst term
        exact upper
      · simp [heads,two,five,GeneralSourceState.Head.equation] at found
  · intro pair member; cases member
  · intro slot d found
    change (if slot = 0 ∨ slot = 1 then some pointDesc else none) = some d at found
    split at found
    · rename_i either
      cases Option.some.inj found
      have moveOne (a) (fit : GeneralNominalState.Fits base m (.type (2,2)) a) :
          GeneralNominalState.Fits extendedBase m
            (GeneralNominalRefinements.renameParameter embed (.type (2,2))) a := by
        cases a with
        | inl ty =>
          change Subtype (m 2).1 ty ∧ Subtype ty (m 2).1 at fit ⊢
          exact fit
        | inr => cases fit
      rcases either with rfl | rfl
      · obtain ⟨values,fits,equal⟩ := valid.2.1 (0 : Fin 5) exactCopy rfl
        refine ⟨values,?_,equal⟩
        change GeneralNominalState.FitsAll base m [.type (2,2),.type (2,2)] values at fits
        cases fits with
        | cons first tail => cases tail with
          | cons second tail => cases tail; exact .cons (moveOne _ first) (.cons (moveOne _ second) .nil)
      · obtain ⟨values,fits,equal⟩ := valid.2.1 (1 : Fin 5) exactCopy rfl
        refine ⟨values,?_,equal⟩
        change GeneralNominalState.FitsAll base m [.type (2,2),.type (2,2)] values at fits
        cases fits with
        | cons first tail => cases tail with
          | cons second tail => cases tail; exact .cons (moveOne _ first) (.cons (moveOne _ second) .nil)
    · cases found

theorem raw_exact (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models extendedSnapshot m ↔
      GeneralNominalState.Models stage.core.erased.current.context.state m ∧
      Equivalent (m hi).1 .emptyRecord := by
  constructor
  · intro valid
    exact ⟨GeneralNominalRefinements.models refines m valid,valid.1.2.1 (5 : Fin 6) .emptyRecord rfl⟩
  · rintro ⟨valid,upper⟩
    exact extend_models m valid upper

theorem high_raw : GeneralNominalState.Models extendedSnapshot modelHigh := by
  apply extend_models modelHigh GeneralDictionaryOptionalRawStage229.current_raw
  rw [GeneralDictionaryOptionalRaw229.high_fresh 1]
  exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralDictionaryUpper230Models
