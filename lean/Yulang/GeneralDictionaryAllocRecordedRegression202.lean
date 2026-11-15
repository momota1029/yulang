import Yulang.GeneralDictionaryAllocProductionSplit202
import Yulang.GeneralNominalCenteredHeadAllocV7ParentBaseline

namespace Yulang.GeneralDictionaryAllocRecordedRegression202
open GeneralNominalCenteredHeadAllocMergeSource GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState GeneralNominalCenteredHeadAllocMergeStable
open GeneralDictionaryAllocProductionSplit202

/-- The concrete obstructed ancestor is in the historical, not fresh, branch. -/
theorem final_recorded : Recorded final root 37 children := by
  refine ⟨plan,?_,rfl,rfl,rfl⟩
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]
  exact List.mem_singleton_self _

theorem final_generated : ∀ child ∈ children,
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Generated sourceRegistry final root child :=
  fun _ member => generated_of_recorded final_reachable (Or.inl rfl) final_recorded member

/-- No existential extension is smuggled into historical child production. -/
theorem final_no_extension (effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles) :
    ¬ GeneralNominalCenteredHeadMatStepAvailability.Extension final effect := by
  rintro ⟨_,model,valid,_⟩
  exact GeneralNominalCenteredHeadAllocMergeConflict.final_empty ⟨model,valid⟩

theorem historical_branch_nonvacuous :
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final root (.selected 37 children) ∧
    Recorded final root 37 children ∧
    (∀ child ∈ children,
      (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Generated sourceRegistry final root child) ∧
    ¬ GeneralNominalCenteredHeadAllocV7Completion.SelectedCompletion roles :=
  ⟨GeneralNominalCenteredHeadAllocV7ParentBaseline.final_parent_selected,final_recorded,final_generated,
    GeneralNominalCenteredHeadAllocV7ParentBaseline.not_selectedCompletion⟩

end Yulang.GeneralDictionaryAllocRecordedRegression202
