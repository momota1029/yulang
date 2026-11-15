import Yulang.GeneralNominalCenteredHeadAllocV7ParentBaseline
import Yulang.B4SkeletonV7

/-! The owner's empty-final-model ancestor refutes global completion, not the
modelwise dictionary obligation. The precise final snapshot satisfies EvidenceAt. -/
namespace Yulang.GeneralDictionaryAllocV7EvidenceScope201

theorem evidenceAt_of_empty_models {v : B4Target.Vocabulary}
    (boundary : B4TargetV7.SourceBoundary v) (registry : v.Registry)
    (state : v.State) (root : v.Demand)
    (empty : ¬ ∃ model, boundary.Models state model) :
    B4SkeletonV7.EvidenceAt boundary registry state root := by
  intro model valid
  exact False.elim (empty ⟨model,valid⟩)

open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeStable

theorem selected_ancestor_evidenceAt :
    B4SkeletonV7.EvidenceAt (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles)
      sourceRegistry final root :=
  evidenceAt_of_empty_models _ _ _ _ GeneralNominalCenteredHeadAllocMergeConflict.final_empty

theorem completion_and_evidence_distinct :
    ¬ GeneralNominalCenteredHeadAllocV7Completion.HeadBaseline roles ∧
    ¬ GeneralNominalCenteredHeadAllocV7Completion.SelectedCompletion roles ∧
    B4SkeletonV7.EvidenceAt (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles)
      sourceRegistry final root :=
  ⟨GeneralNominalCenteredHeadAllocV7ParentBaseline.not_headBaseline,
    GeneralNominalCenteredHeadAllocV7ParentBaseline.not_selectedCompletion,selected_ancestor_evidenceAt⟩

end Yulang.GeneralDictionaryAllocV7EvidenceScope201
