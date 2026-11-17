import Yulang.GeneralDictionaryUpper230Equality
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Regression
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected

theorem children_empty : currentPacket.children = [] := by
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem selected_empty : GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry after root
    (.selected declaration.id []) := by
  have found := selected
  rw [children_empty] at found
  exact found

theorem no_evidence (dictionaries) :
    ¬ (GeneralDictionaryHeadSharingBoundary220.boundary roles).Evidence
      sourceRegistry after model root (.node declaration.id dictionaries) := by
  intro evidence
  have payload := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases payload with
  | node source children => exact GeneralDictionaryUpper230Joint.no_instance source

theorem not_evidenceNode :
    ¬ B4SkeletonV8.EvidenceNode (GeneralDictionaryHeadSharingBoundary220.boundary roles) := by
  intro node
  apply no_evidence []
  exact node sourceRegistry boundary_checked after root GeneralDictionaryUpper230Step.reachable
    model GeneralDictionaryUpper230Step.inhabited root declaration.id [] [] (Or.inl rfl)
    GeneralDictionaryUpper230Equality.stable (by intro child member; cases member)
    (show GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry after root
      (.selected declaration.id []) from selected_empty) .nil

theorem stable_selected_without_evidence :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root after ∧
    GeneralNominalCenteredHeadMatStepJournal.Models after model ∧
    GeneralDictionaryDefaultKernel208.Stable registry after root ∧
    GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry after root (.selected declaration.id []) ∧
    ¬ (GeneralDictionaryHeadSharingBoundary220.boundary roles).Evidence
      sourceRegistry after model root (.node declaration.id []) :=
  ⟨GeneralDictionaryUpper230Step.reachable, GeneralDictionaryUpper230Step.inhabited,
    GeneralDictionaryUpper230Equality.stable, selected_empty, no_evidence []⟩
end Yulang.GeneralDictionaryUpper230Regression
