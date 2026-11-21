import Yulang.GeneralLiveCompoundCounterexample316
import Yulang.GeneralLiveCompoundPostLeafSelect316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
/-! Full recursive Classify reaches the selected dictionary, not just a
selected local frontier. The executor corollary is conditional on an
actual final-state equality; no particular scheduler is claimed to return it. -/
namespace Yulang.GeneralLiveCompoundFullResult316
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration leaf boundary_checked initial initialState)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundLeafInstall316 (after after_model reachable)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostFrames316 (no_root_evidence)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

abbrev dictionary : GeneralDictionaryReadback.Payload := .node declaration.id [.node leaf.id []]

theorem classified : B4TargetV8.Classify (boundary roles) sourceRegistry after root (.selected dictionary) :=
  .selected GeneralLiveCompoundPostRootSelect316.selected
    (.cons (.selected GeneralLiveCompoundPostLeafSelect316.selected .nil) .nil)

theorem selected_without_evidence :
    B4TargetV8.Reachable (boundary roles) sourceRegistry root after ∧
    (boundary roles).Stable sourceRegistry after root ∧
    (boundary roles).Stable sourceRegistry after child ∧
    B4TargetV8.Classify (boundary roles) sourceRegistry after root (.selected dictionary) ∧
    (boundary roles).Models after w ∧
    ¬ (boundary roles).Evidence sourceRegistry after w root dictionary :=
  ⟨reachable,GeneralLiveCompoundStable316.stable,GeneralLiveCompoundStable316.leaf_stable,
    classified,after_model,no_root_evidence after_model _⟩

theorem not_sound_if_returned
    (exec : B4TargetV3.Executor (GeneralNominalVersionedDiagnostic232.vocabulary roles))
    (same : (exec.run sourceRegistry initialState root).1 = after) :
    ¬ B4TargetV8.DictionarySound (boundary roles) exec := by
  intro sound
  have choose : B4TargetV8.Classify (boundary roles) sourceRegistry (exec.run sourceRegistry initialState root).1 root
      (.selected dictionary) := same.symm ▸ classified
  have valid : (boundary roles).Models (exec.run sourceRegistry initialState root).1 w := same.symm ▸ after_model
  have reported := sound sourceRegistry boundary_checked initialState root dictionary initial choose w valid
  exact no_root_evidence after_model _ (same ▸ reported)

end Yulang.GeneralLiveCompoundFullResult316
