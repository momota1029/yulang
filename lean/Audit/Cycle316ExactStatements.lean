import Yulang.GeneralLiveCompoundCulprit316
import Yulang.GeneralLiveCompoundProposedRepair316

/-! Standalone statement audit distinguishing an actual recursive refutation
from the C315 merely selected-head obstruction. -/
open Yulang
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (sourceRegistry declaration leaf)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundFullResult316 (dictionary)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralLiveCompoundPostFrames316 (rootPlan)

example : (boundary roles).Generated sourceRegistry after root child :=
  GeneralLiveCompoundPost316.generated_after

example : GeneralNominalVersionedEvidence231.Evidence GeneralLiveCompoundRegistry316.registry
    after.core w child (.node leaf.id []) :=
  GeneralLiveCompoundPostFrames316.leaf_evidence GeneralLiveCompoundLeafInstall316.after_model

example : ¬ B4SkeletonV8.EvidenceNode (boundary roles) :=
  GeneralLiveCompoundCounterexample316.not_evidenceNode

example : ¬ GeneralVersionedRevisitCut315.RevisitRhs roles :=
  GeneralLiveCompoundCounterexample316.not_revisit_rhs

example :
    B4TargetV8.Reachable (boundary roles) sourceRegistry root after ∧
    (boundary roles).Stable sourceRegistry after root ∧
    (boundary roles).Stable sourceRegistry after child ∧
    B4TargetV8.Classify (boundary roles) sourceRegistry after root (.selected dictionary) ∧
    (boundary roles).Models after w ∧
    ¬ (boundary roles).Evidence sourceRegistry after w root dictionary :=
  GeneralLiveCompoundFullResult316.selected_without_evidence

example (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalVersionedJournal232.Models after m)
    (head : GeneralNominalVersionedPlans231.HeadModels rootPlan.packet m) :
    ∀ row ∈ GeneralVersionedEndpointEquationCut315.whereRows rootPlan,
      ¬ row.Holds (GeneralNominalVersionedPlans231.variables rootPlan m) m ↔
        row = GeneralVersionedEndpointBadRow315.lowerRow :=
  GeneralLiveCompoundCulprit316.only_lower m valid head

#print axioms Yulang.GeneralLiveCompoundCulprit316.old_head
#print axioms Yulang.GeneralLiveCompoundCulprit316.variables_pair
#print axioms Yulang.GeneralLiveCompoundCulprit316.where_rows
#print axioms Yulang.GeneralLiveCompoundCulprit316.only_lower
#print axioms Yulang.GeneralLiveCompoundCounterexample316.not_evidenceNode
#print axioms Yulang.GeneralLiveCompoundCounterexample316.not_revisit_rhs
#print axioms Yulang.GeneralLiveCompoundFullResult316.selected_without_evidence
#print axioms Yulang.GeneralLiveCompoundFullResult316.not_sound_if_returned
#print axioms Yulang.GeneralLiveCompoundProposedRepair316.cursor
#print axioms Yulang.GeneralLiveCompoundProposedRepair316.old_lower_row
#print axioms Yulang.GeneralLiveCompoundProposedRepair316.choice_compatible
#print axioms Yulang.GeneralLiveCompoundProposedRepair316.feasible_without_rewriting_history
