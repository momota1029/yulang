import Yulang.GeneralDictionaryPointCompound240
import Yulang.GeneralNominalPointEvidenceTransfer240
import Yulang.GeneralDictionaryCompoundVacuity239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointCompoundOutcome240
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundSites238
open GeneralDictionaryCompoundRefresh239
open GeneralDictionaryCompoundVacuity239

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles)
 sourceRegistry refreshed root := by
 intro model _valid demand key children dictionaries reached _stable _childStable chosen childEvidence
 obtain ⟨plan,framed,childrenEq⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame
   GeneralDictionaryCompoundRefreshStep239.reachable (GeneralNominalPointEvidenceTransfer240.local_iff.mp chosen)
 rcases reached_cases demand reached with same | same
 · subst demand
   have planEq := GeneralDictionaryCompoundNoInstance239.frame_plan framed
   subst plan
   rw [current_children] at childrenEq
   cases childrenEq
   cases childEvidence with
   | cons one _ => exact False.elim (GeneralDictionaryCompoundChild239.no_evidence model _ one)
 · subst demand
   exact False.elim (GeneralDictionaryCompoundChild239.no_frame key plan framed)

theorem regression : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root refreshed ∧
 (∃ model, GeneralNominalVersionedJournal232.Models refreshed model) ∧
 (¬ ∃ model, GeneralNominalVersionedJournal232.Models refreshed model ∧
 GeneralNominalVersionedPlans231.Holds GeneralDictionaryCompoundObstruction239.currentPlan model) ∧
 B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry refreshed root :=
 ⟨GeneralDictionaryPointCompound240.refreshed_reachable,⟨_,GeneralDictionaryCompoundRefreshStep239.inhabited⟩,
 GeneralDictionaryCompoundObstruction239.no_common,evidenceAt⟩
end Yulang.GeneralDictionaryPointCompoundOutcome240
