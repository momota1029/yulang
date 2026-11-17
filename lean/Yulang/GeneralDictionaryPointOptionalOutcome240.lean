import Yulang.GeneralDictionaryPointOptional240
import Yulang.GeneralNominalPointEvidenceTransfer240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointOptionalOutcome240
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedClosedStep234 (next)
open GeneralDictionaryMixedClosedRegression234

theorem stable : GeneralNominalPointKernel240.Stable registry next root :=
 GeneralNominalPointErasure240.old_stable GeneralDictionaryMixedClosedStable234.source_stable

theorem selected : GeneralNominalPointSourceBoundary240.Local sourceRegistry next root (.selected declaration.id []) :=
 GeneralNominalPointEvidenceTransfer240.local_iff.mpr GeneralDictionaryMixedClosedSelected234.source_selected

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry next root := by
 apply GeneralNominalPointEvidenceTransfer240.evidenceAt GeneralDictionaryMixedClosedStable234.source_stable ?_ GeneralDictionaryMixedClosedRegression234.evidenceAt
 intro demand key children reached chosen child member
 have same : demand = root := reached.elim id generated_only
 subst demand
 have outcome := B4TargetV8.local_functional chosen GeneralDictionaryMixedClosedSelected234.source_selected
 cases outcome
 cases member

theorem regression : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root next ∧
 GeneralNominalPointKernel240.Stable registry next root ∧
 GeneralNominalPointSourceBoundary240.Local sourceRegistry next root (.selected declaration.id []) ∧
 B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry next root ∧
 ∃ model, GeneralNominalVersionedJournal232.Models next model ∧
 GeneralNominalVersionedEvidence231.Evidence registry next.core model root (.node declaration.id []) :=
 ⟨GeneralDictionaryPointOptional240.reachable,stable,selected,evidenceAt,_,
 GeneralDictionaryMixedClosedStable234.valid,all_models_evidence GeneralDictionaryMixedClosedStable234.valid⟩
end Yulang.GeneralDictionaryPointOptionalOutcome240
