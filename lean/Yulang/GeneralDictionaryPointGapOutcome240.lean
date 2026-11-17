import Yulang.GeneralDictionaryPointGap206240
import Yulang.GeneralNominalPointEvidenceTransfer240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointGapOutcome240
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryMixedGap206Refresh234 (refreshed)

theorem stable : GeneralNominalPointKernel240.Stable registry refreshed root :=
 GeneralNominalPointErasure240.old_stable GeneralDictionaryMixedGap206Stable234.stable

theorem source_stable : (GeneralNominalPointSourceBoundary240.boundary roles).Stable registry refreshed root := stable

theorem selected : GeneralNominalPointSourceBoundary240.Local registry refreshed root (.selected 37 []) :=
 GeneralNominalPointEvidenceTransfer240.local_iff.mpr GeneralDictionaryMixedGap206Selected234.selected

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles) registry refreshed root := by
 intro assignment valid demand key children dictionaries reached _stable _childStable chosen given
 have same : demand = root := reached.elim id GeneralDictionaryMixedGap206Selected234.generated_only
 subst demand
 have outcome := B4TargetV8.local_functional chosen selected
 cases outcome
 cases given
 exact GeneralDictionaryMixedGap206Evidence234.evidence assignment valid

theorem regression : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root refreshed ∧
 GeneralNominalVersionedJournal232.Models refreshed model ∧ ¬ GeneralNominalVersionedJournal232.Models refreshed counter ∧
 GeneralNominalPointKernel240.Stable registry refreshed root ∧
 GeneralNominalPointSourceBoundary240.Local registry refreshed root (.selected 37 []) ∧
 B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles) registry refreshed root ∧
 ∀ assignment, GeneralNominalVersionedJournal232.Models refreshed assignment →
 GeneralNominalVersionedEvidence231.Evidence registry refreshed.core assignment root (.node 37 []) :=
 ⟨GeneralDictionaryPointGap206240.reachable,GeneralDictionaryMixedGap206Refresh234.model_retained,
 GeneralDictionaryMixedGap206Refresh234.counter_removed,stable,selected,evidenceAt,GeneralDictionaryMixedGap206Evidence234.evidence⟩
end Yulang.GeneralDictionaryPointGapOutcome240
