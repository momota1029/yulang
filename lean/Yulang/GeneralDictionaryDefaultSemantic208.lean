import Yulang.GeneralDictionaryDefaultBoundary208
import Yulang.GeneralDictionaryTotalDefault206
import Yulang.GeneralDictionaryTotalRejected206
import Yulang.GeneralDictionaryTotalJoin206

/-! Exact preservation of semantic regressions199,202,204 under the successor
boundary. These are fixed-state semantic statements, not claims that the old
transition relation equals the corrected one. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryDefaultSemantic208
open CommonRoleOutermostResolver
open GeneralDictionaryDefaultBoundary208

theorem local_legacy :
    Local (roles := roles) registry state demand frontier ↔
    B4TargetV7.Local (GeneralDictionaryTotalBoundary206.boundary roles) registry state demand frontier :=
  local_iff.trans GeneralDictionaryTotalBoundary206.local_iff.symm

theorem evidenceAt_legacy
    (given : B4SkeletonV7.EvidenceAt (GeneralDictionaryTotalBoundary206.boundary roles)
      registry state root) :
    B4SkeletonV7.EvidenceAt (boundary roles) registry state root := by
  intro model valid demand key children dictionaries reached stable childrenStable chosen evidence
  exact given model valid demand key children dictionaries reached
    (stable_old stable) (fun child member => stable_old (childrenStable child member))
    (local_legacy.mp chosen) evidence

namespace Rejected199
open GeneralNominalCenteredHeadAllocV7Cycle199Source
open GeneralNominalCenteredHeadAllocV7Cycle199Fixture

theorem rejected : B4TargetV7.Local (boundary roles) registry start root .rejected :=
  local_legacy.mpr GeneralDictionaryTotalRejected206.rejected

theorem no_selected (key children) :
    ¬ B4TargetV7.Local (boundary roles) registry start root (.selected key children) :=
  fun chosen => GeneralDictionaryTotalRejected206.no_selected key children (local_legacy.mp chosen)

theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root :=
  evidenceAt_legacy GeneralDictionaryTotalRejected206.evidenceAt
end Rejected199

namespace Default202
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202

theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 []) :=
  local_legacy.mpr GeneralDictionaryTotalDefault206.selected

theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) :=
  GeneralDictionaryTotalDefault206.evidence_model assignment valid

theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root :=
  evidenceAt_legacy GeneralDictionaryTotalDefault206.evidenceAt
end Default202

namespace Merged204
open GeneralDictionaryDefaultEvidence204JoinSource

theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 []) :=
  local_legacy.mpr GeneralDictionaryTotalJoin206.selected

theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) :=
  GeneralDictionaryTotalJoin206.evidence_model assignment valid

theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root :=
  evidenceAt_legacy GeneralDictionaryTotalJoin206.evidenceAt
end Merged204

end Yulang.GeneralDictionaryDefaultSemantic208
