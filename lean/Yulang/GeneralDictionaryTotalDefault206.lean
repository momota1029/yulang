import Yulang.GeneralDictionaryTotalBoundary206
import Yulang.GeneralDictionaryTotalLegacy206
import Yulang.GeneralDictionaryDefaultSelected204
import Yulang.GeneralDictionaryDefaultRejected204

namespace Yulang.GeneralDictionaryTotalDefault206
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202
open GeneralDictionaryTotalBoundary206
open CommonRoleOutermostResolver

theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 []) :=
  local_iff.mpr v7_selected

theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) :=
  GeneralDictionaryTotalLegacy206.terminal_default_leaf assignment valid.1

theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root := by
  intro assignment valid demand key children dictionaries reached _ _ chosen given
  have same : demand = root := by
    rcases reached with same | generated
    · exact same
    · exact generated_only_root demand generated
  subst demand
  have equal := B4TargetV7.local_functional chosen selected
  cases equal
  cases given
  exact evidence_model assignment valid
end Yulang.GeneralDictionaryTotalDefault206
