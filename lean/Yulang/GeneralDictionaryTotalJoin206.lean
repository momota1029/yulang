import Yulang.GeneralDictionaryTotalBoundary206
import Yulang.GeneralDictionaryDefaultEvidence204JoinCounterexample

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryTotalJoin206
open GeneralDictionaryDefaultEvidence204JoinSource
open GeneralDictionaryDefaultEvidence204JoinLocal
open GeneralDictionaryDefaultEvidence204JoinCounterexample
open GeneralDictionaryTotalBoundary206
open CommonRoleOutermostResolver

theorem certificate (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models start assignment) :
    GeneralDictionaryTotalEvidence206.Certificate registry start.core assignment root 37 [] plan :=
  GeneralDictionaryTotalEvidence206.certificate_of_semantics frame children_empty.symm
    (total_packet assignment valid) ready (class_effects assignment valid.1)

theorem evidence_model (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) := by
  change GeneralDictionaryTotalEvidence206.Evidence registry start.core assignment root (.node 37 [])
  exact GeneralDictionaryTotalEvidence206.evidence_leaf ⟨plan,certificate assignment valid⟩

theorem selected : B4TargetV7.Local (boundary roles) registry start root (.selected 37 []) :=
  local_iff.mpr v7_selected

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
end Yulang.GeneralDictionaryTotalJoin206
