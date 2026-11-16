import Yulang.GeneralDictionaryHeadSharingWitness220
import Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Regression
import Yulang.GeneralDictionaryTotalDefault206
import Yulang.GeneralDictionaryTotalJoin206
import Yulang.GeneralDictionaryDefaultRegression208

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryHeadSharingPrior220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)

namespace Rejected199
open GeneralNominalCenteredHeadAllocV7Cycle199Source
open GeneralNominalCenteredHeadAllocV7Cycle199Local
open GeneralNominalCenteredHeadAllocV7Cycle199Fixture

theorem rejected : Local registry start root .rejected := by
  classical
  by_cases bad : GeneralDictionaryHeadSharingConflict220.Conflict registry start root
  · exact GeneralDictionaryHeadSharingBoundary220.conflict_rejected bad
  · exact .ordinary bad (GeneralDictionaryDefaultBoundary208.local_iff.mpr
      GeneralNominalCenteredHeadAllocV7Cycle199Regression.rejected_v7)

theorem not_selected (key children) : ¬ Local registry start root (.selected key children) := by
  intro chosen
  have impossible := B4TargetV8.local_functional chosen rejected
  cases impossible
end Rejected199

namespace Default202
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202

theorem evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) :=
  GeneralDictionaryTotalDefault206.evidence_model assignment valid
theorem selected : Local registry start root (.selected 37 []) := by
  apply GeneralDictionaryHeadSharingWitness220.selected_of_feasible
    (GeneralDictionaryDefaultBoundary208.local_iff.mpr v7_selected)
  exact ⟨model,inhabited,plan,GeneralDictionaryAllocDefaultLocal202.frame,
    GeneralDictionaryHeadSharing220.packet_holds plan model (total_packet model inhabited)⟩

end Default202

namespace Join204
open GeneralDictionaryDefaultEvidence204JoinSource
open GeneralDictionaryDefaultEvidence204JoinLocal
open GeneralDictionaryDefaultEvidence204JoinCounterexample

theorem evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : (boundary roles).Models start assignment) :
    (boundary roles).Evidence registry start assignment root (.node 37 []) :=
  GeneralDictionaryTotalJoin206.evidence_model assignment valid
theorem selected : Local registry start root (.selected 37 []) := by
  apply GeneralDictionaryHeadSharingWitness220.selected_of_feasible
    (GeneralDictionaryDefaultBoundary208.local_iff.mpr v7_selected)
  exact ⟨model,inhabited,plan,frame,
    GeneralDictionaryHeadSharing220.packet_holds plan model (total_packet model inhabited)⟩

end Join204

namespace Install206
open GeneralDictionaryDefaultGap206Source GeneralDictionaryDefaultGap206Local GeneralDictionaryDefaultGap206State
open GeneralDictionaryDefaultRegression208

theorem genuine_default_change :
    GeneralDictionaryDefaultKernel208.Step registry root start after ∧
    GeneralNominalCenteredHeadMatStepJournal.Models after model ∧
    ¬ GeneralNominalCenteredHeadMatStepJournal.Models after counter :=
  ⟨step,int_retained,bottom_removed⟩
end Install206

end Yulang.GeneralDictionaryHeadSharingPrior220
