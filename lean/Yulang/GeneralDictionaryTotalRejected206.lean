import Yulang.GeneralDictionaryTotalBoundary206
import Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Regression

namespace Yulang.GeneralDictionaryTotalRejected206
open GeneralNominalCenteredHeadAllocV7Cycle199Source
open GeneralNominalCenteredHeadAllocV7Cycle199Fixture
open GeneralDictionaryTotalBoundary206

theorem rejected : B4TargetV7.Local (boundary roles) registry start root .rejected :=
  local_iff.mpr GeneralNominalCenteredHeadAllocV7Cycle199Regression.rejected_v7

theorem no_selected (key children) :
    ¬ B4TargetV7.Local (boundary roles) registry start root (.selected key children) := by
  intro selected
  have same := B4TargetV7.local_functional selected rejected
  cases same

/-- The old output-conflict regression imposes no new evidence obligation:
all generated demands here equal the rejected root. -/
theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root := by
  apply B4SkeletonV7.evidenceAt_of_no_selection
  intro demand key children reached
  have same : demand = root := by
    rcases reached with same | generated
    · exact same
    · exact generated_only_root demand generated
  subst demand
  exact no_selected key children

end Yulang.GeneralDictionaryTotalRejected206
