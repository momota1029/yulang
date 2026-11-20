import Yulang.GeneralDeferredLadderInstallData303
import Yulang.GeneralDeferredLadderRefreshAppend303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderReplay303
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalVersionedInstallation231 (replayPlan reserved atoms allocated)
open GeneralNominalRefinements (Refines)
open GeneralDeferredLadderInstallData303
open GeneralDeferredLadderRefreshAppend303

/-- Reindexed plans that agree on the erased report extend their own contexts
by exactly the same source-facing installation data. -/
def replay_refines {p q : Plan roles} (same : Same p q)
    (base : Refines p.packet.context.state q.packet.context.state) :
    Refines (replayPlan p).packet.context.state (replayPlan q).packet.context.state := by
  unfold replayPlan
  rw [← reserved_eq same,← atoms_eq same,← allocated_eq same]
  exact extend_refines base _ _ _

theorem replay_support {p q : Plan roles} (same : Same p q)
    (supported : ∀ s ∈ GeneralNominalState.sources q.packet.context.state,
      s ∈ GeneralNominalState.sources p.packet.context.state) :
    ∀ s ∈ GeneralNominalState.sources (replayPlan q).packet.context.state,
      s ∈ GeneralNominalState.sources (replayPlan p).packet.context.state := by
  unfold replayPlan
  rw [← reserved_eq same,← atoms_eq same,← allocated_eq same]
  exact extend_support supported _ _ _

end Yulang.GeneralDeferredLadderReplay303
