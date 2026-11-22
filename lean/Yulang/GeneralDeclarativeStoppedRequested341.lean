import Yulang.GeneralDeclarativeStoppedPairedDepth341
import Yulang.GeneralDeclarativeStoppedOrdinal341
import Yulang.GeneralDeclarativeStoppedFreshCut341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 15800000
namespace Yulang.GeneralDeclarativeStoppedRequested341
open GeneralDictionaryOutputDepth252 (registry root)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralRebaseDepthHalt285 (halted)
open GeneralDeclarativeStoppedRetarget340 (candidate row exact_requests exact_packet installable current_plan_not_retained)
open GeneralDeclarativeStoppedDepthView341 (requested outRow exact_rhs)
open GeneralDeclarativeStoppedPairedDepth341 (actual_placement Rel)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDeclarativeStoppedOrder339 (compileRequests)
open GeneralDeclarativeStoppedOrdinal341 (placed_ordinal)
open GeneralDeclarativeEntailment320 (Holds)

theorem ordinal_zero :
    (requests refreshed.core root)[0]? = some ⟨0,3⟩ ∧
    outRow.left = 3 ∧ (∀ m, Models refreshed m → Holds m outRow) ∧
    ∀ e ∈ refreshed.effects, e.plan ≠ candidate.plan := by
  have holdsPlace := actual_placement Rel.rootH
  have literal : compileRequests candidate.plan requested.outputs = some [outRow] := by
    rw [← exact_rhs]
    change compileRequests candidate.plan [⟨0,3⟩] = some [row]
    exact exact_requests ▸ exact_packet
  obtain ⟨seen,target,held⟩ := placed_ordinal (e := candidate) (idx := 0)
    holdsPlace halted .root installable literal rfl rfl
  exact ⟨seen,target,held,current_plan_not_retained⟩

end Yulang.GeneralDeclarativeStoppedRequested341
