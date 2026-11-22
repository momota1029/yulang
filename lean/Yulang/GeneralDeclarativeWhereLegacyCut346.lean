import Yulang.GeneralDeclarativeWhereRawAtoms346
import Yulang.GeneralDeclarativeCurrentCandidate345

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeWhereLegacyCut346
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal)
open GeneralWhereOriginDelta318 (Cell High)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeWhereRawAtoms346 (cell)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundLeafInstall316 (after reachable after_model)
open GeneralLiveCompoundPostRootHead316 (frame)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralWhereVersionCase317 (expr)
open GeneralWhereVersionInstall317 (before)
open GeneralVersionedEndpointAddress315 (Side atCell)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralDictionaryJournalRefinement228Source (root)

abbrev sideCell (side : Side) : Cell rootPlan :=
  ⟨otherChild,0,side,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,
    (fun _ impossible => by cases impossible),rfl⟩

theorem native_no_slot (side : Side) :
    sourceSlot (rawOf before).base (sideCell side).row.target = none := by
  cases result : sourceSlot (rawOf before).base (sideCell side).row.target with
  | none => rfl
  | some atSlot =>
    have inRaw : (sideCell side).row.target ∈ GeneralNominalState.sources (rawOf before) :=
      (sourceSlot_exact ..).mp result ▸ GeneralNominalAllocationSupport.slot_source (rawOf before) atSlot
    have same : (rawOf before).seed = rootPlan.packet.context.state.seed :=
      congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq.symm
    obtain ⟨name,high,key⟩ := (sideCell side).high same
    rw [key] at inRaw
    exact False.elim (GeneralVersionedHighOrigins315.raw_absent reachable high inRaw)

theorem no_fallback (side : Side) :
    cell (rawOf before).base (sideCell side) = none := by
  unfold cell
  rw [native_no_slot]
  rfl

/-- The native C316 return has real output Ready, but the corrected
physical where author addresses are absent on that raw layout.
There is no fallback to the archived lower address. -/
theorem actual_cut :
    Ready after.core root rootPlan ∧
    cell (rawOf before).base (sideCell .lower) = none ∧
    cell (rawOf before).base (sideCell .upper) = none :=
  ⟨GeneralDeclarativeCurrentBarrier345.ready.2,no_fallback _,no_fallback _⟩

end Yulang.GeneralDeclarativeWhereLegacyCut346
