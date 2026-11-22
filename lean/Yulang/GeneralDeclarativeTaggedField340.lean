import Yulang.GeneralDeclarativeTaggedWhole340
import Yulang.GeneralDeclarativeTaggedNamed340
import Yulang.GeneralDeclarativeCompoundReadback338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedField340
open GeneralDeclarativeCompoundTree338
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (dispatch dispatch_exact)
open GeneralDeclarativeCompoundSources338 (minted_valid minted_anchors Anchors)
open GeneralDeclarativeCompoundReadback338 (operandLow operandHigh child_operands)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTaggedSources340 (BoundsRead merge)
open GeneralDeclarativeTaggedNamed340 (Source)
open GeneralDeclarativeTaggedWhole340 (fullState copied existing_head)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeExactSupport337 (receipts_same)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeStableReads329 (One names_one)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralCandidateInspection (plainNames)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open CommonRoleCanonicalRows (normalize)

theorem named_endpoints {w : World done} (t : Ticket w.source a fs)
    (routed : dispatch fs (minted w.state w.reads keep t.jobs) = some (tasks,residual))
    (uses : task ∈ tasks)
    (left : Source (restriction (advance w t keep).source) tag (operandLow task.1.1) lo)
    (right : Source (restriction (advance w t keep).source) tag (operandHigh task.1.1) hi) :
    Source (restriction (advance w t keep).source) tag (.variable task.1.2.lower) lo ∧
    Source (restriction (advance w t keep).source) tag (.variable task.1.2.upper) hi := by
  have listed : task.1 ∈ minted w.state w.reads keep t.jobs := by
    rw [(dispatch_exact routed).2.1]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨task,uses,rfl⟩)
  obtain ⟨⟨owner,no,authored⟩,⟨higher,hiAlias,standing⟩⟩ := minted_anchors t listed
  exact ⟨.named ⟨owner,_,no,authored⟩ left,.named ⟨higher,_,hiAlias,standing⟩ right⟩

theorem whole_field_read {w : World done} (t : Ticket w.source a fs)
    (routed : dispatch fs (minted w.state w.reads keep t.jobs) = some (tasks,residual))
    (used : task ∈ tasks)
    (lower : merge tag (operandLow task.1.1) = some lo)
    (upper : merge tag (operandHigh task.1.1) = some hi) :
    BoundsRead (advance w t keep).source task.1.2 tag lo hi := by
  have inBatch : task.1 ∈ minted w.state w.reads keep t.jobs := by
    rw [(dispatch_exact routed).2.1]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨task,used,rfl⟩)
  have auth := minted_anchors t inBatch
  exact ⟨minted_valid t inBatch,⟨_,auth.1,lower⟩,⟨_,auth.2,upper⟩⟩

def after {w : World done} (retained : Retains w.state final (names w.reads ++ keep)) : World done :=
  ⟨final,preserve w.source retained.grows,w.reads⟩

theorem preserves {w : World done} (retained : Retains w.state final (names w.reads ++ keep)) :
    Sound keep w (after retained) := by
  refine ⟨⟨retained.grows,fun _ h => h,sources_grow w.source retained.grows⟩,?_⟩
  intro m fit
  obtain ⟨next,good,unchanged⟩ := retained.lifts m fit.1
  exact ⟨next,⟨good,(receipts_same (fun n named => unchanged n
    (List.mem_append_right _ (List.mem_append_left _ named)))).mpr fit.2⟩,unchanged⟩

/-- In the actual routed nested-record field, keep the record's existing
receipt table and all caller-protected names, then construct the single
real merged payload address reused by every plain variable in order.
No unrelated field, alternate route, or withheld output is used. -/
theorem routed_whole {w : World done} (t : Ticket w.source a fs)
    (routed : dispatch fs (minted w.state w.reads keep t.jobs) = some (tasks,residual))
    (taskListed : task ∈ tasks)
    (lower : merge tag (operandLow task.1.1) = some lo)
    (upper : merge tag (operandHigh task.1.1) = some hi)
    (printed : GeneralDeclarationPatterns.normalize task.2 = .variant tag body)
    (plain : plainNames body = some order) (translated : translate c i body = some code) :
    ∃ final shared,
      Sound keep w final ∧
      TreeExact keep (advance w t keep) (GeneralDeclarationPatterns.normalize task.2) final (copied shared order) ∧
      One final.state c i task.1.2 task.2 (copied shared order) ∧
      final.reads = (advance w t keep).reads := by
  let next := advance w t keep
  let keys := names next.reads ++ keep
  have matched := whole_field_read t routed taskListed lower upper
  obtain ⟨kept,head,bounded⟩ := existing_head matched keys printed plain translated
  exact ⟨after kept,captured next.state task.1.2 tag lo hi keys,
    chain (stage (keep := keep) t) (preserves kept),
    ⟨preserves kept,names_one head,bounded⟩,head,rfl⟩

end Yulang.GeneralDeclarativeTaggedField340
