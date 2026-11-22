import Yulang.GeneralDeclarativeTaggedNamedPatch340
import Yulang.GeneralDeclarativeTaggedParent340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedNamedRoute340
open GeneralDeclarativeCompoundTree338
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (dispatch dispatch_exact)
open GeneralDeclarativeCompoundSources338 (minted_valid)
open GeneralDeclarativeCompoundReadback338 (operandLow operandHigh)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeTaggedNamed340 (Source)
open GeneralDeclarativeTaggedField340 (named_endpoints after preserves)
open GeneralDeclarativeTaggedNamedPatch340 (checked_head)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeTaggedWhole340 (copied)
open GeneralDeclarativeStableReads329 (One names_one)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeGrowth327 (Extends aliases)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeAlternativeView333 (Offer)
open GeneralNominalCenteredHeadMatExpressions (translate Expr)
open GeneralDeclarationPatterns (normalize)
open GeneralCandidateInspection (plainNames)

theorem lift_read {s t : State} (old : Source s tag e payload) (more : Extends s t) : Source t tag e payload := by
  induction old with
  | tagged => exact .tagged
  | join _ _ a b => exact .join a b
  | named offer _ proof =>
    exact .named ⟨offer.owner,offer.rhs,aliases more offer.linked,more.equations offer.stored⟩ proof

/-- Proof-side safeguard: a finite exact read across a union cannot
silently omit a named branch with no backed origin. This is not a
global pending/reject priority or a rule for empty values. -/
theorem no_missing_branch {s : State} (missing : ∀ _offer : Offer s n, False) :
    ¬ ∃ payload, Source s tag (.join left (.variable n)) payload := by
  rintro ⟨_,known⟩
  cases known with
  | join _ right =>
    cases right with
    | named offer _ => exact missing offer

/-- After an arbitrary prefix of already checked sibling fields, use
the actual dispatched address and its source offers. Neither the
prefix nor whole-payload specialization hides any minted record entry. -/
theorem under_siblings {w mid : World done} (t : Ticket w.source a fs)
    (routed : dispatch fs (minted w.state w.reads keep t.jobs) = some (tasks,residual))
    (used : task ∈ tasks) (prior : (advance w t keep).Grows mid)
    (lo : Source (restriction mid.source) tag (operandLow task.1.1) low)
    (hi : Source (restriction mid.source) tag (operandHigh task.1.1) high)
    (shape : normalize task.2 = .variant tag body)
    (plain : plainNames body = some order) (translated : translate c i body = some code) :
    ∃ final shared, TreeExact keep mid (normalize task.2) final (copied shared order) ∧
      One final.state c i task.1.2 task.2 (copied shared order) ∧ final.reads = mid.reads := by
  have listed : task.1 ∈ minted w.state w.reads keep t.jobs := by
    rw [(dispatch_exact routed).2.1]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨task,used,rfl⟩)
  obtain ⟨lower,upper⟩ := GeneralDeclarativeCompoundSources338.minted_anchors t listed
  obtain ⟨x,xSame,xStored⟩ := lower
  obtain ⟨y,ySame,yStored⟩ := upper
  have fromLower : Source (restriction mid.source) tag (.variable task.1.2.lower) low :=
    .named ⟨x,_,aliases prior.2.2 xSame,prior.2.2.equations xStored⟩ lo
  have fromUpper : Source (restriction mid.source) tag (.variable task.1.2.upper) high :=
    .named ⟨y,_,aliases prior.2.2 ySame,prior.2.2.equations yStored⟩ hi
  let keys := names mid.reads ++ keep
  obtain ⟨kept,head,spanBounds⟩ := checked_head
    (GeneralDeclarativeGrowth327.fits prior.1 (minted_valid t listed))
    fromLower fromUpper keys shape plain translated
  exact ⟨after kept,captured mid.state task.1.2 tag low high keys,
    ⟨preserves kept,names_one head,spanBounds⟩,head,rfl⟩

end Yulang.GeneralDeclarativeTaggedNamedRoute340
