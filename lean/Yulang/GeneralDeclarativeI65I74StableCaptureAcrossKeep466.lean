import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open OrdinaryOccurrenceStamp466
open GeneralDeclarativeInlineMaterial331 (seed)

theorem keeping_slots_does_not_choose_a_different_original_capture
    {s : State} {done : Nat → Prop} {old : Supported s done}
    {idx : Sources (restriction old)} {c interp a p job first later r t}
    (one : ExactOldCaptureExecution idx c interp a first p job r)
    (two : ExactOldCaptureExecution idx c interp a later p job t) :
    r.captureOrdinal = t.captureOrdinal ∧ r.captured = t.captured ∧
      r.written = t.written ∧ r.rawOrdinal = t.rawOrdinal := by
  obtain ⟨pr,src,_,read,_,was,binder,raw⟩ := one
  obtain ⟨qr,dst,_,seen,_,now,auth,rawAfter⟩ := two
  have eq := Option.some.inj (read.symm.trans seen)
  subst dst
  cases record : (taggedParts 0 src)[job]? with
  | none => simp [existingCaptureJob,record] at was
  | some pair =>
    obtain ⟨i,x⟩ := pair
    have earlier : (seed s a first src + job,i,x) = (r.target,r.captureOrdinal,r.captured) := by
      simpa [existingCaptureJob,record] using was
    have next : (seed s a later src + job,i,x) = (t.target,t.captureOrdinal,t.captured) := by
      simpa [existingCaptureJob,record] using now
    have index : r.captureOrdinal = t.captureOrdinal :=
      (congrArg (fun a => a.2.1) earlier).symm.trans (congrArg (fun a => a.2.1) next)
    have exact : r.captured = t.captured :=
      (congrArg (fun a => a.2.2) earlier).symm.trans (congrArg (fun a => a.2.2) next)
    have written : r.written = t.written := by
      rw [index,exact] at binder
      exact congrArg Prod.fst (Option.some.inj (binder.symm.trans auth))
    exact ⟨index,exact,written,raw.trans rawAfter.symm⟩

theorem two_actual_ready_allocation_runs_sharing_only_keep_are_same_literal_capture
    (p : Problem) (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {old : Supported (ordinary p) done}
    (idx : Sources (restriction old)) (addr : HeadAddress) (first later : List Nat) (job : Nat)
    (r t : CheckedCaptureHead p tab)
    (pre : readCaptureFromReadyHead p tab idx addr first job = some r)
    (post : readCaptureFromReadyHead p tab idx addr later job = some t) :
    r.original = t.original ∧
    r.allocated.captured = t.allocated.captured ∧ r.allocated.written = t.allocated.written ∧
    r.allocated.rawOrdinal = t.allocated.rawOrdinal := by
  obtain ⟨_,before,first⟩ := (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mp pre
  obtain ⟨_,after,later⟩ := (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mp post
  have original : r.original = t.original := Option.some.inj (before.symm.trans after)
  rw [original] at first
  have pos := keeping_slots_does_not_choose_a_different_original_capture first later
  exact ⟨original,pos.2⟩

end Yulang.C466WrittenBinderCoordinates
