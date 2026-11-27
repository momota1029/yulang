import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466
import Yulang.GeneralDeclarativeI65I74ProjectionCompilerFrame464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeI65 (visible)
open GeneralDeclarativeI65.I72.NamedProjection464
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

private theorem an_indexed_original_head_receipt_has_its_literal_producer_call
    {p tab legacySource} {idx : Sources legacySource} {addr keep job}
    {r : CheckedCaptureHead p tab}
    (ok : readCaptureFromReadyHead p tab idx addr keep job = some r) :
    (visible p.state.core p.root).length = 1 ∧
    readPrecheckedHead (p := p) tab addr = some r.original ∧
    readOldCaptureReceipt (ordinary p) idx (actualConstructors p) (actualInterpretation p)
      r.original.orig.capture keep r.original.orig.original job = some r.allocated := by
  by_cases one : (visible p.state.core p.root).length = 1
  · cases old : readPrecheckedHead (p := p) tab addr with
    | none => simp [readCaptureFromReadyHead,one,old,Option.bind] at ok
    | some orig =>
      cases proof : readOldCaptureReceipt (ordinary p) idx (actualConstructors p)
        (actualInterpretation p) orig.orig.capture keep orig.orig.original job with
      | none => simp [readCaptureFromReadyHead,one,old,proof,Option.bind] at ok
      | some raw =>
        have equal : (⟨orig,raw⟩ : CheckedCaptureHead p tab) = r := by
          simpa [readCaptureFromReadyHead,one,old,proof,Option.bind] using ok
        subst r
        exact ⟨one,rfl,proof⟩
  · simp [readCaptureFromReadyHead,one] at ok

/-- The old compiler, unlike a native ledger writer, cannot observe a
difference in current origin rows/routes when the actual ordinary state,
catalogue, modes, exact request and checked declaration are identical.
The legacy index supplied to each execution is literally the same. -/
theorem ordinary_capture_receipt_is_invariant_under_native_ledger_differences
    (p : SnapshotPair) (frame : SameCompilerFrame p) (raw : p.pre = p.post)
    (tab : CheckedTable p.before.state.base.core.current)
    {legacySource : State} (idx : Sources legacySource) (addr : HeadAddress)
    (keep : List Nat) (job : Nat)
    {r : CheckedCaptureHead p.after.old (p.afterTable tab)}
    (observed : readCaptureFromReadyHead p.after.old (p.afterTable tab) idx addr keep job = some r) :
    ∃ earlier,
      readCaptureFromReadyHead p.before.old tab idx addr keep job = some earlier ∧
      earlier.allocated = r.allocated ∧
      earlier.original.orig.original = r.original.orig.original ∧
      earlier.original.orig.declaration = r.original.orig.declaration := by
  obtain ⟨one,anchor,run⟩ := an_indexed_original_head_receipt_has_its_literal_producer_call observed
  obtain ⟨earlier,sameLoc,sameDecl,samePat,sameArg,_,read⟩ :=
    an_after_prechecked_head_has_its_same_compiled_origin_before frame tab r.original
  have location := prechecked_reader_never_renumbers_the_visible_roster anchor
  rw [location] at read
  have active : (visible p.before.old.state.core p.before.old.root).length = 1 := by
    exact (congrArg List.length (same_authored_roster_and_original_head_arguments p).1).trans one
  have consts : actualConstructors p.before.old = actualConstructors p.after.old := by
    exact congrArg (fun r => r.constructors) p.registry
  have interp : actualInterpretation p.before.old = actualInterpretation p.after.old := by
    unfold actualInterpretation
    change GeneralSourceMetadataRows291.interpretation
      p.before.state.base.core.current.environment.source.snapshot = _
    rw [frame.environment]
    rfl
  have sameRaw : ordinary p.before.old = ordinary p.after.old := raw
  have oldReads : readOldCaptureReceipt (ordinary p.before.old) idx (actualConstructors p.before.old)
    (actualInterpretation p.before.old) earlier.orig.capture keep earlier.orig.original job =
      some r.allocated := by
    rw [sameRaw,consts,interp,sameArg,samePat]
    exact run
  refine ⟨⟨earlier,r.allocated⟩,?_,rfl,samePat,sameDecl⟩
  simp [readCaptureFromReadyHead,active,read,oldReads,Option.bind]

def SnapshotPair.reversed466 (p : SnapshotPair) : SnapshotPair :=
  ⟨p.after,p.before,p.registry.symm,p.root.symm⟩

theorem both_same_state_snapshots_have_the_same_compiled_ordinary_capture_data
    (p : SnapshotPair) (frame : SameCompilerFrame p) (raw : p.pre = p.post)
    (tab : CheckedTable p.before.state.base.core.current)
    {legacySource : State} (idx : Sources legacySource) (addr : HeadAddress)
    (keep : List Nat) (job : Nat) :
    (readCaptureFromReadyHead p.before.old tab idx addr keep job).map CheckedCaptureHead.allocated =
      (readCaptureFromReadyHead p.after.old (p.afterTable tab) idx addr keep job).map CheckedCaptureHead.allocated := by
  cases actual : readCaptureFromReadyHead p.after.old (p.afterTable tab) idx addr keep job with
  | some r =>
    obtain ⟨earlier,exact,receipt,_,_⟩ :=
      ordinary_capture_receipt_is_invariant_under_native_ledger_differences p frame raw tab idx addr keep job actual
    simp [exact,receipt]
  | none =>
    cases pre : readCaptureFromReadyHead p.before.old tab idx addr keep job with
    | none => rfl
    | some earlier =>
      let rev := SnapshotPair.reversed466 p
      have eqFrame : SameCompilerFrame rev := ⟨frame.environment.symm,frame.modes.symm⟩
      have eqRaw : rev.pre = rev.post := raw.symm
      have eqTab : rev.afterTable (p.afterTable tab) = tab := by
        cases tab
        rfl
      have hit : readCaptureFromReadyHead rev.after.old (rev.afterTable (p.afterTable tab))
          idx addr keep job = some (eqTab.symm ▸ earlier) := by
        cases eqTab
        exact pre
      obtain ⟨later,exact,_,_,_⟩ :=
        ordinary_capture_receipt_is_invariant_under_native_ledger_differences rev eqFrame eqRaw
          (p.afterTable tab) idx addr keep job hit
      change readCaptureFromReadyHead p.after.old (p.afterTable tab) idx addr keep job = some later at exact
      rw [actual] at exact
      cases exact

end Yulang.C466WrittenBinderCoordinates
