import Yulang.GeneralDeclarativeI65I74TypedCompletedFocus482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open Producer479 (PriorPhase CompletedAssociation)
open ObservationAlternatives473 (Positions)
open NativeProducer465 (CheckedPhase)
open InputCoordinates475 (rawAt)

theorem no_completed_focus_uses_an_unreleased_ordinary_owner
    {n : Nat} {p : FullProblem} (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (wire : CompletedFocusWire n)
    (pending : wire.ordinaryOwner ∉ basis.authors.released) :
    readCompletedFocus p gd pos rel basis phase wire = none := by
  cases ran : readCompletedFocus p gd pos rel basis phase wire with
  | none => rfl
  | some received =>
    exact False.elim (pending (completed_focus_reads_same_ordinary_row_and_exact_active_native_release received).2.2.1)

theorem no_completed_focus_can_claim_a_missing_native_grant
    {n : Nat} {p : FullProblem} (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (wire : CompletedFocusWire n)
    (missing : wire.release.write.address ∉ phase.gate.grants) :
    readCompletedFocus p gd pos rel basis phase wire = none := by
  cases ran : readCompletedFocus p gd pos rel basis phase wire with
  | none => rfl
  | some received =>
    have placed := (completed_focus_reads_same_ordinary_row_and_exact_active_native_release received).2.2.2.2
    obtain ⟨oldRelease⟩ := placed.2.2
    exact False.elim (missing oldRelease.released.granted)

theorem no_completed_focus_can_use_an_inactive_source_stamp
    {n : Nat} {p : FullProblem} (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (wire : CompletedFocusWire n)
    (stale : wire.release.write.address.owner ∉ phase.world.board.active) :
    readCompletedFocus p gd pos rel basis phase wire = none := by
  cases ran : readCompletedFocus p gd pos rel basis phase wire with
  | none => rfl
  | some received =>
    have placed := (completed_focus_reads_same_ordinary_row_and_exact_active_native_release received).2.2.2.2
    obtain ⟨oldRelease⟩ := placed.2.2
    exact False.elim (stale oldRelease.released.active)

theorem no_completed_focus_can_replace_independent_same_phase_association
    {n : Nat} {p : FullProblem} (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (phase : CheckedPhase p.old.state.core) (wire : CompletedFocusWire n)
    (missing : ∀ ix row, (⟨wire.ordinaryOwner,ix,row,wire.release.write,wire.release.originOrdinal⟩ :
        CompletedAssociation) ∉ basis.completed) :
    readCompletedFocus p gd pos rel basis phase wire = none := by
  cases ran : readCompletedFocus p gd pos rel basis phase wire with
  | none => rfl
  | some received =>
    have placed := (completed_focus_reads_same_ordinary_row_and_exact_active_native_release received).2.2.2.1
    exact False.elim (missing _ _ placed)

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
