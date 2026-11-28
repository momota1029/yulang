import Yulang.GeneralDeclarativeI65I74PreElectionTape485
import Yulang.GeneralDeclarativeI65I74MixedRecordRival413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open GeneralDeclarativeI65
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)
open MixedRecord413 (ActualOuterRecord PlainCandidate PlainTape MixedTape MixedVerified
  bindingQuery413 plain_record_candidate_does_not_enter_payload413)
open GeneralDeclarativeInspect321 (PatternK2)
open RecordK2412 (query412)
open GeneralDeclarativeWitnessDeclaredState357 (point)

private theorem actual_plain_of_plain_tape_at_ordinal
    {s q} {o : ActualOuterRecord s q} {rows}
    (all : PlainTape o rows) (i : Nat) {d : Declaration} (atRow : rows[i]? = some d) :
    Nonempty (PlainCandidate o d) := by
  induction all generalizing i with
  | nil => simp at atRow
  | cons front tail ih =>
    cases i with
    | zero =>
      simp at atRow
      cases atRow
      exact ⟨front⟩
    | succ i => exact ih i atRow

private theorem actual_plain_at_every_nonopening_ordinal
    {s q} {o : ActualOuterRecord s q} {rows}
    (all : MixedTape o rows) (i : Nat) {d : Declaration} (atRow : rows[i]? = some d)
    (other : i ≠ all.opening.ordinal) : Nonempty (PlainCandidate o d) := by
  induction all generalizing i with
  | opens front rest =>
    cases i with
    | zero => exact False.elim (other rfl)
    | succ i => exact actual_plain_of_plain_tape_at_ordinal rest i atRow
  | next front rest ih =>
    cases i with
    | zero =>
      simp at atRow
      cases atRow
      exact ⟨front⟩
    | succ i =>
      apply ih i atRow
      intro eq
      exact other (congrArg Nat.succ eq)

theorem every_nonopening_candidate_of_the_actual_old_mixed_roster_is_a_safe_binding485
    (p : FullProblem) (mixed : MixedVerified p.old) (i : Nat) (d : Declaration)
    (atRow : (visible485 p)[i]? = some d)
    (other : i ≠ mixed.rejection.tape.opening.ordinal) :
    ∃ read : PlainCandidate mixed.rejection.outer d,
      Nonempty (SourceHead p.old.state.core p.old.root d) ∧
      ¬ PatternK2 p.old.state.core.current.ordinary mixed.rejection.outer.root
        (bindingQuery413 mixed.rejection.outer.box read.binder) := by
  obtain ⟨read⟩ := actual_plain_at_every_nonopening_ordinal mixed.rejection.tape i atRow other
  refine ⟨read,⟨read.matches⟩,?_⟩
  rintro ⟨site,visited,cycle⟩
  have home := plain_record_candidate_does_not_enter_payload413 visited
  exact mixed.rootSafe ⟨point mixed.rejection.outer.root,by simp [mixed.rejection.outer.args],home ▸ cycle⟩

theorem old_actual_opening_reaches_K2_at_its_independent_authored_ordinal485
    (p : FullProblem) (mixed : MixedVerified p.old) :
    ∃ ord, OriginalRosterCell485 p mixed.rejection.tape.opening.ordinal
        (ord,mixed.rejection.tape.opening.decl) ∧
      PatternK2 p.old.state.core.current.ordinary mixed.rejection.outer.root
        (query412 mixed.rejection.outer.box mixed.rejection.tape.opening.source.nextField
          mixed.rejection.tape.opening.source.binder) := by
  have seen := mixed.rejection.tape.opening.fromOriginalList
  obtain ⟨ord,atSource,exactDecl⟩ := unfilterOrdinal395_exact (role485 p) (declared485 p)
    mixed.rejection.tape.opening.ordinal seen
  exact ⟨ord,⟨seen,atSource,exactDecl⟩,MixedRecord413.full_scan_has_actual_K2_413 mixed.rejection⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
