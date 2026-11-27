import Yulang.GeneralDeclarativeI65I74PinnedNestedTypedK2474
import Yulang.GeneralDeclarativeI65I74C332SourceErasure473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open RetainedFull445 (FullProblem)
open LiteralFold471 (SourceGate)
open PreparedDeclarations463 (CheckedTable readPrecheckedHead)

theorem the_exact_supplied_author_token_was_verified_at_the_actual_source_event
    {p : FullProblem} {g : SourceGate p}
    {ready : CheckedTable p.old.state.core.current} {w : FieldOriginWire g}
    {found : FieldOrigin g ready w}
    (observed : readFieldOrigin g ready w = some found) :
    g.verify p.root.occurrence w.rawOrdinal found.row w.token = true := by

  cases head : readPrecheckedHead (p := p.old) ready w.source with
  | none => simp [readFieldOrigin,head,bind,Option.bind] at observed
  | some prechecked =>
    simp only [readFieldOrigin,head,bind,Option.bind] at observed
    repeat' first | split at observed | contradiction
    have equal := Option.some.inj observed
    subst found
    simp_all

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471


namespace Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471
open RetainedFull445 (FullProblem)
open LiteralFold471 (SourceGate)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeTermWalk322 (Occurrence)

theorem same_phase_field_read_iff_this_literal_author_token_verified
    {p : FullProblem} {g : SourceGate p}
    {ready : CheckedTable p.old.state.core.current} {w : FieldOriginWire g}
    (original : FieldOrigin g ready w) :
    readFieldOrigin g ready w = some original ↔
      g.verify p.root.occurrence w.rawOrdinal original.row w.token = true :=
  ⟨the_exact_supplied_author_token_was_verified_at_the_actual_source_event,
   independent_source_field_origin_replays original⟩

theorem exactly_the_given_physical_and_author_ordinals_were_read
    {p : FullProblem} {t : Table} {gd : CheckedTable p.old.state.core.current}
    {a : Attached p.state.base.core.current.ordinary t} {w : AttachedFieldWire472}
    {field : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (w.atGate a)}
    (ran : readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (w.atGate a) = some field) :
    p.state.base.core.current.ordinary.equations[w.rawOrdinal]? = some field.row ∧
      t.authored[w.authorOrdinal]? = some field.row := by
  have confirmed := (same_phase_field_read_iff_this_literal_author_token_verified field).mp ran
  exact ((attached_author_wire_checks_both_literal_ordinals472 (p := p) a).mp confirmed).2

theorem no_decoder_of_capture_output_alone_can_name_two_distinct_verified_positions
    {p : FullProblem} {t : Table} {gd : CheckedTable p.old.state.core.current}
    {a : Attached p.state.base.core.current.ordinary t} {w v : AttachedFieldWire472}
    (left : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (w.atGate a))
    (right : FieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (v.atGate a))
    (sameWritten : left.head.orig.original = right.head.orig.original)
    (sameCode : left.head.orig.code = right.head.orig.code)
    (samePoint : left.head.orig.capture.lower = right.head.orig.capture.lower)
    (sameRow : left.row = right.row)
    (different : (w.rawOrdinal,w.authorOrdinal) ≠ (v.rawOrdinal,v.authorOrdinal)) :
    ¬ ∃ decode : Option (List Occurrence) → (Nat × Nat),
      decode ((readTyping left).map SourceTyping.uses) = (w.rawOrdinal,w.authorOrdinal) ∧
      decode ((readTyping right).map SourceTyping.uses) = (v.rawOrdinal,v.authorOrdinal) := by
  rintro ⟨d,first,last⟩
  have erased := original_capture_execution_cannot_distinguish_erased_physical_author_positions left right
    sameWritten sameCode samePoint sameRow
  exact different (first.symm.trans ((congrArg d erased).trans last))

end Yulang.GeneralDeclarativeI65.I72.ObservationSyntax471

namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open ObservationSyntax471 (exactly_the_given_physical_and_author_ordinals_were_read)
open RetainedFull445 (FullProblem)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeHead320 (Equation)

theorem any_successful_nested_result_consumed_the_exact_physical_and_original_author_pair
    {p : FullProblem} {t : Table} {gd input pos rel outer wire result}
    (ran : @readNestedAuthoredField n p t gd input pos rel outer wire = some result) :
    ∃ row : Equation,
      p.state.base.core.current.ordinary.equations[input.rawOrdinal]? = some row ∧
      t.authored[input.authorOrdinal]? = some row := by
  obtain ⟨ready⟩ := successful_nested_report_never_changes_source_event_or_exact_positions ran
  exact ⟨ready.firstRead.row,exactly_the_given_physical_and_author_ordinals_were_read ready.originalRead⟩

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
