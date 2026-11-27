import Yulang.GeneralDeclarativeI65I74AuthenticatedPathSound473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open ObservationAlternatives473 (Place Positions oldPosition graphOf readAlternatives)

def reportedCheckpoint (w : PathWire n) : Checkpoint n :=
  match w.rest.getLast? with
  | none => w.here
  | some (_,checkpoint) => checkpoint

theorem checkpoint_of_nonempty_route_is_its_recursive_terminal
    (first next : Checkpoint n) (move : StepWire) (rest : List (StepWire × Checkpoint n)) :
    reportedCheckpoint (⟨first,(move,next)::rest⟩ : PathWire n) =
      reportedCheckpoint (⟨next,rest⟩ : PathWire n) := by
  cases rest <;> rfl

theorem successful_literal_read_uses_the_given_terminal_checkpoint_without_replacement
    {s : OwnState} {positions : Positions n} {rel : List (Fin n × Fin n)}
    {p : Pattern} {query raw : Expr} {site : Place} {wire : PathWire n}
    {report : TypedPathResult s positions site p query raw wire}
    (ran : readLiteralPath s positions rel site p query raw wire = some report) :
    (reportedCheckpoint wire).which = report.final ∧
      readCheck s positions rel (oldPosition positions report.final) (reportedCheckpoint wire) = some report.bit := by
  rcases wire with ⟨here,rest⟩
  induction rest generalizing here site p query raw with
  | nil =>
    rw [readLiteralPath] at ran
    split at ran
    · cases ran
    · rename_i b check
      cases Option.some.inj ran
      obtain ⟨atSite,_⟩ := checkpoint_does_not_substitute_a_place_or_change_its_bit check
      exact ⟨rfl,by simpa [reportedCheckpoint,atSite] using check⟩
  | cons step remaining ih =>
    rcases step with ⟨move,follow⟩
    rw [readLiteralPath] at ran
    split at ran
    · cases readStep : readLiteralVisitStep s p query raw move with
      | none => simp [readStep,bind,Option.bind] at ran
      | some actual =>
        simp only [readStep,bind,Option.bind] at ran
        split at ran
        · cases ran
        · rename_i next atNext
          cases later : readLiteralPath s positions rel next actual.writtenChild actual.childQuery
              actual.actualRawChild ⟨follow,remaining⟩ with
          | none => simp [later] at ran
          | some tail =>
            simp only [later] at ran
            cases ran
            simpa only [checkpoint_of_nonempty_route_is_its_recursive_terminal] using ih follow later
    · cases ran

theorem exact_checkpoint_data_at_the_reported_terminal_reflects_the_accepted_bit
    {s : OwnState} {positions : Positions n} {rel : List (Fin n × Fin n)}
    {p : Pattern} {query raw : Expr} {site : Place} {wire : PathWire n}
    {report : TypedPathResult s positions site p query raw wire}
    (ran : readLiteralPath s positions rel site p query raw wire = some report) :
    readAlternatives s positions rel (reportedCheckpoint wire).which
      (reportedCheckpoint wire).scope (reportedCheckpoint wire).partition = some report.bit := by
  obtain ⟨_,fitted⟩ := successful_literal_read_uses_the_given_terminal_checkpoint_without_replacement ran
  unfold readCheck at fitted
  split at fitted
  · exact fitted
  · cases fitted


open RetainedFull445 (FullProblem)
open ObservationSyntax471 (readFieldOrigin readTyping)
open GeneralDeclarativeWitnessOrigins350 (attach)

theorem existing_full_nested_result_pins_its_exact_terminal_partition_and_physical_address
    {p : FullProblem} {table gd input pos rel outer wire result}
    (accepted : @readNestedAuthoredField n p table gd input pos rel outer wire = some result) :
    let terminal := reportedCheckpoint wire
    result.physicalSite = oldPosition pos terminal.which ∧
      readAlternatives p.old.state.core pos rel terminal.which terminal.scope terminal.partition =
        some result.bit := by
  dsimp only
  obtain ⟨h⟩ := successful_nested_report_never_changes_source_event_or_exact_positions accepted
  have final := terminal_selector_is_exact.mpr h.actuallyField
  cases checked : readCheck p.old.state.core pos rel (.logical h.firstRead.head.orig.capture.lower) outer with
  | none =>
    simp [readNestedAuthoredField,final,h.sameAttachment,h.originalRead,h.event,h.actualFirst,checked,
      bind,Option.bind] at accepted
  | some sign =>
    cases sign
    · cases taken : readLiteralPath p.old.state.core pos rel (.rowPos h.rawOrdinal h.rawPrefix)
        h.firstRead.sourcePattern h.firstRead.selectedQuery h.firstRead.actualPayload wire with
      | none =>
        simp [readNestedAuthoredField,final,h.sameAttachment,h.originalRead,h.event,h.actualFirst,checked,
          taken,bind,Option.bind] at accepted
      | some v =>
        have reportEq : (⟨p.root.occurrence,h.firstRead.head.orig.declaration.id,input.declarationOrdinal,
            input.path ++ v.suffix,oldPosition pos v.final,v.bit⟩ : NestedFieldReport n) = result := by
          simpa [readNestedAuthoredField,final,h.sameAttachment,h.originalRead,h.event,h.actualFirst,checked,
            taken,bind,Option.bind] using accepted
        have same := successful_literal_read_uses_the_given_terminal_checkpoint_without_replacement taken
        have data := exact_checkpoint_data_at_the_reported_terminal_reflects_the_accepted_bit taken
        exact ⟨(congrArg NestedFieldReport.physicalSite reportEq).symm.trans (congrArg (oldPosition pos) same.1.symm),
          data.trans (congrArg (some ∘ NestedFieldReport.bit) reportEq)⟩
    · simp [readNestedAuthoredField,final,h.sameAttachment,h.originalRead,h.event,h.actualFirst,checked,
        bind,Option.bind] at accepted

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473

