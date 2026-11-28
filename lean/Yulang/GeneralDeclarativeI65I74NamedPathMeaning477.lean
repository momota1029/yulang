import Yulang.GeneralDeclarativeI65I74NamedFieldTrail477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose atSource)
open ObservationAlternatives473 (Positions graphOf interpretedAt readAlternatives)
open QuotientObservation471 (ReturnsUpToEquality ExactCone cone_replay_sound)
open CommonRoleRegularGraph (successors)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (environment)
open LiteralVisits473 (readCheck Checkpoint)

def NamedPathTrace477.points {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) :
    List (NamedCheckpoint477 r trace table rel) :=
  match xs with
  | .stop _ => [c]
  | .step _ tail => c :: tail.points

theorem every_checkpoint_retains_all_three_source_coordinates477 {n : Nat} {p : FullProblem}
    {t : Table} {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) :
    xs.points.length = ws.length + 1 ∧
    ∀ x ∈ xs.points, trace.marks[x.ordinal]? = some x.mark ∧
      atSource r.head.orig.original x.pose = some x.source ∧
      (rawAt p).equations[x.mark.exposure.picked.raw]? = some x.mark.exposure.picked.row ∧
      t.authored[x.mark.exposure.picked.author]? = some x.mark.exposure.picked.row := by
  constructor
  · induction xs with
    | stop => rfl
    | step _ tail ih => simp [NamedPathTrace477.points,ih]
  · intro x _
    obtain ⟨source,raw,author,_⟩ := named_checkpoint_carries_exact_written_raw_and_author_occurrences477 x
    exact ⟨x.stamped,source,raw,author⟩

theorem a_named_hop_denotes_the_actual_chosen_raw_operand_in_every_assignment477
    {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c : NamedCheckpoint477 r trace table rel}
    {wire : NamedPathStepWire477 n} (hop : NamedPathHop477 c wire) (m : Model) :
    interpretedAt p.old.state.core table m.assignment wire.arriveCheck.which =
      value (environment m.assignment) .actual hop.next.actualRawChild := by
  rw [hop.rawChild]
  simp [interpretedAt,hop.actual.1,value,environment]

open GeneralNominalCenteredHeadMatExpressions (Expr)

def NamedPathTrace477.lastOperand {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d) (initial : Expr) : Expr :=
  match xs with
  | .stop _ => initial
  | .step hop tail => tail.lastOperand hop.next.actualRawChild

theorem exact_terminal_operand_is_selected_not_recovered_from_its_type477
    {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)} {c d : NamedCheckpoint477 r trace table rel}
    {ws : List (NamedPathStepWire477 n)} (xs : NamedPathTrace477 c ws d)
    (initial : Expr) (h : initial = .variable c.mark.exposure.name) :
    xs.lastOperand initial = .variable d.mark.exposure.name := by
  induction xs generalizing initial with
  | stop _ => exact h
  | step hop tail ih =>
    exact ih _ hop.rawChild

theorem last_checkpoint_has_its_actual_field_operand_value477
    {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)} (x : NamedFieldTrail477 fixed q table rel outer inner wires)
    (m : Model) :
    interpretedAt p.old.state.core table m.assignment x.last.checkpoint.which =
      value (environment m.assignment) .actual (x.follows.lastOperand x.first.selected.field.actualPayload) := by
  rw [exact_terminal_operand_is_selected_not_recovered_from_its_type477 x.follows _
    x.first.selected.sameNamedChild]
  simp [interpretedAt,x.last.actual.1,value,environment]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
