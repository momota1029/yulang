import Yulang.GeneralDeclarativeI65I74NamedPathTrace477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open LiteralVisits473 (Checkpoint readCheck)
open ObservationAlternatives473 (Positions graphOf readAlternatives interpretedAt
  actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit
  actual_safe_quotient_never_returns_to_its_own_observation_class)
open QuotientObservation471 (ReturnsUpToEquality cone embedded classOf)
open ObservationSyntax471 (CheckedFieldBit)
open CommonRoleRegularGraph (successors)
open CommonNominalFullCarrier (Equivalent)
open FiniteWorklist (Path)
open GeneralDeclarativeTermWalk322 (Walk)

def terminalFieldLabel477 (initial : Nat) : List (NamedPathStepWire477 n) → Option Nat
  | [] => some initial
  | [wire] => match wire.literal.action with
    | .field label => some label
    | _ => none
  | _ :: middle :: rest => terminalFieldLabel477 initial (middle :: rest)

structure NamedFieldTrail477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n)
    (wires : List (NamedPathStepWire477 n)) where
  first : NamedFieldQuotient476 fixed q table rel outer inner
  last : NamedCheckpoint477 r first.selected.trace table rel
  follows : NamedPathTrace477 (firstNamedCheckpoint477 first) wires last
  label : Nat
  exactLabel : terminalFieldLabel477 fixed.label wires = some label

def NamedFieldTrail477.report {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)}
    (x : NamedFieldTrail477 fixed q table rel outer inner wires) : CheckedFieldBit :=
  ⟨p.root.occurrence,r.head.orig.declaration.id,w.frame.sourceOrdinal,x.last.pose,x.label,x.last.bit⟩

def readNamedFieldTrail477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    (fixed : FixedFieldChoice476 r) (q : NamedSelectionWire476)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n)
    (wires : List (NamedPathStepWire477 n)) :
    Option (NamedFieldTrail477 fixed q table rel outer inner wires) := do
  let first ← readNamedFieldQuotient476 fixed q table rel outer inner
  let tail ← readNamedPathTrace477 (firstNamedCheckpoint477 first) wires
  match seen : terminalFieldLabel477 fixed.label wires with
  | none => none
  | some label => some ⟨first,tail.1,tail.2,label,seen⟩

theorem named_field_trail_replays_without_replacing_initial_source_or_final_site477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)}
    (x : NamedFieldTrail477 fixed q table rel outer inner wires) :
    readNamedFieldTrail477 fixed q table rel outer inner wires = some x := by
  rcases x with ⟨first,last,rest,label,atLabel⟩
  simp only [readNamedFieldTrail477,exact_named_quotient_receipt_replays476 first,
    finite_named_path_receipt_replays_exactly477 rest,bind,Option.bind]
  split
  · rename_i absent
    rw [atLabel] at absent
    contradiction
  · rename_i got seen
    have same := Option.some.inj (seen.symm.trans atLabel)
    subst got
    rfl

theorem deep_field_uses_one_original_source_typing_and_actual_safe_prefixes477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)}
    (x : NamedFieldTrail477 fixed q table rel outer inner wires) :
    ¬ ReturnsUpToEquality (graphOf p.old.state.core table) outer.which ∧
    Path (successors (graphOf p.old.state.core table)) inner.which x.last.checkpoint.which ∧
    (∀ atPt ∈ x.follows.prefixPoints, ¬ ReturnsUpToEquality (graphOf p.old.state.core table) atPt) ∧
    (x.last.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) x.last.checkpoint.which) ∧
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt r.head.orig.code x.first.selected.trace.uses := by
  exact ⟨(exact_named_quotient_pin_and_both_bits476 x.first).1,
    (finite_named_path_points_are_all_safe_before_terminal477 x.follows).1,
    (finite_named_path_points_are_all_safe_before_terminal477 x.follows).2.1,
    (finite_named_path_points_are_all_safe_before_terminal477 x.follows).2.2,
    located_capture_uses_one_actual_typing_walk_in_every_fit476 r x.first.selected.returned⟩

theorem deep_positive_field_reaches_its_own_type_in_every_same_fit477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)}
    (x : NamedFieldTrail477 fixed q table rel outer inner wires) (yes : x.last.bit = true) :
    ∃ first last : Fin x.last.checkpoint.m,
      first ∈ successors (cone x.last.checkpoint.scope) x.last.checkpoint.scope.site ∧
      Path (successors (cone x.last.checkpoint.scope)) first last ∧
      classOf x.last.checkpoint.partition last = classOf x.last.checkpoint.partition x.last.checkpoint.scope.site ∧
      (∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core table m.assignment (embedded x.last.checkpoint.scope last))
          (interpretedAt p.old.state.core table m.assignment (embedded x.last.checkpoint.scope x.last.checkpoint.scope.site))) := by
  have seen := x.last.returned
  rw [yes] at seen
  have actual : readAlternatives p.old.state.core table rel x.last.checkpoint.which
      x.last.checkpoint.scope x.last.checkpoint.partition = some true := by
    simpa [readCheck,x.last.actual.1] using seen
  exact actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit (p := p) actual

theorem deep_negative_field_excludes_every_return_to_its_checked_type477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {wires : List (NamedPathStepWire477 n)}
    (x : NamedFieldTrail477 fixed q table rel outer inner wires) (no : x.last.bit = false) :
    ∀ first ∈ successors (cone x.last.checkpoint.scope) x.last.checkpoint.scope.site, ∀ last,
      Path (successors (cone x.last.checkpoint.scope)) first last →
      classOf x.last.checkpoint.partition last ≠ classOf x.last.checkpoint.partition x.last.checkpoint.scope.site := by
  have seen := x.last.returned
  rw [no] at seen
  have actual : readAlternatives p.old.state.core table rel x.last.checkpoint.which
      x.last.checkpoint.scope x.last.checkpoint.partition = some false := by
    simpa [readCheck,x.last.actual.1] using seen
  exact actual_safe_quotient_never_returns_to_its_own_observation_class (p := p) actual

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
