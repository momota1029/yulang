import Yulang.GeneralDeclarativeI65I74NamedFieldTrail477
import Yulang.GeneralDeclarativeI65I74NamedHopAutoOrdinal477
import Yulang.GeneralDeclarativeI65I74NamedSourceAutoOrdinal477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint StepWire)

abbrev NamedChoiceWithoutOrdinal477 (n : Nat) := StepWire × Checkpoint n

def NamedPathStepWire477.dropOrdinal {n : Nat} (wire : NamedPathStepWire477 n) :
    NamedChoiceWithoutOrdinal477 n := (wire.literal,wire.arriveCheck)

structure DerivedNamedPath477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (pieces : List (NamedChoiceWithoutOrdinal477 n)) where
  oldWires : List (NamedPathStepWire477 n)
  agrees : oldWires.map NamedPathStepWire477.dropOrdinal = pieces
  endpoint : NamedCheckpoint477 r trace table rel
  checked : NamedPathTrace477 c oldWires endpoint

theorem a_single_named_hop_lookup_only_adds_the_missing_ordinal477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {step : StepWire} {check : Checkpoint n}
    {known : (wire : NamedPathStepWire477 n) × NamedPathHop477 c wire}
    (seen : readNamedHopWithoutOrdinal477 c step check = some known) :
    known.1.dropOrdinal = (step,check) := by
  unfold readNamedHopWithoutOrdinal477 chooseNamedHopOrdinal477 at seen
  cases h : exactMarkOrdinal477 (c.mark.path ++ [oneCompiledStep477 step.action]) trace with
  | none => simp [h] at seen
  | some ordinal =>
    cases k : readNamedPathHop477 c ⟨step,ordinal,check⟩ with
    | none => simp [h,k] at seen
    | some run =>
      simp only [h,k,bind,Option.bind,pure,Option.some.injEq] at seen
      cases seen
      rfl

def readDerivedNamedPath477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) :
    (pieces : List (NamedChoiceWithoutOrdinal477 n)) → Option (DerivedNamedPath477 c pieces)
  | [] => some ⟨[],rfl,c,.stop c⟩
  | part :: parts =>
    match seen : readNamedHopWithoutOrdinal477 c part.1 part.2 with
    | none => none
    | some head => do
      let tail ← readDerivedNamedPath477 head.2.endPoint parts
      have step := a_single_named_hop_lookup_only_adds_the_missing_ordinal477 seen
      pure ⟨head.1 :: tail.oldWires,by simp [step,tail.agrees],tail.endpoint,.step head.2 tail.checked⟩

theorem lookup_recovers_every_explicit_path_receipt_at_the_same_ordinals477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c d : NamedCheckpoint477 r trace table rel} {ws : List (NamedPathStepWire477 n)}
    (actual : readLocatedAtHead476 r = some trace) (walk : NamedPathTrace477 c ws d) :
    readDerivedNamedPath477 c (ws.map NamedPathStepWire477.dropOrdinal) =
      some ⟨ws,rfl,d,walk⟩ := by
  induction walk with
  | stop _ => rfl
  | @step point stop wire wires hop tail ih =>
    have h := ordinal_lookup_preserves_exact_checked_hop477 actual hop
    change readDerivedNamedPath477 point ((wire.literal,wire.arriveCheck) :: wires.map NamedPathStepWire477.dropOrdinal) = _
    unfold readDerivedNamedPath477
    split
    · rename_i missing
      rw [h] at missing
      contradiction
    · rename_i head selected
      have same := Option.some.inj (selected.symm.trans h)
      subst head
      simp only [ih,bind,Option.bind,pure]

theorem exact_old_trace_validation_is_retained_after_ordinal_derivation477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel}
    {pieces : List (NamedChoiceWithoutOrdinal477 n)} (x : DerivedNamedPath477 c pieces) :
    readNamedPathTrace477 c x.oldWires = some ⟨x.endpoint,x.checked⟩ :=
  finite_named_path_receipt_replays_exactly477 x.checked


structure DerivedNamedField477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n)
    (choices : List (NamedChoiceWithoutOrdinal477 n)) where
  originalOrdinal : Nat
  expanded : List (NamedPathStepWire477 n)
  sameChoices : expanded.map NamedPathStepWire477.dropOrdinal = choices
  answer : NamedFieldTrail477 fixed ⟨fixed.label,fixed.path,originalOrdinal⟩ table rel outer inner expanded

def readDerivedNamedField477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current}
    {w : BeforeCaptureWire} {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer inner : Checkpoint n)
    (choices : List (NamedChoiceWithoutOrdinal477 n)) :
    Option (DerivedNamedField477 fixed table rel outer inner choices) := do
  let ⟨j,first⟩ ← readImmediateNamedQuotientWithoutOrdinal477 fixed table rel outer inner
  let trail ← readDerivedNamedPath477 (firstNamedCheckpoint477 first) choices
  match h : terminalFieldLabel477 fixed.label trail.oldWires with
  | none => none
  | some label => some ⟨j,trail.oldWires,trail.agrees,first,trail.endpoint,trail.checked,label,h⟩

theorem exact_field_report_and_entire_trace_replay_without_any_supplied_ordinals477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer inner : Checkpoint n} {i : Nat} {wires : List (NamedPathStepWire477 n)}
    (answer : NamedFieldTrail477 fixed ⟨fixed.label,fixed.path,i⟩ table rel outer inner wires) :
    readDerivedNamedField477 fixed table rel outer inner (wires.map NamedPathStepWire477.dropOrdinal) =
      some ⟨i,wires,rfl,answer⟩ := by
  have first := exact_named_quotient_needs_no_supplied_ordinal477 fixed answer.first
    (exact_named_quotient_receipt_replays476 answer.first)
  have rest := lookup_recovers_every_explicit_path_receipt_at_the_same_ordinals477
    answer.first.selected.returned answer.follows
  rcases answer with ⟨source,last,tail,label,seen⟩
  simp only [readDerivedNamedField477,first,rest,bind,Option.bind]
  split
  · rename_i missing
    rw [seen] at missing
    contradiction
  · rename_i got h
    have same := Option.some.inj (h.symm.trans seen)
    subst got
    rfl

theorem ordinal_free_named_field_reader_is_sound_and_complete_on_the_exact_scope477
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    (fixed : FixedFieldChoice476 r) (table : Positions n) (rel : List (Fin n × Fin n))
    (outer inner : Checkpoint n) (choices : List (NamedChoiceWithoutOrdinal477 n)) :
    (readDerivedNamedField477 fixed table rel outer inner choices).isSome = true ↔
      Nonempty (DerivedNamedField477 fixed table rel outer inner choices) := by
  constructor
  · cases h : readDerivedNamedField477 fixed table rel outer inner choices with
    | none => simp
    | some out => exact fun _ => ⟨out⟩
  · rintro ⟨⟨i,wires,agree,answer⟩⟩
    subst choices
    simp [exact_field_report_and_entire_trace_replay_without_any_supplied_ordinals477 answer]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
