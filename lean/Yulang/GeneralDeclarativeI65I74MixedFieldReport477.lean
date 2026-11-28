import Yulang.GeneralDeclarativeI65I74MixedInlineSeed477
import Yulang.GeneralDeclarativeI65I74NamedSourceAutoOrdinal477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions Place graphOf oldPosition)
open ObservationSyntax471 (confirmedAddress)
open LiteralVisits473 (Checkpoint StepWire terminalIsField checkpoint_does_not_substitute_a_place_or_change_its_bit)
open QuotientObservation471 (ReturnsUpToEquality)
open GeneralDeclarativeTermWalk322 (Walk)

structure MixedInputSeed477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n) where
  start : MixedPoint477 r table rel
  original : start.pose = fixed.path
  compiled : start.compiled = [.field fixed.label]
  sameCheckpoint : start.checkpoint = first
  rooted : first.which ∈ CommonRoleRegularGraph.successors (graphOf p.old.state.core table) outer.which
  safe : ¬ ReturnsUpToEquality (graphOf p.old.state.core table) outer.which

def readMixedInputSeed477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n) :
    Option (MixedInputSeed477 fixed table rel outer first) :=
  match confirmedAddress fixed.original with
  | .inline _ _ => do
    let seed ← readMixedInlineSeed477 fixed table rel outer first
    have h := (checkpoint_does_not_substitute_a_place_or_change_its_bit seed.outerSafe).2
    pure ⟨seed.point,rfl,rfl,rfl,(inline_seed_is_exact_old_source_and_original_graph_edge477 seed).1,
      fun c => Bool.false_ne_true (h.mpr c)⟩
  | .named _ => do
    let held ← readImmediateNamedQuotientWithoutOrdinal477 fixed table rel outer first
    let seed := mixedPointFromChosenNamed477 (firstNamedCheckpoint477 held.2)
    have h := (checkpoint_does_not_substitute_a_place_or_change_its_bit held.2.prefixSafe).2
    pure ⟨seed,rfl,held.2.selected.selectedPath,rfl,exact_named_field_is_an_original_outer_graph_edge476 held.2,
      fun c => Bool.false_ne_true (h.mpr c)⟩

structure MixedFieldReport477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n)
    (route : List (StepWire × Checkpoint n)) where
  fieldTail : terminalIsField ⟨first,route⟩ = true
  captured : LocatedCapture476 w.offered
  executed : readLocatedAtHead476 r = some captured
  seed : MixedInputSeed477 fixed table rel outer first
  result : MixedPoint477 r table rel
  visits : MixedTrail477 captured seed.start route result

def readMixedFieldReport477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n)
    (route : List (StepWire × Checkpoint n)) :
    Option (MixedFieldReport477 fixed table rel outer first route) :=
  if tail : terminalIsField ⟨first,route⟩ = true then
    match ran : readLocatedAtHead476 r with
    | none => none
    | some trace => do
      let seed ← readMixedInputSeed477 fixed table rel outer first
      let result ← readMixedTrail477 trace seed.start route
      pure ⟨tail,trace,ran,seed,result.1,result.2⟩
  else none

theorem mixed_field_report_keeps_same_input_and_finishes_at_the_actual_quotient477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer first : Checkpoint n}
    {route : List (StepWire × Checkpoint n)}
    (read : MixedFieldReport477 fixed table rel outer first route) :
    read.result.pose = fixed.path ++ route.flatMap (fun x => x.1.written) ∧
    read.result.compiled = [.field fixed.label] ++ route.map (fun x => oneCompiledStep477 x.1.action) ∧
    oldPosition table read.result.checkpoint.which = read.result.place ∧
    (read.result.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) read.result.checkpoint.which) ∧
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable r.head.orig.capture.lower) rebuilt) ∧
        Walk .actual rebuilt r.head.orig.code read.captured.uses := by
  have path := mixed_trail_keeps_both_paths_and_terminal_is_exact477 read.visits
  rw [read.seed.original] at path
  rw [read.seed.compiled] at path
  exact ⟨path.1,path.2.1,(checkpoint_does_not_substitute_a_place_or_change_its_bit read.result.checked).1,
    path.2.2,located_capture_uses_one_actual_typing_walk_in_every_fit476 r read.executed⟩

theorem mixed_field_report_preserves_full_safe_path_after_its_original_root477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer first : Checkpoint n}
    {route : List (StepWire × Checkpoint n)}
    (read : MixedFieldReport477 fixed table rel outer first route) :
    SafeEdgeTrail477 (CommonRoleRegularGraph.successors (graphOf p.old.state.core table))
      (ReturnsUpToEquality (graphOf p.old.state.core table)) outer.which
      (first.which :: route.map fun x => x.2.which) read.result.checkpoint.which := by
  have trail := mixed_trail_contains_actual_edges_and_only_safe_proper_prefixes477 read.visits
  rw [read.seed.sameCheckpoint] at trail
  exact .step read.seed.rooted read.seed.safe trail

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

