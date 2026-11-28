import Yulang.GeneralDeclarativeI65I74NamedFieldWitness476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (atSource literal_occurrence)
open LiteralVisits473 (StepWire ReadStep written_pose_append_is_exact childSlot)
open ObservationSyntax471 (descend one_step_raw_lexical_position_is_the_actual_selected_operand)
open GeneralDeclarativeHead320 (Equation)

theorem deeper_literal_step_after_named_capture_has_original_pose_and_old_row477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {q : NamedSelectionWire476}
    (selected : NamedSelection476 r q) {step : StepWire}
    (next : ReadStep p.old.state.core step selected.field.sourcePattern selected.field.selectedQuery
      selected.mark.exposure.picked.row.right) :
    atSource r.head.orig.original (q.writtenPath ++ step.written) = some next.writtenChild ∧
    (rawAt p).equations[selected.mark.exposure.picked.raw]? = some selected.mark.exposure.picked.row ∧
    t.authored[selected.mark.exposure.picked.author]? = some selected.mark.exposure.picked.row ∧
    descend p.old.state.core selected.mark.exposure.picked.row.right [childSlot step.action] =
      some next.actualRawChild := by
  have old := checked_field_and_mark_retain_distinct_exact_source_positions476 selected
  refine ⟨?_,old.2.1,old.2.2.1,?_⟩
  · rw [written_pose_append_is_exact,literal_occurrence old.1]
    exact literal_occurrence next.writtenFrom
  · exact one_step_raw_lexical_position_is_the_actual_selected_operand (path := []) rfl next.exactRaw next.exactRawChild

open ObservationAlternatives473
open CommonRoleRegularGraph (successors)
open LiteralVisits473 (Checkpoint readCheck)

theorem deeper_literal_operand_has_an_actual_edge_in_the_checked_named_cone477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner)
    {step : StepWire} (next : ReadStep p.old.state.core step answer.selected.field.sourcePattern
      answer.selected.field.selectedQuery answer.selected.mark.exposure.picked.row.right) :
    ∃ arrived, arrived ∈ successors (graphOf p.old.state.core table) inner.which ∧
      oldPosition table arrived =
        anchorFor (table.cells.get inner.which) (childSlot step.action) next.actualRawChild := by
  have replay : readAlternatives p.old.state.core table rel inner.which inner.scope inner.partition =
      some answer.bit := by simpa [readCheck,answer.actualInner.1] using answer.innerCheck
  obtain ⟨_,resolved⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨raw,label,fields,children,read,desc,all,exact⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors resolved
  obtain ⟨row,atRow,_,spelling⟩ :=
    a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row answer.actualInner.1 read
  have own := (checked_field_and_mark_retain_distinct_exact_source_positions476 answer.selected).2.1
  rw [answer.actualInner.2] at atRow
  have sameRow := Option.some.inj (atRow.symm.trans own)
  have rawEq : raw = answer.selected.mark.exposure.picked.row.right := by
    rw [←sameRow]
    exact spelling.symm
  have d := ObservationSyntax471.description_exact.mpr desc
  rw [rawEq] at d
  have b := ObservationSyntax471.description_exact.mpr next.exactRaw
  have sameFields : fields = next.rawChildren := congrArg Prod.snd (Option.some.inj (d.symm.trans b))
  have pickedChild : (childSlot step.action,next.actualRawChild) ∈ fields := by
    rw [sameFields]
    exact next.exactRawChild
  obtain ⟨idx,kept,atIndex⟩ :=
    map_some_indexes_every_selected_operand
      (fun c => findPosition table (anchorFor (table.cells.get inner.which) c.1 c.2)) all pickedChild
  exact ⟨idx,exact ▸ kept,found_position_is_literal atIndex⟩


open WrittenPattern460 (Address)
open LiteralVisits473 (readLiteralVisitStep independent_step_derivation_replays_its_original_addresses)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

def oneCompiledStep477 : Address → QueryStep476
  | .field label => .field label
  | .tag _ => .variantPayload
  | .arg ordinal => .argument ordinal

structure NextNamedStampWire477 where
  step : StepWire
  markOrdinal : Nat

/-- Local compatibility only. The current named field was actually
checked safe. A candidate deeper stamp must occur at exactly the
extended compiled path in that same original trace. -/
structure NextNamedStamp477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) (wire : NextNamedStampWire477) where
  safe : answer.bit = false
  next : ReadStep p.old.state.core wire.step answer.selected.field.sourcePattern
    answer.selected.field.selectedQuery answer.selected.mark.exposure.picked.row.right
  mark : LocatedMark476 w.offered
  ordinal : answer.selected.trace.marks[wire.markOrdinal]? = some mark
  path : mark.path = answer.selected.mark.path ++ [oneCompiledStep477 wire.step.action]
  payload : next.actualRawChild = .variable mark.exposure.name

def readNextNamedStamp477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) (wire : NextNamedStampWire477) :
    Option (NextNamedStamp477 answer wire) :=
  if safe : answer.bit = false then do
    let next ← readLiteralVisitStep p.old.state.core answer.selected.field.sourcePattern
      answer.selected.field.selectedQuery answer.selected.mark.exposure.picked.row.right wire.step
    match known : answer.selected.trace.marks[wire.markOrdinal]? with
    | none => none
    | some mark =>
      if path : mark.path = answer.selected.mark.path ++ [oneCompiledStep477 wire.step.action] then
        if child : eqExpr next.actualRawChild (.variable mark.exposure.name) = true then
          some ⟨safe,next,mark,known,path,(eq_expr ..).mp child⟩
        else none
      else none
  else none

theorem given_next_named_stamp_replays477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {answer : NamedFieldQuotient476 fixed q table rel outer inner} {wire : NextNamedStampWire477}
    (read : NextNamedStamp477 answer wire) : readNextNamedStamp477 answer wire = some read := by
  rcases read with ⟨safe,next,mark,chosen,path,payload⟩
  have literal := independent_step_derivation_replays_its_original_addresses next
  have body := (eq_expr ..).mpr payload
  simp only [readNextNamedStamp477,safe,dite_true,literal,bind,Option.bind]
  split
  · rename_i absent
    rw [chosen] at absent
    contradiction
  · rename_i picked hit
    have same := Option.some.inj (hit.symm.trans chosen)
    subst picked
    simp [path,body]

theorem next_named_stamp_has_exact_literal_path_and_real_graph_edge477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {answer : NamedFieldQuotient476 fixed q table rel outer inner} {wire : NextNamedStampWire477}
    (read : NextNamedStamp477 answer wire) :
    atSource r.head.orig.original (q.writtenPath ++ wire.step.written) = some read.next.writtenChild ∧
    (rawAt p).equations[read.mark.exposure.picked.raw]? = some read.mark.exposure.picked.row ∧
    t.authored[read.mark.exposure.picked.author]? = some read.mark.exposure.picked.row ∧
    ∃ arrived ∈ successors (graphOf p.old.state.core table) inner.which,
      oldPosition table arrived = .logical read.mark.exposure.name := by
  have coordinate := deeper_literal_step_after_named_capture_has_original_pose_and_old_row477 answer.selected read.next
  have mark := a_marked_name_exposure_keeps_both_exact_original_rows r read.mark.exposure
  obtain ⟨atCell,edge,anchor⟩ := deeper_literal_operand_has_an_actual_edge_in_the_checked_named_cone477 answer read.next
  rw [read.payload] at anchor
  exact ⟨coordinate.1,mark.1,mark.2.1,atCell,edge,anchor⟩


open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (checkpoint_does_not_substitute_a_place_or_change_its_bit)

structure NextNamedPointBit477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {answer : NamedFieldQuotient476 fixed q table rel outer inner} {wire : NextNamedStampWire477}
    (read : NextNamedStamp477 answer wire) (terminal : Checkpoint n) where
  actual : atNamedCell476 table terminal.which read.mark.exposure.name read.mark.exposure.picked.raw
  bit : Bool
  returned : readCheck p.old.state.core table rel (.logical read.mark.exposure.name) terminal = some bit

def readNextNamedPointBit477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {answer : NamedFieldQuotient476 fixed q table rel outer inner} {wire : NextNamedStampWire477}
    (read : NextNamedStamp477 answer wire) (terminal : Checkpoint n) :
    Option (NextNamedPointBit477 read terminal) :=
  if good : atNamedCellTest476 table terminal.which read.mark.exposure.name read.mark.exposure.picked.raw = true then
    match ran : readCheck p.old.state.core table rel (.logical read.mark.exposure.name) terminal with
    | none => none
    | some bit => some ⟨(exact_named_cell_test476 ..).mp good,bit,ran⟩
  else none

theorem next_named_bit_uses_the_actual_next_edge_and_checked_class477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    {answer : NamedFieldQuotient476 fixed q table rel outer inner} {wire : NextNamedStampWire477}
    {read : NextNamedStamp477 answer wire} {terminal : Checkpoint n}
    (bit : NextNamedPointBit477 read terminal) :
    terminal.which ∈ successors (graphOf p.old.state.core table) inner.which ∧
    ¬ ReturnsUpToEquality (graphOf p.old.state.core table) inner.which ∧
    (bit.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) terminal.which) := by
  obtain ⟨_,_,_,edge,isEdge,atEdge⟩ := next_named_stamp_has_exact_literal_path_and_real_graph_edge477 read
  have returned : readAlternatives p.old.state.core table rel inner.which inner.scope inner.partition =
      some answer.bit := by simpa [readCheck,answer.actualInner.1] using answer.innerCheck
  have distinct := (accepted_outer_cone_keeps_distinct_resolved_cells476 returned).1
  have same := distinct_observation_cells_have_unique_literal_indices476 distinct _ _ (atEdge.trans bit.actual.1.symm)
  refine ⟨same ▸ isEdge,?_,(checkpoint_does_not_substitute_a_place_or_change_its_bit bit.returned).2⟩
  intro back
  have falseAtInner := (checkpoint_does_not_substitute_a_place_or_change_its_bit answer.innerCheck).2.mpr back
  exact Bool.false_ne_true (read.safe.symm.trans falseAtInner)


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
