import Yulang.GeneralDeclarativeI65I74DeeperLiteralNamed477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence)
open WrittenPattern460 (Address)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open LiteralVisits473 (StepWire ReadStep Checkpoint readCheck readLiteralVisitStep
  written_pose_append_is_exact childSlot independent_step_derivation_replays_its_original_addresses
  checkpoint_does_not_substitute_a_place_or_change_its_bit)
open ObservationAlternatives473
open ObservationSyntax471 (descend one_step_raw_lexical_position_is_the_actual_selected_operand)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

structure NamedCheckpoint477 {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w) (trace : LocatedCapture476 w.offered)
    (table : Positions n) (rel : List (Fin n × Fin n)) where
  source : Pattern
  code : Expr
  pose : List Pose
  written : atSource r.head.orig.original pose = some source
  mark : LocatedMark476 w.offered
  ordinal : Nat
  stamped : trace.marks[ordinal]? = some mark
  checkpoint : Checkpoint n
  actual : atNamedCell476 table checkpoint.which mark.exposure.name mark.exposure.picked.raw
  bit : Bool
  returned : readCheck p.old.state.core table rel (.logical mark.exposure.name) checkpoint = some bit

def firstNamedCheckpoint477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) :
    NamedCheckpoint477 r answer.selected.trace table rel :=
  ⟨answer.selected.field.sourcePattern,answer.selected.field.selectedQuery,q.writtenPath,
   literal_occurrence (checked_field_and_mark_retain_distinct_exact_source_positions476 answer.selected).1,
   answer.selected.mark,q.markOrdinal,answer.selected.chosen,inner,answer.actualInner,answer.bit,answer.innerCheck⟩

theorem named_checkpoint_carries_exact_written_raw_and_author_occurrences477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) :
    atSource r.head.orig.original c.pose = some c.source ∧
    (rawAt p).equations[c.mark.exposure.picked.raw]? = some c.mark.exposure.picked.row ∧
    t.authored[c.mark.exposure.picked.author]? = some c.mark.exposure.picked.row ∧
    (c.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) c.checkpoint.which) :=
  ⟨c.written,(a_marked_name_exposure_keeps_both_exact_original_rows r c.mark.exposure).1,
   (a_marked_name_exposure_keeps_both_exact_original_rows r c.mark.exposure).2.1,
   (checkpoint_does_not_substitute_a_place_or_change_its_bit c.returned).2⟩

theorem named_checkpoint_selected_operand_is_real477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel)
    {step : StepWire}
    (next : ReadStep p.old.state.core step c.source c.code c.mark.exposure.picked.row.right) :
    ∃ arrived, arrived ∈ successors (graphOf p.old.state.core table) c.checkpoint.which ∧
      oldPosition table arrived =
        anchorFor (table.cells.get c.checkpoint.which) (childSlot step.action) next.actualRawChild := by
  have replay : readAlternatives p.old.state.core table rel c.checkpoint.which c.checkpoint.scope c.checkpoint.partition =
      some c.bit := by simpa [readCheck,c.actual.1] using c.returned
  obtain ⟨_,resolved⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨raw,label,fields,children,read,desc,all,exact⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors resolved
  obtain ⟨row,atRow,_,spelling⟩ :=
    a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row c.actual.1 read
  have own := (named_checkpoint_carries_exact_written_raw_and_author_occurrences477 c).2.1
  rw [c.actual.2] at atRow
  have sameRow := Option.some.inj (atRow.symm.trans own)
  have rawEq : raw = c.mark.exposure.picked.row.right := by
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
      (fun item => findPosition table (anchorFor (table.cells.get c.checkpoint.which) item.1 item.2)) all pickedChild
  exact ⟨idx,exact ▸ kept,found_position_is_literal atIndex⟩




structure NamedPathStepWire477 (n : Nat) where
  literal : StepWire
  arriveOrdinal : Nat
  arriveCheck : Checkpoint n

structure NamedPathHop477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (wire : @NamedPathStepWire477 n) where
  safe : c.bit = false
  next : ReadStep p.old.state.core wire.literal c.source c.code c.mark.exposure.picked.row.right
  stamp : LocatedMark476 w.offered
  chosen : trace.marks[wire.arriveOrdinal]? = some stamp
  path : stamp.path = c.mark.path ++ [oneCompiledStep477 wire.literal.action]
  rawChild : next.actualRawChild = .variable stamp.exposure.name
  actual : atNamedCell476 table wire.arriveCheck.which stamp.exposure.name stamp.exposure.picked.raw
  bit : Bool
  hit : readCheck p.old.state.core table rel (.logical stamp.exposure.name) wire.arriveCheck = some bit

def NamedPathHop477.endPoint {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {wire : @NamedPathStepWire477 n}
    (hop : NamedPathHop477 c wire) : NamedCheckpoint477 r trace table rel :=
  ⟨hop.next.writtenChild,hop.next.childQuery,c.pose ++ wire.literal.written,
    by rw [written_pose_append_is_exact,c.written]; exact literal_occurrence hop.next.writtenFrom,
    hop.stamp,wire.arriveOrdinal,hop.chosen,wire.arriveCheck,hop.actual,hop.bit,hop.hit⟩

def readNamedPathHop477 {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    (c : NamedCheckpoint477 r trace table rel) (wire : @NamedPathStepWire477 n) :
    Option (NamedPathHop477 c wire) :=
  if safe : c.bit = false then do
    let next ← readLiteralVisitStep p.old.state.core c.source c.code c.mark.exposure.picked.row.right wire.literal
    match chosen : trace.marks[wire.arriveOrdinal]? with
    | none => none
    | some stamp =>
      if path : stamp.path = c.mark.path ++ [oneCompiledStep477 wire.literal.action] then
        if child : eqExpr next.actualRawChild (.variable stamp.exposure.name) = true then
          if pin : atNamedCellTest476 table wire.arriveCheck.which stamp.exposure.name stamp.exposure.picked.raw = true then
            match hit : readCheck p.old.state.core table rel (.logical stamp.exposure.name) wire.arriveCheck with
            | none => none
            | some bit => some ⟨safe,next,stamp,chosen,path,(eq_expr ..).mp child,
                (exact_named_cell_test476 ..).mp pin,bit,hit⟩
          else none
        else none
      else none
  else none

theorem named_path_hop_has_exact_replay477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {wire : @NamedPathStepWire477 n}
    (hop : NamedPathHop477 c wire) : readNamedPathHop477 c wire = some hop := by
  rcases hop with ⟨safe,next,stamp,chosen,path,rawChild,actual,bit,hit⟩
  have literal := independent_step_derivation_replays_its_original_addresses next
  have child := (eq_expr ..).mpr rawChild
  have pin := (exact_named_cell_test476 ..).mpr actual
  simp only [readNamedPathHop477,safe,dite_true,literal,bind,Option.bind]
  split
  · rename_i absent
    rw [chosen] at absent
    contradiction
  · rename_i picked seen
    have same := Option.some.inj (seen.symm.trans chosen)
    subst picked
    simp only [path, child, pin, dite_true]
    split
    · rename_i absent
      rw [hit] at absent
      contradiction
    · rename_i got seen
      have same := Option.some.inj (seen.symm.trans hit)
      subst got
      rfl

theorem named_path_hop_has_real_edge_and_safe_source477 {n : Nat} {p : FullProblem} {t : Table}
    {a : Attached (rawAt p) t} {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {trace : LocatedCapture476 w.offered}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {c : NamedCheckpoint477 r trace table rel} {wire : @NamedPathStepWire477 n}
    (hop : NamedPathHop477 c wire) :
    wire.arriveCheck.which ∈ successors (graphOf p.old.state.core table) c.checkpoint.which ∧
    ¬ ReturnsUpToEquality (graphOf p.old.state.core table) c.checkpoint.which := by
  obtain ⟨endAt,isEdge,whereAt⟩ := named_checkpoint_selected_operand_is_real477 c hop.next
  rw [hop.rawChild] at whereAt
  have replay : readAlternatives p.old.state.core table rel c.checkpoint.which c.checkpoint.scope
      c.checkpoint.partition = some c.bit := by simpa [readCheck,c.actual.1] using c.returned
  have distinct := (accepted_outer_cone_keeps_distinct_resolved_cells476 replay).1
  have same := distinct_observation_cells_have_unique_literal_indices476 distinct _ _
    (whereAt.trans hop.actual.1.symm)
  refine ⟨same ▸ isEdge,?_⟩
  intro back
  exact Bool.false_ne_true (hop.safe.symm.trans
    ((checkpoint_does_not_substitute_a_place_or_change_its_bit c.returned).2.mpr back))

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
