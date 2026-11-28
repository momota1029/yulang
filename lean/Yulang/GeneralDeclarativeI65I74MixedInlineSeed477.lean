import Yulang.GeneralDeclarativeI65I74MixedLiteralTrail477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open ObservationAlternatives473
open ObservationSyntax471 (Slot ReadsDescription confirmedAddress description_exact descend)
open LiteralVisits473 (Checkpoint readCheck checkpoint_does_not_substitute_a_place_or_change_its_bit)
open CommonRoleRegularGraph (successors)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

private theorem outer_checked_raw_read477
    {r : BeforeCapture (p := p) a gd w} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer : Checkpoint n}
    (pin : atNamedCell476 table outer.which r.head.orig.capture.lower r.picked.raw)
    (guard : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) outer = some false) :
    readTermAt p.old.state.core table outer.which = some r.picked.row.right := by
  have replay : readAlternatives p.old.state.core table rel outer.which outer.scope outer.partition = some false :=
    by simpa [readCheck,pin.1] using guard
  obtain ⟨_,known⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨actual,_,_,_,read,_,_,_⟩ := a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors known
  obtain ⟨row,whereAt,_,showing⟩ :=
    a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row pin.1 read
  rw [pin.2] at whereAt
  change (rawAt p).equations[r.picked.raw]? = some row at whereAt
  have exact := (literal_frame_and_input_rows_before_any_capture r).2.2.2.1
  have same := Option.some.inj (whereAt.symm.trans exact)
  rw [←same,showing]
  exact read

private theorem borrowed_original_field_is_real_successor477
    {r : BeforeCapture (p := p) a gd w} (fixed : FixedFieldChoice476 r)
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer : Checkpoint n}
    (pin : atNamedCell476 table outer.which r.head.orig.capture.lower r.picked.raw)
    (guard : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) outer = some false) :
    ∃ whereAt, whereAt ∈ successors (graphOf p.old.state.core table) outer.which ∧
      oldPosition table whereAt =
        anchorFor (table.cells.get outer.which) (.field fixed.label) fixed.original.actualPayload := by
  have replay : readAlternatives p.old.state.core table rel outer.which outer.scope outer.partition = some false :=
    by simpa [readCheck,pin.1] using guard
  obtain ⟨_,known⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨actual,label,fields,children,read,desc,all,exact⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors known
  have body := outer_checked_raw_read477 pin guard
  have exactBody : actual = r.picked.row.right := Option.some.inj (read.symm.trans body)
  have rowEq := (forwarded_old_read_uses_the_very_same_prechecked_head_and_row r _ _ fixed.original).2
  have d := description_exact.mpr desc
  rw [exactBody,←rowEq] at d
  have eq : fields = fixed.original.rowChildren := congrArg Prod.snd
    (Option.some.inj (d.symm.trans (description_exact.mpr fixed.original.rowObservation)))
  have selected : (.field fixed.label,fixed.original.actualPayload) ∈ fields := by
    rw [eq]
    exact fixed.original.borrowedAtField
  obtain ⟨i,edge,atIndex⟩ :=
    map_some_indexes_every_selected_operand
      (fun item => findPosition table (anchorFor (table.cells.get outer.which) item.1 item.2)) all selected
  exact ⟨i,exact ▸ edge,found_position_is_literal atIndex⟩

structure MixedInlineSeed477
    {r : BeforeCapture (p := p) a gd w} (fixed : FixedFieldChoice476 r)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer atField : Checkpoint n) where
  outerPin : atNamedCell476 table outer.which r.head.orig.capture.lower r.picked.raw
  outerSafe : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) outer = some false
  ordinal : Nat
  lexical : List Slot
  addr : confirmedAddress fixed.original = .inline ordinal lexical
  exactAnchor : .rowPos ordinal lexical =
    anchorFor (table.cells.get outer.which) (.field fixed.label) fixed.original.actualPayload
  found : readTermAt p.old.state.core table atField.which = some fixed.original.actualPayload
  bit : Bool
  checked : readCheck p.old.state.core table rel (.rowPos ordinal lexical) atField = some bit

def readMixedInlineSeed477 {r : BeforeCapture (p := p) a gd w}
    (fixed : FixedFieldChoice476 r) (table : Positions n) (rel : List (Fin n × Fin n))
    (outer atField : Checkpoint n) : Option (MixedInlineSeed477 fixed table rel outer atField) :=
  if pin : atNamedCellTest476 table outer.which r.head.orig.capture.lower r.picked.raw = true then
    match safe : readCheck p.old.state.core table rel (.logical r.head.orig.capture.lower) outer with
    | some false =>
      match addr : confirmedAddress fixed.original with
      | .named _ => none
      | .inline old route =>
        if exact : .rowPos old route =
          anchorFor (table.cells.get outer.which) (.field fixed.label) fixed.original.actualPayload then
          match found : readTermAt p.old.state.core table atField.which with
          | none => none
          | some child =>
            if same : eqExpr child fixed.original.actualPayload = true then
              match check : readCheck p.old.state.core table rel (.rowPos old route) atField with
              | none => none
              | some bit => some ⟨(exact_named_cell_test476 ..).mp pin,safe,old,route,addr,exact,
                by rw [(eq_expr ..).mp same] at found; exact found,bit,check⟩
            else none
        else none
    | _ => none
  else none

def MixedInlineSeed477.point {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    (seed : MixedInlineSeed477 fixed table rel outer atField) :
    MixedPoint477 r table rel :=
  ⟨fixed.original.sourcePattern,fixed.original.selectedQuery,fixed.path,
    by
      have id := (forwarded_old_read_uses_the_very_same_prechecked_head_and_row r _ _ fixed.original).1
      have site := literal_occurrence fixed.original.selectedWritten
      rw [id] at site
      exact site,
    [.field fixed.label],fixed.original.actualPayload,.rowPos seed.ordinal seed.lexical,atField,
    seed.found,seed.bit,seed.checked⟩

theorem inline_seed_is_exact_old_source_and_original_graph_edge477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    (seed : MixedInlineSeed477 fixed table rel outer atField) :
    atField.which ∈ successors (graphOf p.old.state.core table) outer.which ∧
    (atSource r.head.orig.original seed.point.pose = some fixed.original.sourcePattern) ∧
    (oldPosition table atField.which = .rowPos seed.ordinal seed.lexical) := by
  have replay : readAlternatives p.old.state.core table rel outer.which outer.scope outer.partition = some false :=
    by simpa [readCheck,seed.outerPin.1] using seed.outerSafe
  obtain ⟨unique,_⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨i,edge,node⟩ := borrowed_original_field_is_real_successor477 fixed seed.outerPin seed.outerSafe
  have pin := (checkpoint_does_not_substitute_a_place_or_change_its_bit seed.checked).1
  have eq := distinct_observation_cells_have_unique_literal_indices476 unique i atField.which
    (node.trans (pin.trans seed.exactAnchor).symm)
  exact ⟨eq ▸ edge,seed.point.written,pin⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

