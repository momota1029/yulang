import Yulang.GeneralDeclarativeI65I74NamedPathHop477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open LiteralVisits473 (Checkpoint StepWire ReadStep readCheck childSlot)
open ObservationAlternatives473
open ObservationSyntax471 (Slot descend description_exact one_step_raw_lexical_position_is_the_actual_selected_operand)
open CommonRoleRegularGraph (successors)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)

theorem checked_step_operand_is_actual_edge_at_either_place477
    {s : GeneralDeclarativeI65.State} {table : Positions n} {rel : List (Fin n × Fin n)}
    {here : Checkpoint n} {p query raw whereAt bit}
    (check : readCheck s table rel whereAt here = some bit)
    (stored : readTermAt s table here.which = some raw)
    {wire : StepWire} (step : ReadStep s wire p query raw) :
    ∃ i, i ∈ successors (graphOf s table) here.which ∧
      oldPosition table i = anchorFor (table.cells.get here.which) (childSlot wire.action) step.actualRawChild := by
  obtain ⟨pin,_⟩ := LiteralVisits473.checkpoint_does_not_substitute_a_place_or_change_its_bit check
  have replay : readAlternatives s table rel here.which here.scope here.partition = some bit := by
    simpa [readCheck,pin] using check
  obtain ⟨_,known⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨actual,label,fields,children,read,desc,all,exact⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors known
  have same : actual = raw := Option.some.inj (read.symm.trans stored)
  subst actual
  have sameFields : fields = step.rawChildren := congrArg Prod.snd (Option.some.inj
    ((description_exact.mpr desc).symm.trans (description_exact.mpr step.exactRaw)))
  have pickedChild : (childSlot wire.action,step.actualRawChild) ∈ fields := by
    rw [sameFields]
    exact step.exactRawChild
  obtain ⟨idx,kept,atIndex⟩ :=
    map_some_indexes_every_selected_operand
      (fun item => findPosition table (anchorFor (table.cells.get here.which) item.1 item.2)) all pickedChild
  exact ⟨idx,exact ▸ kept,found_position_is_literal atIndex⟩

theorem positional_pin_forces_the_same_actual_edge477
    {s : GeneralDeclarativeI65.State} {table : Positions n} {rel : List (Fin n × Fin n)}
    {here : Checkpoint n} {p query raw whereAt bit}
    (check : readCheck s table rel whereAt here = some bit)
    (stored : readTermAt s table here.which = some raw)
    {wire : StepWire} (step : ReadStep s wire p query raw) {i : Fin n}
    (atNext : oldPosition table i = anchorFor (table.cells.get here.which) (childSlot wire.action) step.actualRawChild) :
    i ∈ successors (graphOf s table) here.which := by
  obtain ⟨pin,_⟩ := LiteralVisits473.checkpoint_does_not_substitute_a_place_or_change_its_bit check
  have replay : readAlternatives s table rel here.which here.scope here.partition = some bit := by
    simpa [readCheck,pin] using check
  obtain ⟨unique,_⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨j,edge,atJ⟩ := checked_step_operand_is_actual_edge_at_either_place477 check stored step
  have same := distinct_observation_cells_have_unique_literal_indices476 unique j i (atJ.trans atNext.symm)
  exact same ▸ edge

theorem actual_inline_term_has_one_original_row_and_path477
    {s : GeneralDeclarativeI65.State} {table : Positions n} {i : Fin n}
    {ord : Nat} {path : List Slot} {raw : Expr}
    (pin : oldPosition table i = .rowPos ord path)
    (read : readTermAt s table i = some raw) :
    ord = (table.cells.get i).oldOrdinal ∧
    ∃ row, s.current.ordinary.equations[ord]? = some row ∧ descend s row.right path = some raw := by
  unfold oldPosition at pin
  unfold readTermAt at read
  cases row : s.current.ordinary.equations[(table.cells.get i).oldOrdinal]? with
  | none => simp [row,bind,Option.bind] at read
  | some eq =>
    by_cases correct : ord = (table.cells.get i).oldOrdinal
    · have found : s.current.ordinary.equations[ord]? = some eq := correct.symm ▸ row
      have h : descend s eq.right path = some raw := by
        simpa [row,bind,Option.bind,pin,correct] using read
      exact ⟨correct,eq,found,h⟩
    · simp [row,bind,Option.bind,pin,correct] at read

theorem incoming_inline_term_is_exact_selected_operand477
    {s : GeneralDeclarativeI65.State} {table : Positions n} {rel : List (Fin n × Fin n)}
    {next : Checkpoint n} {b p query raw}
    {ord : Nat} {path : List Slot} {row : Equation}
    (atRow : s.current.ordinary.equations[ord]? = some row)
    (stored : descend s row.right path = some raw)
    {wire : StepWire} (step : ReadStep s wire p query raw)
    (there : readCheck s table rel (.rowPos ord (path ++ [childSlot wire.action])) next = some b) :
    readTermAt s table next.which = some step.actualRawChild := by
  obtain ⟨loc,_⟩ := LiteralVisits473.checkpoint_does_not_substitute_a_place_or_change_its_bit there
  have replay : readAlternatives s table rel next.which next.scope next.partition = some b := by
    simpa [readCheck,loc] using there
  obtain ⟨_,known⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 replay
  obtain ⟨actual,_,_,_,actualRead,_,_,_⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors known
  obtain ⟨_,chosen,whereChosen,descChosen⟩ := actual_inline_term_has_one_original_row_and_path477 loc actualRead
  have same : chosen = row := Option.some.inj (whereChosen.symm.trans atRow)
  subst chosen
  have literal := one_step_raw_lexical_position_is_the_actual_selected_operand stored step.exactRaw step.exactRawChild
  exact Option.some.inj (descChosen.symm.trans literal) ▸ actualRead

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

