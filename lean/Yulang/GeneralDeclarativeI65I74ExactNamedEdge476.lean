import Yulang.GeneralDeclarativeI65I74NamedQuotientSemantics476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationSyntax471 (Slot description_exact)
open ObservationAlternatives473
open QuotientObservation471 (ExactCone cone_replay_sound projectNode embedded cone)
open LiteralVisits473 (Checkpoint readCheck)
open CommonRoleRegularGraph (successors)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralDeclarativeHead320 (environment)
open FiniteWorklist (Path)
open QuotientObservation471 (classOf)

theorem accepted_outer_cone_keeps_distinct_resolved_cells476
    {s : GeneralDeclarativeI65.State} {table : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : QuotientObservation471.ConeWire n m}
    {q : QuotientObservation471.Wire m k} {b}
    (run : readAlternatives s table rel root scope q = some b) :
    (List.ofFn (oldPosition table)).Nodup ∧ graphOf s table root ≠ .unresolved := by
  unfold readAlternatives at run
  split at run
  · rename_i guards
    have summary := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp guards).1).1).1
    have nodes : (List.ofFn (oldPosition table)).Nodup := (of_decide_eq_true summary).2
    have exactScope : ExactCone (graphOf s table) root scope := (cone_replay_sound run).1
    have resolved : graphOf s table (embedded scope scope.site) ≠ .unresolved := by
      rw [exactScope.2.2.2]
      have yes := exactScope.2.2.1 scope.site
      cases atNode : cone scope scope.site <;> simp_all [projectNode]
    simpa [exactScope.1] using And.intro nodes resolved
  · cases run

theorem distinct_observation_cells_have_unique_literal_indices476
    {table : Positions n} (distinct : (List.ofFn (oldPosition table)).Nodup)
    (i j : Fin n) (same : oldPosition table i = oldPosition table j) : i = j := by
  apply Fin.ext
  have hi : i.val < (List.ofFn (oldPosition table)).length := by simp
  have hj : j.val < (List.ofFn (oldPosition table)).length := by simp
  apply distinct.eq_of_getElem_eq hi hj
  simpa only [List.getElem_ofFn] using same

theorem exact_named_field_is_an_original_outer_graph_edge476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) :
    inner.which ∈ successors (graphOf p.old.state.core table) outer.which := by
  have outerRead : readAlternatives p.old.state.core table rel outer.which
      outer.scope outer.partition = some false := by
    simpa [readCheck,answer.actualOuter.1] using answer.prefixSafe
  obtain ⟨distinct,closed⟩ := accepted_outer_cone_keeps_distinct_resolved_cells476 outerRead
  obtain ⟨raw,label,fields,indices,rawRead,desc,mapIndices,links⟩ :=
    a_closed_old_read_node_uses_all_and_only_its_ordered_literal_successors closed
  obtain ⟨owner,physical,_,spelled⟩ :=
    a_resolved_logical_node_reuses_its_actual_alias_and_physical_owner_row answer.actualOuter.1 rawRead
  have pinned := (literal_frame_and_input_rows_before_any_capture r).2.2.2.1
  rw [answer.actualOuter.2] at physical
  have ownerExact := Option.some.inj (physical.symm.trans pinned)
  have knownField := (forwarded_old_read_uses_the_very_same_prechecked_head_and_row r q.field q.writtenPath
    answer.selected.field).2
  have sameRaw : raw = answer.selected.field.row.right :=
    (congrArg (fun e : GeneralDeclarativeHead320.Equation => e.right) (knownField.trans ownerExact.symm)).trans spelled |>.symm
  have d := description_exact.mpr desc
  rw [sameRaw] at d
  have f := description_exact.mpr answer.selected.field.rowObservation
  have sameFields : fields = answer.selected.field.rowChildren := congrArg Prod.snd (Option.some.inj (d.symm.trans f))
  have child : ((Slot.field q.field),answer.selected.field.actualPayload) ∈ fields := by
    rw [sameFields]
    exact answer.selected.field.borrowedAtField
  obtain ⟨target,seen,picked⟩ :=
    map_some_indexes_every_selected_operand (fun c => findPosition table
      (anchorFor (table.cells.get outer.which) c.1 c.2)) mapIndices child
  have same := found_position_is_literal picked
  simp only [answer.selected.sameNamedChild,anchorFor] at same
  have sameIndex := distinct_observation_cells_have_unique_literal_indices476 distinct _ _
    (same.trans answer.actualInner.1.symm)
  rw [links,←sameIndex]
  exact seen

theorem named_field_value_is_the_same_actual_selected_raw_operand476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) (m : Model) :
    interpretedAt p.old.state.core table m.assignment inner.which =
      value (environment m.assignment) .actual answer.selected.field.actualPayload := by
  rw [answer.selected.sameNamedChild]
  simp [interpretedAt,answer.actualInner.1,value,environment]

theorem positive_named_cycle_is_rooted_at_the_actual_selected_raw_operand476
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    {r : BeforeCapture a gd w} {fixed : FixedFieldChoice476 r} {q : NamedSelectionWire476}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer inner : Checkpoint n}
    (answer : NamedFieldQuotient476 fixed q table rel outer inner) (yes : answer.bit = true) :
    inner.which ∈ successors (graphOf p.old.state.core table) outer.which ∧
    ∃ first last : Fin inner.m,
      first ∈ successors (cone inner.scope) inner.scope.site ∧
      Path (successors (cone inner.scope)) first last ∧
      classOf inner.partition last = classOf inner.partition inner.scope.site ∧
      ∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core table m.assignment (embedded inner.scope last))
          (value (environment m.assignment) .actual answer.selected.field.actualPayload) := by
  refine ⟨exact_named_field_is_an_original_outer_graph_edge476 answer,?_⟩
  obtain ⟨first,last,edge,trail,returns,meaning⟩ :=
    positive_named_field_returns_to_its_checked_type_in_every_fit476 answer yes
  refine ⟨first,last,edge,trail,returns,?_⟩
  intro m fit
  have certified : readAlternatives p.old.state.core table rel inner.which inner.scope inner.partition = some true := by
    simpa [readCheck,answer.actualInner.1,yes] using answer.innerCheck
  have innerScope : ExactCone (graphOf p.old.state.core table) inner.which inner.scope := by
    unfold readAlternatives at certified
    split at certified
    · exact (cone_replay_sound certified).1
    · cases certified
  simpa only [innerScope.1,named_field_value_is_the_same_actual_selected_raw_operand476 answer m] using meaning m fit

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
