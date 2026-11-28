import Yulang.GeneralDeclarativeI65I74TypedCompletedFocus482
import Yulang.GeneralDeclarativeI65I74TypedFocusMeaning482
import Yulang.GeneralDeclarativeInlineFootprint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open NativeProducer465 (CheckedPhase)
open Producer479 (PriorPhase Site)
open InputCoordinates475 (rawAt SourceIndexPair478)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineTrace331 (realize)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralDeclarativeHead320 (Equation)

theorem all_checked_projection_visits_use_the_same_original_completed_models
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {here : Site p.old.state.core pos} {card : ReadCard} {moves final selected reads}
    (a : Attached (rawAt p) table)
    (path : FocusedChain (p := p) (visibleReadView table) here card moves final selected reads) :
    FocusMeaning (p := p) (visibleReadView table) here card moves final selected reads := by
  induction path with
  | stop => exact .stop
  | step step _ ih =>
    refine .step step ?_ ih
    have arrival := scoped_selected_arrival_means_the_exact_typed_raw_child
      (visible_projected_rows_are_existing_physical_equations a) step.sameRow
    have used := GeneralDeclarativeInlineFootprint331.trace step.typed
    obtain ⟨facts,covered,continued⟩ := used
    have proved := continued (restriction (support a)) rfl
      (fun fact present => (visible_read_view_reflects_existing_authority a fact).mp (covered present))
    obtain ⟨rebuilt,source,walk⟩ := realize proved
    exact ⟨rebuilt,fun m fit => eqv_trans (eqv_symm (arrival m fit)) (source m.assignment fit.1.1.1),walk⟩

theorem each_named_visit_has_exact_original_scope_and_completion_ordinals
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {here : Site p.old.state.core pos} {card : ReadCard} {moves final selected reads}
    (path : FocusedChain (p := p) (visibleReadView table) here card moves final selected reads) :
    ∀ entry : SourceIndexPair478, some entry ∈ reads →
    ∃ (row : Equation) (origin : ReadRowAuthority),
      (rawAt p).equations[entry.raw]? = some row ∧
      (visibleWithAuthority table)[entry.author]? = some (origin,row) ∧ origin.Valid table row := by
  induction path with
  | stop => intro _ absent; cases absent
  | @step here action card rest last terminal later chosen step path ih =>
    intro entry present
    rcases List.mem_cons.mp present with first|after
    · have exactArrival := checked_arrival_is_exact_original_source_row_or_literal_term step.sameRow
      rcases exactArrival with ⟨empty,_,_⟩ | ⟨_,idx,row,_,named,_,raw,projected,_,_⟩
      · rw [empty] at first
        cases first
      · rw [named] at first
        have same := Option.some.inj first
        subst entry
        obtain ⟨tag,atMark,valid⟩ :=
          each_projected_view_slot_has_original_ordinal_authority _ _ _ projected
        exact ⟨row,tag,raw,atMark,valid⟩
    · exact ih entry after

theorem completed_focus_retains_every_original_support_and_types_each_visited_site
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {wire : CompletedFocusWire n} (x : CompletedFocus p gd pos rel basis phase wire) :
    FocusMeaning (p := p) (visibleReadView basis.authors) x.focused.here wire.focus.source wire.focus.route.trail.tail
      x.focused.reportTrace.focus.finish x.focused.reportTrace.focus.selected x.focused.reportTrace.focus.reads ∧
    ∀ entry : SourceIndexPair478, some entry ∈ x.focused.reportTrace.focus.reads →
      ∃ (row : Equation) (origin : ReadRowAuthority),
        (rawAt p).equations[entry.raw]? = some row ∧
        (visibleWithAuthority basis.authors)[entry.author]? = some (origin,row) ∧ origin.Valid basis.authors row :=
  ⟨all_checked_projection_visits_use_the_same_original_completed_models
    x.attached x.focused.reportTrace.focus.trail,
    each_named_visit_has_exact_original_scope_and_completion_ordinals x.focused.reportTrace.focus.trail⟩


theorem completed_focus_preserves_exact_installed_value_in_every_original_fit
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {phase : CheckedPhase p.old.state.core}
    {wire : CompletedFocusWire n} (x : CompletedFocus p gd pos rel basis phase wire)
    (m : Model) (fit : FitsFull p.state m) :
    m.nativeSyntax wire.release.write.address.target =
      some (GeneralDeclarativeWitnessNativeOrder362.node wire.release.write.code) ∧
    GeneralDeclarativeWitnessNativeInstall360.interpreted phase.world.board m.assignment
      wire.release.write.address.target = some (wire.release.write.code.eval m.assignment) := by
  have checked := (completed_focus_reads_same_ordinary_row_and_exact_active_native_release x).2.2.2.2
  exact NativeProducer465.actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit
    ((NativeProducer465.finite_phase_origin_check_iff_literal_placed_active_row ..).mpr checked) m fit.1

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
