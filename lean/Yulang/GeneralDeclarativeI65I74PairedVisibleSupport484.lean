import Yulang.GeneralDeclarativeI65I74SignedInteriorPath483
import Yulang.GeneralDeclarativeI65I74TypedCompletedVisitMeaning482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions)
open Producer479 (Site)
open InputCoordinates475 (rawAt SourceIndexPair478)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineTrace331 (realize)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralDeclarativeHead320 (Equation)

inductive InteriorSourceOrCompletion {p : FullProblem} {pos : Positions n} (table : Table) :
    Site p.old.state.core pos → Site p.old.state.core pos → ReadCard → List (InteriorMove n) →
    List (Site p.old.state.core pos × Site p.old.state.core pos) → Prop where
  | nil : InteriorSourceOrCompletion table left right card [] []
  | cons
      (visit : PairedFocusedHop (p := p) (visibleReadView table) left right move.step card move.author move.ambient) :
      (∀ entry : SourceIndexPair478, visit.author.chosenSource = some entry →
        ∃ (row : Equation) (origin : ReadRowAuthority),
          (rawAt p).equations[entry.raw]? = some row ∧
          (visibleWithAuthority table)[entry.author]? = some (origin,row) ∧ origin.Valid table row) →
      InteriorSourceOrCompletion table visit.author.after visit.ambient visit.author.childCard more rest →
      InteriorSourceOrCompletion table left right card (move::more) ((visit.author.after,visit.ambient)::rest)

theorem paired_visible_path_retains_original_completed_support_and_same_models
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path}
    (attached : Attached (rawAt p) table)
    (chosen : InteriorSequence (p := p) (visibleReadView table) left right card moves path) :
    InteriorMeaning (p := p) (visibleReadView table) left right card moves path ∧
    InteriorSourceOrCompletion (p := p) table left right card moves path := by
  induction chosen with
  | nil => exact ⟨.nil,.nil⟩
  | cons visit _ _ _ ih =>
    refine ⟨.cons visit ?_ ih.1,.cons visit ?_ ih.2⟩
    · have original := scoped_selected_arrival_means_the_exact_typed_raw_child
        (visible_projected_rows_are_existing_physical_equations attached) visit.author.sameRow
      obtain ⟨facts,covered,replay⟩ := GeneralDeclarativeInlineFootprint331.trace visit.author.typed
      have read := replay (restriction (support attached)) rfl
        (fun row hit => (visible_read_view_reflects_existing_authority attached row).mp (covered hit))
      obtain ⟨rebuilt,typed,W⟩ := realize read
      exact ⟨rebuilt,fun m fit => eqv_trans (eqv_symm (original m fit)) (typed m.assignment fit.1.1.1),W⟩
    · intro entry selected
      obtain literal | ⟨_,idx,row,_,stored,_,raw,view,_,_⟩ :=
        checked_arrival_is_exact_original_source_row_or_literal_term visit.author.sameRow
      · rw [literal.1] at selected
        cases selected
      · have same := Option.some.inj (stored.symm.trans selected)
        subst entry
        obtain ⟨tag,whereFrom,valid⟩ := each_projected_view_slot_has_original_ordinal_authority _ _ _ view
        exact ⟨row,tag,raw,whereFrom,valid⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
