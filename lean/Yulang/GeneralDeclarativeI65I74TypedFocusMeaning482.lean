import Yulang.GeneralDeclarativeI65I74TypedFocusTrail482
import Yulang.GeneralDeclarativeI65I74SourceExposureMeaning481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions)
open Producer479 (Site)
open LiteralVisits473 (StepWire Checkpoint)
open InputCoordinates475 (rawAt SourceIndexPair478)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInlineTrace331 (realize)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)

theorem scoped_selected_arrival_means_the_exact_typed_raw_child
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {next : Site p.old.state.core pos} {rawChild : Expr} {nextCard : ReadCard}
    {selection : Option SourceIndexPair478}
    (anchor : Attached (rawAt p) table)
    (read : checkArrival table next rawChild nextCard = some selection) :
    ∀ m : Model, FitsFull p.state m → eqAt m.assignment rawChild next.term := by
  obtain literal | ⟨name,idx,row,shape,_,_,stored,_,related,rowTerm⟩ :=
    checked_arrival_is_exact_original_source_row_or_literal_term read
  · intro m _
    rw [literal.2.2]
    exact eqv_refl _
  · intro m fit
    rw [shape]
    have oldAlias : GeneralDeclarativeLowerKnown321.Alias (rawAt p) name row.left :=
      GeneralDeclarativeLowerKnown321.alias_mono (s := authoredView (rawAt p) table) (t := rawAt p)
        rfl anchor.authored related
    have all := fit.1.1.1
    have actualKnown := all.2 row (List.mem_of_getElem? stored)
    rw [rowTerm] at actualKnown
    exact eqv_trans (alias_sound oldAlias m.assignment all) actualKnown

theorem scoped_selected_arrival_uses_same_original_fits_and_compiled_child
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {here : Site p.old.state.core pos} {move : StepWire} {card : ReadCard} {choice : Fin n}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (anchor : Attached (rawAt p) table)
    (authority : ∀ row ∈ table.authored, support.derivesFrom row .source)
    (step : FocusedCardHop (p := p) table here move card choice) :
    ∃ rebuilt : Expr,
      (∀ m : Model, FitsFull p.state m → eqAt m.assignment step.after.term rebuilt) ∧
      Walk .actual rebuilt step.after.query step.uses := by
  have atChild := scoped_selected_arrival_means_the_exact_typed_raw_child anchor step.sameRow
  have actualRead := genuine_authored_reads_transport_into_same_support481 authority step.typed
  obtain ⟨term,source,walk⟩ := realize actualRead
  exact ⟨term,fun m fit => eqv_trans (eqv_symm (atChild m fit)) (source m.assignment fit.1.1.1),walk⟩

inductive FocusMeaning {n : Nat} {p : FullProblem} {pos : Positions n}
    (table : Table) : Site p.old.state.core pos → ReadCard → List (StepWire × Checkpoint n) →
      Site p.old.state.core pos → ReadCard → List (Option SourceIndexPair478) → Prop where
  | stop : FocusMeaning table here card [] here card []
  | step (visit : FocusedCardHop (p := p) table here action card chosen.which) :
      (∃ rebuilt, (∀ m : Model, FitsFull p.state m → eqAt m.assignment visit.after.term rebuilt) ∧
          Walk .actual rebuilt visit.after.query visit.uses) →
      FocusMeaning table visit.after visit.childCard more final terminal ordered →
      FocusMeaning table here card ((action,chosen)::more) final terminal (visit.chosenSource::ordered)

theorem every_actual_focused_site_has_typed_meaning_in_same_fits
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {here : Site p.old.state.core pos} {card : ReadCard} {more final terminal ordered}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (anchor : Attached (rawAt p) table)
    (authority : ∀ row ∈ table.authored, support.derivesFrom row .source)
    (chain : FocusedChain (p := p) table here card more final terminal ordered) :
    FocusMeaning (p := p) table here card more final terminal ordered := by
  induction chain with
  | stop => exact .stop
  | step visit _ ih =>
    exact .step visit (scoped_selected_arrival_uses_same_original_fits_and_compiled_child anchor authority visit) ih

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
