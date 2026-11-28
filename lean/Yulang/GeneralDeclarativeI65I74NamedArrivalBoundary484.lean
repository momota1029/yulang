import Yulang.GeneralDeclarativeI65I74TypedFocusHop482
import Yulang.GeneralDeclarativeI65I74ChildOrdinal483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions oldPosition anchorFor)
open Producer479 (Site Hop readHop)
open LiteralVisits473 (StepWire ReadStep readLiteralVisitStep)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open InputCoordinates475 (rawAt)

theorem pending_named_geometry_does_not_construct_a_focused_old_child
    {n : Nat} {p : FullProblem} {pos : Positions n} {t : Table}
    {here next : Site p.old.state.core pos} {move : StepWire} {ticket : ReadCard} {i : Fin n}
    {step : ReadStep p.old.state.core move here.pattern here.query here.term}
    {v : Nat} {pending : Equation}
    (literal : readLiteralVisitStep p.old.state.core here.pattern here.query here.term move = some step)
    (named : step.actualRawChild = .variable v)
    (geometric : readHop here move i = some next)
    (stored : (rawAt p).equations[(pos.cells.get next.index).oldOrdinal]? = some pending)
    (notSource : pending ∉ t.authored) :
    readFocusedCardHop (p := p) t here move ticket i = none := by
  cases ran : readFocusedCardHop (p := p) t here move ticket i with
  | none => rfl
  | some checked =>
    have atSite := Option.some.inj (checked.siteRead.symm.trans geometric)
    have atStep := Option.some.inj (checked.stepRead.symm.trans literal)
    have checkedNamed := checked_arrival_is_exact_original_source_row_or_literal_term checked.sameRow
    rcases checkedNamed with noName|⟨other,idx,row,rawName,__,located,rawFound,authFound,_,_⟩
    · exact False.elim (noName.2.1 v (atStep.symm ▸ named))
    · have oldPos : idx.raw = (pos.cells.get next.index).oldOrdinal := by simpa [atSite] using located
      have sameRow : row = pending := by
        rw [oldPos,stored] at rawFound
        exact (Option.some.inj rawFound).symm
      subst row
      exact False.elim (notSource (List.mem_of_getElem? authFound))

theorem two_unique_old_sites_for_a_named_arrival_cannot_have_different_raw_ordinals
    {n : Nat} {pos : Positions n}
    {a b : Fin n} {v : Nat}
    (nonrepeat : (List.ofFn (oldPosition pos)).Nodup)
    (landA : oldPosition pos a = .logical v) (landB : oldPosition pos b = .logical v) :
    (pos.cells.get a).oldOrdinal = (pos.cells.get b).oldOrdinal :=
  congrArg (fun (j : Fin n) => (pos.cells.get j).oldOrdinal)
    (ChildOrdinal483.unique_observation_coordinates_are_injective nonrepeat (landA.trans landB.symm))


theorem actual_hops_sharing_the_same_logical_child_cannot_reanchor_to_another_old_row
    {s : GeneralDeclarativeI65.State} {n : Nat} {pos : Positions n}
    {here there a b : Site s pos} {one two : StepWire} {v : Nat}
    (nonrepeat : (List.ofFn (oldPosition pos)).Nodup)
    (rawA : Hop here a one) (rawB : Hop there b two)
    (namedA : rawA.typed.actualRawChild = .variable v)
    (namedB : rawB.typed.actualRawChild = .variable v) :
    (pos.cells.get a.index).oldOrdinal = (pos.cells.get b.index).oldOrdinal := by
  apply two_unique_old_sites_for_a_named_arrival_cannot_have_different_raw_ordinals nonrepeat
  · rw [←rawA.position,namedA,anchorFor]
  · rw [←rawB.position,namedB,anchorFor]

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
