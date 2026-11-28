import Yulang.GeneralDeclarativeI65I74InteriorCorrespondence483
import Yulang.GeneralDeclarativeI65I74GeometryCounterpart484
import Yulang.GeneralDeclarativeI65I74ProducerTrail479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Counterpart484
open ObservationAlternatives473 (Positions graphOf)
open Producer479 (Site Hop Trail TrailWire readTrail)
open LiteralVisits473 (StepWire GuardedObservationInput)
open CommonRoleRegularGraph (successors)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation)

private theorem guard_is_inherited_at_an_actual_child
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)} {i j : Fin n}
    (top : GuardedObservationInput s pos rel i) (edge : j ∈ successors (graphOf s pos) i) :
    GuardedObservationInput s pos rel j :=
  ⟨top.1,top.2.1,top.2.2.1,top.2.2.2.1,
    (fun k h => top.2.2.2.2.1 k (.cons edge h)),fun k h => top.2.2.2.2.2 k (.cons edge h)⟩

/-- A derivation on one physical presentation and an independently complete
same-class cone on the other suffice for geometry only. The original selected
actions are retained exactly, including each literal written pose and the sign. -/
theorem one_independently_selected_trail_reifies_its_equal_observation_geometry
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {left right finish : Site s pos} {moves : List StepWire} {sites : List (Fin n)} {bit : Bool}
    (selected : Trail s pos rel left moves sites finish bit)
    (guard : GuardedObservationInput s pos rel right.index)
    (same : ObservationallyEqual (graphOf s pos) left.index right.index)
    (samePattern : left.pattern = right.pattern) (sameCode : left.query = right.query) :
    ∃ (other : Site s pos) (otherSites : List (Fin n)),
      Trail s pos rel right moves otherSites other bit ∧ other.pattern = finish.pattern ∧
        other.query = finish.query ∧ ObservationallyEqual (graphOf s pos) finish.index other.index := by
  induction selected generalizing right with
  | stop _ existing =>
    exact ⟨right,[],.stop guard
      (existing.trans (quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation same)),
      samePattern.symm,sameCode.symm,same⟩
  | step one sourceGuard safe later ih =>
    have leftKnown := sourceGuard.2.2.2.2.2 _ (.nil _)
    have rightKnown := guard.2.2.2.2.2 _ (.nil _)
    obtain ⟨next,⟨two⟩,pattern,code⟩ :=
      equal_presentations_reify_one_already_selected_original_geometric_hop
        leftKnown rightKnown (fun i edge => guard.2.2.2.2.2 i (.cons edge (.nil _)))
        same samePattern sameCode one
    have both := InteriorCorrespondence483.paired_selected_children_have_equal_regular_observations
      guard.2.1 leftKnown rightKnown same one two rfl
    obtain ⟨other,there,path,terminalPattern,terminalCode,terminalObs⟩ :=
      ih (guard_is_inherited_at_an_actual_child guard two.edge) both pattern.symm code.symm
    exact ⟨other,next.index::there,.step two guard
      (fun cycle => safe ((quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation same).mpr cycle)) path,
      terminalPattern,terminalCode,terminalObs⟩

theorem one_trail_and_equal_complete_cone_reify_an_exact_finite_geometry_wire
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {left right finish : Site s pos} {moves : List StepWire} {sites : List (Fin n)} {bit : Bool}
    (selected : Trail s pos rel left moves sites finish bit)
    (guard : GuardedObservationInput s pos rel right.index)
    (same : ObservationallyEqual (graphOf s pos) left.index right.index)
    (samePattern : left.pattern = right.pattern) (sameCode : left.query = right.query) :
    ∃ (other : Site s pos) (wire : TrailWire n),
      wire.cursor.which = right.index ∧ wire.tail.map Prod.fst = moves ∧
      readTrail rel right wire = some (other,bit) ∧ other.pattern = finish.pattern ∧
        other.query = finish.query ∧ ObservationallyEqual (graphOf s pos) finish.index other.index := by
  obtain ⟨other,_,chosen,original,query,observed⟩ :=
    one_independently_selected_trail_reifies_its_equal_observation_geometry selected guard same samePattern sameCode
  obtain ⟨wire,root,steps,_,replayed⟩ := Producer479.finite_trail_wire_replays_exact_selected_path479 chosen
  exact ⟨other,wire,root,steps,replayed,original,query,observed⟩

end Yulang.GeneralDeclarativeI65.I72.Counterpart484
