import Yulang.GeneralDeclarativeI65I74ChildOrdinal483
import Yulang.GeneralDeclarativeI65I74OrdinalPath483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InteriorCorrespondence483
open ObservationAlternatives473 (Positions oldPosition graphOf)
open Producer479 (Site Hop)
open LiteralVisits473 (StepWire childSlot)
open CommonRoleRegularGraph (successors)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality)

theorem paired_selected_children_have_equal_regular_observations
    {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {left right a b : Site s pos} {action other : StepWire}
    (loc : (List.ofFn (oldPosition pos)).Nodup)
    (leftKnown : graphOf s pos left.index ≠ .unresolved)
    (rightKnown : graphOf s pos right.index ≠ .unresolved)
    (same : ObservationallyEqual (graphOf s pos) left.index right.index)
    (one : Hop left a action) (two : Hop right b other)
    (selected : childSlot action.action = childSlot other.action) :
    ObservationallyEqual (graphOf s pos) a.index b.index := by
  obtain ⟨ix,atLeft,atRight⟩ :=
    ChildOrdinal483.paired_actual_constructors_pull_the_exact_selected_slot_to_the_same_ordinal
      loc leftKnown rightKnown same one two selected
  obtain ⟨b',atOther,otherSame⟩ :=
    QuotientObservation471.OrdinalPath483.corresponding_ordinal_child_exists_and_preserves_observations
      same ix atLeft
  have eq : b' = b.index := Option.some.inj (atOther.symm.trans atRight)
  rw [←eq]
  exact otherSame

/-- Each side provides its literal hop separately. Equality identifies matching
observations at the selected child, not either side's authority or written pose. -/
inductive PairedTrail {s : GeneralDeclarativeI65.State} {pos : Positions n} :
    Site s pos → Site s pos → List (Site s pos × Site s pos) → Prop where
  | nil : PairedTrail left right []
  | cons : graphOf s pos left.index ≠ .unresolved →
      graphOf s pos right.index ≠ .unresolved →
      Hop left a action → Hop right b other →
      childSlot action.action = childSlot other.action →
      PairedTrail a b rest → PairedTrail left right ((a,b)::rest)

theorem every_paired_actual_position_keeps_its_own_return_status
    {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {left right : Site s pos} {later}
    (loc : (List.ofFn (oldPosition pos)).Nodup)
    (same : ObservationallyEqual (graphOf s pos) left.index right.index)
    (trail : PairedTrail left right later) :
    ∀ pair ∈ (left,right)::later,
      ObservationallyEqual (graphOf s pos) pair.1.index pair.2.index ∧
      (ReturnsUpToEquality (graphOf s pos) pair.1.index ↔
        ReturnsUpToEquality (graphOf s pos) pair.2.index) := by
  induction trail with
  | nil =>
    intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    exact ⟨same,QuotientObservation471.quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation same⟩
  | cons l r one two select _ ih =>
    intro pair member
    rcases List.mem_cons.mp member with h | h
    · subst pair
      exact ⟨same,QuotientObservation471.quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation same⟩
    · exact ih (paired_selected_children_have_equal_regular_observations loc l r same one two select) pair h

end Yulang.GeneralDeclarativeI65.I72.InteriorCorrespondence483
