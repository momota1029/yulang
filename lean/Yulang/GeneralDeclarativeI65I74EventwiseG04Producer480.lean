import Yulang.GeneralDeclarativeI65I74G04Producer479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

/-- The event-wise existence needed by A. The event already has an
independent typed path and the prior phase has the specified lineage. -/
def EventwiseG04Producer : Prop :=
  ∀ (n : Nat) (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (positions : Positions n) (relations : List (Fin n × Fin n))
    (basis : PriorPhase) (event : TypedInput p gd positions relations),
    basis.ExactFor event → ∃ wire, IssueIsFaithful basis event wire

theorem g04_producer_iff_eventwise_exists480 :
    G04Producer ↔ EventwiseG04Producer := by
  constructor
  · rintro ⟨emit,finished⟩ n p gd positions relations basis event valid
    obtain ⟨wire,_,ok⟩ := finished n p gd positions relations basis event valid
    exact ⟨wire,ok⟩
  · intro pointwise
    classical
    let emit : InputPhaseEmission := fun n p gd positions relations basis event =>
      if valid : basis.ExactFor event then
        some (Classical.choose (pointwise n p gd positions relations basis event valid))
      else none
    refine ⟨emit,?_⟩
    intro n p gd positions relations basis event valid
    let w := Classical.choose (pointwise n p gd positions relations basis event valid)
    refine ⟨w,?_,Classical.choose_spec (pointwise n p gd positions relations basis event valid)⟩
    simp [emit,valid,w]

end Yulang.GeneralDeclarativeI65.I72.Producer479
