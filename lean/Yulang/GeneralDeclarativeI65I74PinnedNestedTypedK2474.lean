import Yulang.GeneralDeclarativeI65I74TypedConeQuotientSound474
import Yulang.GeneralDeclarativeI65I74PinnedNestedTerminal474

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.LiteralVisits473
open RetainedFull445 (FullProblem)
open GeneralDeclarativeI65 (Model)
open ObservationAlternatives473 (oldPosition interpretedAt actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit
  actual_safe_quotient_never_returns_to_its_own_observation_class)
open QuotientObservation471 (embedded cone classOf)
open CommonRoleRegularGraph (successors)
open CommonNominalFullCarrier (Equivalent)
open FiniteWorklist (Path)

theorem actual_nested_k2_has_its_own_checked_walk_returning_to_an_equal_type_in_every_fit
    {p : FullProblem} {table gd input pos rel outer wire result}
    (ran : @readNestedAuthoredField n p table gd input pos rel outer wire = some result)
    (k2 : result.bit = true) :
    let final := reportedCheckpoint wire
    result.physicalSite = oldPosition pos (embedded final.scope final.scope.site) ∧
    ∃ first last : Fin final.m,
      first ∈ successors (cone final.scope) final.scope.site ∧
      Path (successors (cone final.scope)) first last ∧
      classOf final.partition last = classOf final.partition final.scope.site ∧
      (∀ m : Model, FitsFull p.state m →
        Equivalent (interpretedAt p.old.state.core pos m.assignment (embedded final.scope last))
          (interpretedAt p.old.state.core pos m.assignment (embedded final.scope final.scope.site))) := by
  dsimp only
  obtain ⟨site,computation⟩ := existing_full_nested_result_pins_its_exact_terminal_partition_and_physical_address ran
  rw [k2] at computation
  have approved := actual_quotient_k2_gives_a_nonempty_constructor_walk_and_same_type_in_every_fit (p := p) computation
  have here : embedded (reportedCheckpoint wire).scope (reportedCheckpoint wire).scope.site =
      (reportedCheckpoint wire).which := by
    have view : QuotientObservation471.replayCone (ObservationAlternatives473.graphOf p.old.state.core pos)
        (reportedCheckpoint wire).which (reportedCheckpoint wire).scope
        (reportedCheckpoint wire).partition = some true := by
      unfold ObservationAlternatives473.readAlternatives at computation
      split at computation
      · exact computation
      · cases computation
    exact (QuotientObservation471.cone_replay_sound view).1.1
  exact ⟨site.trans (congrArg (oldPosition pos) here.symm),approved⟩

theorem actual_nested_safe_report_excludes_return_in_its_own_checked_class
    {p : FullProblem} {table gd input pos rel outer wire result}
    (ran : @readNestedAuthoredField n p table gd input pos rel outer wire = some result)
    (safe : result.bit = false) :
    let final := reportedCheckpoint wire
    ∀ first ∈ successors (cone final.scope) final.scope.site, ∀ last,
      Path (successors (cone final.scope)) first last →
      classOf final.partition last ≠ classOf final.partition final.scope.site := by
  dsimp only
  have computation := (existing_full_nested_result_pins_its_exact_terminal_partition_and_physical_address ran).2
  rw [safe] at computation
  exact actual_safe_quotient_never_returns_to_its_own_observation_class (p := p) computation

end Yulang.GeneralDeclarativeI65.I72.LiteralVisits473

