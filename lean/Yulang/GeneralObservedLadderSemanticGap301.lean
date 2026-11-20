import Yulang.GeneralObservedLadderBudget301
import Yulang.GeneralNominalPeelingSources

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderSemanticGap301
open GeneralObservedLadderSource301 (snapshot endpoint models_exact)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderReport301 (point int_report display_query int_query)
open GeneralObservedLadderJournalCompiler301 (probe)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalExamples (intDisplay)
open GeneralDeclarationExamples (display)
open GeneralNominalCommonBridge (Assignment)

abbrev equationOnly (n : Nat) := GeneralNominalPeelingSources.context n

theorem same_models (n : Nat) (m : Assignment) :
    GeneralNominalState.Models (equationOnly n).state m ↔ GeneralNominalState.Models (snapshot n) m :=
  (GeneralNominalPeelingSources.source_models n m).trans (models_exact n m).symm

abbrev terminalPoint (n : Nat) : GeneralNominalInspection.Bounds (equationOnly n).state :=
  (endpoint n,endpoint n)

theorem unresolved (n : Nat) :
    (equationOnly n).state.nominals (endpoint n) = none ∧
      (equationOnly n).state.view.heads (endpoint n) = .deferred .unresolved := by
  refine ⟨?_,rfl⟩
  exact dite_eq_right (by change ¬ n+1 ≤ n; omega)

theorem old_int_report (n : Nat) :
    report (equationOnly n) intDisplay [terminalPoint n] =
      { inspected := [terminalPoint n], checked := [terminalPoint n,terminalPoint n],
        blocked := [terminalPoint n] } := by
  unfold report
  rw [show GeneralNominalInspection.queries (equationOnly n).state (equationOnly n).interpretation intDisplay =
    [.scalar .int] from int_query n]
  simp [inspectMany, inspect, Report.visit, Report.append, block, terminalPoint, (unresolved n).1,(unresolved n).2]

theorem old_list_report (n : Nat) :
    report (equationOnly n) display [terminalPoint n] =
      { inspected := [terminalPoint n], checked := [terminalPoint n,terminalPoint n],
        blocked := [terminalPoint n] } := by
  unfold report
  rw [show GeneralNominalInspection.queries (equationOnly n).state (equationOnly n).interpretation display =
    [.nominal 0 [.variables [0]]] from display_query n]
  simp [inspectMany, inspect, Report.visit, Report.append, block, terminalPoint, (unresolved n).1,(unresolved n).2]

theorem no_observation (n : Nat) : probe (equationOnly n) [terminalPoint n] = none := by
  unfold probe
  rw [old_int_report,old_list_report]
  rfl

theorem observed (n : Nat) : probe (context n) [point n (n+1) (Nat.le_refl _)] = some ⟨3,[]⟩ := by
  unfold probe
  rw [int_report,GeneralObservedLadderReport301.int_as_list]
  rfl

/-- Equality of all type/row assignment models is insufficient to transport
the actual inspector/compiler result. The old source here is a documented
equation-only reference source, not claimed as another V8 execution. -/
theorem strict_gap (n : Nat) :
    (∀ m, GeneralNominalState.Models (equationOnly n).state m ↔ GeneralNominalState.Models (snapshot n) m) ∧
      probe (equationOnly n) [terminalPoint n] ≠ probe (context n) [point n (n+1) (Nat.le_refl _)] := by
  refine ⟨same_models n,?_⟩
  rw [no_observation,observed]
  intro impossible
  cases impossible

end Yulang.GeneralObservedLadderSemanticGap301
