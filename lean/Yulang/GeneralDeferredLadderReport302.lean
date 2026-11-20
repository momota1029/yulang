import Yulang.GeneralObservedLadderRefreshProgram301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderReport302
open GeneralObservedLadderSemanticGap301 (equationOnly)
open GeneralObservedLadderReport301 (pos point)
open GeneralNominalOutputGrowthModels (descriptor)
open GeneralNominalExamples (interpretation intDisplay)
open GeneralDeclarationExamples (display)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalUnaryCaptureFacts (captured report_exact)

abbrev context := equationOnly
abbrev snapshot (n : Nat) := (context n).state

theorem nominal_at (n i : Nat) (hi : i ≤ n) :
    (snapshot n).nominals (pos n i (by omega)) = some (descriptor n (pos n i (by omega)) hi) :=
  dite_eq_left hi

theorem display_query (n : Nat) : GeneralNominalInspection.queries (snapshot n) interpretation display =
    [.nominal 0 [.variables [0]]] :=
  GeneralObservedLadderReport301.display_query n

theorem int_query (n : Nat) : GeneralNominalInspection.queries (snapshot n) interpretation intDisplay = [.scalar .int] :=
  GeneralObservedLadderReport301.int_query n

theorem display_report (n i : Nat) (hi : i ≤ n) :
    report (context n) display [point n i (by omega)] =
      captured (snapshot n) (pos n i (by omega)) 0 0 (point n (i+1) (by omega)) :=
  report_exact (context n) display (pos n i (by omega)) _ (nominal_at n i hi) 0
    (point n (i+1) (by omega)) rfl (display_query n)

theorem list_as_int (n i : Nat) (hi : i ≤ n) :
    report (context n) intDisplay [point n i (by omega)] =
      { inspected := [point n i (by omega)], checked := [point n i (by omega),point n i (by omega)],
        conflicts := [point n i (by omega)] } := by
  unfold report
  rw [show GeneralNominalInspection.queries (context n).state (context n).interpretation intDisplay = _ from int_query n]
  simp [inspectMany,inspect,Report.visit,Report.append,nominal_at n i hi]

theorem list_finished (n i : Nat) (hi : i ≤ n) :
    Finished (report (context n) display [point n i (by omega)]) := by
  rw [display_report n i hi]
  exact ⟨rfl,rfl,rfl⟩

theorem int_not_finished (n i : Nat) (hi : i ≤ n) :
    ¬ Finished (report (context n) intDisplay [point n i (by omega)]) := by
  rw [list_as_int n i hi]
  intro bad
  cases bad.2.1

end Yulang.GeneralDeferredLadderReport302
