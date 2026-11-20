import Yulang.GeneralObservedLadderInitial301
import Yulang.GeneralNominalUnaryCaptureFacts

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderReport301
open GeneralObservedLadderSource301
open GeneralObservedLadderInitial301 (context)
open GeneralDeclarationExamples (display)
open GeneralNominalExamples (intDisplay interpretation)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalUnaryCaptureFacts (captured report_exact)
open GeneralNominalInspection (queries)

abbrev pos (n i : Nat) (hi : i ≤ n+1) : Fin (n+2) := ⟨i,by omega⟩

abbrev point (n i : Nat) (hi : i ≤ n+1) : GeneralNominalInspection.Bounds (snapshot n) :=
  (pos n i hi,pos n i hi)

theorem no_nominal (n : Nat) : (snapshot n).nominals (endpoint n) = none :=
  dite_eq_right (by change ¬ n+1 ≤ n; omega)

theorem display_query (n : Nat) : queries (snapshot n) interpretation display =
    [.nominal 0 [.variables [0]]] := by
  simp [queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation,snapshot]

theorem int_query (n : Nat) : queries (snapshot n) interpretation intDisplay = [.scalar .int] := by
  simp [queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]

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
  rw [show queries (context n).state (context n).interpretation intDisplay = _ from int_query n]
  simp [inspectMany,inspect,Report.visit,Report.append,nominal_at n i hi]

theorem int_as_list (n : Nat) :
    report (context n) display [point n (n+1) (Nat.le_refl _)] =
      { inspected := [point n (n+1) (Nat.le_refl _)],
        checked := [point n (n+1) (Nat.le_refl _),point n (n+1) (Nat.le_refl _)],
        conflicts := [point n (n+1) (Nat.le_refl _)] } := by
  unfold report
  rw [show queries (context n).state (context n).interpretation display = _ from display_query n]
  simp [inspectMany,inspect,Report.visit,Report.append,show pos n (n+1) (Nat.le_refl _) = endpoint n from rfl,
    no_nominal,scalar_at]

theorem int_report (n : Nat) :
    report (context n) intDisplay [point n (n+1) (Nat.le_refl _)] =
      { inspected := [point n (n+1) (Nat.le_refl _)],
        checked := [point n (n+1) (Nat.le_refl _),point n (n+1) (Nat.le_refl _)] } := by
  unfold report
  rw [show queries (context n).state (context n).interpretation intDisplay = _ from int_query n]
  simp [inspectMany,inspect,Report.visit,Report.append,show pos n (n+1) (Nat.le_refl _) = endpoint n from rfl,
    no_nominal,scalar_at]

theorem exact_at (n i : Nat) (hi : i ≤ n+1) :
    (Finished (report (context n) display [point n i hi]) ↔ i ≤ n) ∧
    (Finished (report (context n) intDisplay [point n i hi]) ↔ i = n+1) := by
  by_cases inner : i ≤ n
  · rw [display_report n i inner,list_as_int n i inner]
    have diff : i ≠ n+1 := by omega
    simp [Finished,captured,inner,diff]
  · have last : i = n+1 := by omega
    subst i
    rw [int_as_list,int_report]
    simp [Finished]

end Yulang.GeneralObservedLadderReport301
