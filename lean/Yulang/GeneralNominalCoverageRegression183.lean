import Yulang.GeneralNominalCompleteNames183

/-! A terminal declaration exercises input capture without a child from which
covered-head hypotheses could be obtained. Registry acceptance is not claimed. -/
namespace Yulang.GeneralNominalCoverageRegression183
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalRecursiveInspection GeneralNominalInspectionAlignment

def terminal : Declaration := ⟨183,0,[.var 37],[],[],[]⟩

theorem terminal_has_input : 37 ∈ terminal.inputNames := by decide

theorem terminal_has_no_children : terminal.requirements = [] := rfl

theorem terminal_finished (state : GeneralNominalState.State) (interpretation : Interpretation)
    (bounds : Bounds state) (origins : Nat → Option Origin) :
    Finished (inspectMany state (queries state interpretation terminal) [bounds] origins 0) := by
  simp only [queries,terminal,Declaration.normalHead,normalizeArgs,normalize,translate,
    List.map_cons,List.map_nil,GeneralNominalRecursiveInspection.inspectMany,
    GeneralNominalRecursiveInspection.inspect,GeneralNominalRecursiveInspection.Finished,
    GeneralNominalRecursiveInspection.Report.append,List.append_nil]
  trivial

theorem terminal_input_captured (state : GeneralNominalState.State) (interpretation : Interpretation)
    (bounds : Bounds state) (origins : Nat → Option Origin) :
    ∃ captured ∈ (inspectMany state (queries state interpretation terminal) [bounds] origins 0).captures,
      captured.name = 37 :=
  GeneralNominalCompleteNames183.declaration_input_capture state interpretation terminal [bounds] origins 0
    (terminal_finished state interpretation bounds origins) 37 terminal_has_input

end Yulang.GeneralNominalCoverageRegression183
