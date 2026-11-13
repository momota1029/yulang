import Yulang.GeneralDictionarySharedTerminalInstallation
import Yulang.GeneralDictionaryExactRefreshChain

/-! The two emitters coincide only for terminal packets, whose child-site lists
are empty. This limited equality transfers the concrete output obstruction to
an actual guarded Shared step; it is not a subrelation claim for nonterminals. -/
namespace Yulang.GeneralDictionarySharedTerminalObstruction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport

theorem terminal_install_eq (state : Tracked roles) (packet : Packet roles)
    (support : List (Occurrence roles)) (terminal : packet.children = []) :
    GeneralNominalSharedSteps.install state packet support =
      GeneralNominalSettledSteps.install state packet support := by
  simp only [GeneralNominalSharedSteps.install,GeneralNominalSettledSteps.install,
    GeneralNominalValueSteps.install,GeneralNominalSupportSteps.install,
    GeneralNominalFeedbackSites.install,GeneralNominalSharedEmission.emitted,
    GeneralNominalFeedbackSites.emitted,terminal,List.map_nil]

theorem concrete_after_eq : GeneralDictionarySharedTerminalInstallation.after = GeneralNominalBudgetContainer.afterC :=
  terminal_install_eq _ _ _ GeneralNominalBudgetContainer.children

theorem shared_unknown_after_exact_chain (after : State GeneralDeclarationExamples.roles)
    (path : B4Target.Steps GeneralDictionaryExactRefreshChain.ExactRefresh
      GeneralDictionarySharedTerminalInstallation.after.current after) :
    ¬ GeneralNominalState.Known after.context.state GeneralNominalSupportSiblings.out := by
  rw [concrete_after_eq] at path
  exact GeneralDictionaryExactRefreshChain.terminal_unknown after path

/-- Actual Shared terminal dictionary, with no semantic head inferred from its
named output or settlement, even after arbitrary exact-refresh chains. -/
theorem dictionary_and_obstruction :
    (∃ model, Models GeneralDictionarySharedTerminalInstallation.after.current model ∧
      GeneralDictionaryRecursiveEvidence.Evidence GeneralNominalSupportSiblings.reg
        GeneralDictionarySharedTerminalInstallation.after.current.context model
        GeneralNominalSupportSiblings.kidC (.node GeneralNominalSupportSiblings.c.id [])) ∧
    ∀ after, B4Target.Steps GeneralDictionaryExactRefreshChain.ExactRefresh
      GeneralDictionarySharedTerminalInstallation.after.current after →
      ¬ GeneralNominalState.Known after.context.state GeneralNominalSupportSiblings.out := by
  constructor
  · obtain ⟨model,valid⟩ := GeneralDictionarySharedTerminalInstallation.inhabited
    exact ⟨model,valid,GeneralDictionarySharedTerminalInstallation.current_dictionary model valid⟩
  · exact shared_unknown_after_exact_chain
end Yulang.GeneralDictionarySharedTerminalObstruction
