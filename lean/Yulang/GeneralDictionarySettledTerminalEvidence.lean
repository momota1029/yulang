import Yulang.GeneralDictionarySettledTerminalPrefix
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Current-context dictionary for the genuinely novel terminal Container child.
The actual I26 two-step prefix is proved separately, so the all-model dictionary
is not just an install-function assertion. Parent settlement and observation of
the new output are not claimed: the output is still unlocated here. -/
namespace Yulang.GeneralDictionarySettledTerminalEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalDownstreamSiblingFixture
open GeneralNominalBudgetContainer
open GeneralDictionaryRecursiveEvidence
open GeneralDeclarationExamples (roles)

/-- Every model after the actual terminal install supports its current source
instance, including its nonempty named output obligation. -/
theorem current_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models afterC.current model) :
    Instance reg afterC.current.context model kidC c.id [] := by
  have result := GeneralDictionaryOrdinaryTrace.installed_trace_current_instance
    reg root afterP.current afterC.current containerPacket enabled .refl model valid
  change Instance reg afterC.current.context model kidC c.id containerPacket.children at result
  simpa only [children] using result

theorem current_evidence (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models afterC.current model) :
    Evidence reg afterC.current.context model kidC (.node c.id []) :=
  evidence_node reg afterC.current.context model kidC c.id [] [] (current_instance model valid) .nil

/-- The named output is genuinely required, not an empty-schema leaf shortcut. -/
theorem nonempty_output : kidC.demand.outputs ≠ [] := by
  rw [shared_output.1]
  simp

/-- The all-model claim is inhabited at the actual reached state. -/
theorem inhabited_evidence : ∃ model, Models afterC.current model ∧
    Evidence reg afterC.current.context model kidC (.node c.id []) := by
  obtain ⟨model,valid⟩ := GeneralDictionarySettledTerminalPrefix.inhabited
  exact ⟨model,valid,current_evidence model valid⟩

/-- Evidence for this named output does not imply a current observation slot:
settlement/semantic evidence and inspection readiness are different judgments. -/
theorem evidence_without_output_readiness :
    (∃ model, Models afterC.current model ∧
      Evidence reg afterC.current.context model kidC (.node c.id [])) ∧
    ¬ GeneralNominalSettledSupport.ReadyAt afterC out :=
  ⟨inhabited_evidence,GeneralDictionarySettledTerminalPrefix.output_not_ready⟩

/-- Concrete actual execution plus nonvacuous final all-model dictionary.
No Stable or parent-selection premise is hidden in this result. -/
theorem actual_terminal_dictionary :
    B4Target.Steps (GeneralNominalSettledSteps.Step reg root) start afterC ∧
    B4TargetV5.Reachable (GeneralNominalSettledBoundary.boundary roles) reg root afterC ∧
    kidC.demand.outputs ≠ [] ∧
    (∃ model, Models afterC.current model) ∧
    ∀ model, Models afterC.current model →
      Evidence reg afterC.current.context model kidC (.node c.id []) :=
  ⟨GeneralDictionarySettledTerminalPrefix.actual_prefix,
    GeneralDictionarySettledTerminalPrefix.reachable,nonempty_output,
    GeneralDictionarySettledTerminalPrefix.inhabited,current_evidence⟩

/-- Ordinary-only feedback continuations retain the current dictionary. This is
explicitly restricted to unchanged inspection views, not arbitrary reobserve. -/
theorem ordinary_continuation_evidence (after : State roles)
    (path : B4Target.Steps (GeneralDictionaryOrdinaryTrace.OrdinaryStep reg root)
      afterC.current after)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    Evidence reg after.context model kidC (.node c.id []) := by
  apply GeneralDictionaryOrdinaryTrace.installed_trace_current_evidence
    reg root afterP.current after containerPacket enabled path model valid []
  rw [children]
  exact .nil
end Yulang.GeneralDictionarySettledTerminalEvidence
