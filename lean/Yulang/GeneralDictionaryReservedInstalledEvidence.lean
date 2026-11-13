import Yulang.GeneralDictionaryFiniteObservedExampleReservedRecorded
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Current-context evidence after the reserved-output installation. The general
installed-trace theorem is applied to the actual guarded step, not to an assumed
final dictionary. Stability is deliberately not a premise or a conclusion. -/
namespace Yulang.GeneralDictionaryReservedInstalledEvidence
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration)
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence
open GeneralDeclarationExamples (roles)

theorem current_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Instance registry installed.current.context assignment root declaration.id [] := by
  have result := GeneralDictionaryOrdinaryTrace.installed_trace_current_instance
    registry root start.current installed.current packet enabled .refl assignment valid
  change Instance registry installed.current.context assignment root declaration.id packet.children at result
  simpa only [packet_children] using result

theorem current_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Evidence registry installed.current.context assignment root (.node declaration.id []) :=
  evidence_node registry installed.current.context assignment root declaration.id [] []
    (current_instance assignment valid) .nil

/-- Every ordinary continuation retains the installed current-context dictionary.
The continuation is explicitly restricted to existing no-view-change steps. -/
theorem ordinary_continuation_evidence (after : State roles)
    (path : B4Target.Steps (GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root)
      installed.current after)
    (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models after assignment) :
    Evidence registry after.context assignment root (.node declaration.id []) := by
  apply GeneralDictionaryOrdinaryTrace.installed_trace_current_evidence
    registry root start.current after packet enabled path assignment valid []
  rw [packet_children]
  exact .nil

theorem actual_reserved_dictionary :
    GeneralNominalValueSteps.Step registry root start installed ∧
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root installed ∧
    Models installed.current positive ∧
    (¬ ∃ slot : Fin state.base.slots, state.base.source slot = 2) ∧
    ∀ assignment, Models installed.current assignment →
      Evidence registry installed.current.context assignment root (.node declaration.id []) :=
  ⟨value_install_step,value_reachable,installed_models,no_target_slot,current_evidence⟩
end Yulang.GeneralDictionaryReservedInstalledEvidence
