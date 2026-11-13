import Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation
import Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence

/-! Full named-output dictionary after an actual guarded installation, in every
final model. No final stability premise is smuggled into the reachability claim. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence
open GeneralDictionaryFiniteObservedExampleNonterminal GeneralDictionaryFiniteObservedExampleNonterminalInstallation
open GeneralDictionaryFiniteObservedExampleNonterminalEvidence
open GeneralDictionaryFiniteObservedExample (model)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence

theorem models_of_source (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source assignment) : Models installed.current assignment := by
  apply (GeneralNominalFeedbackSites.install_models start.current packet _ rfl assignment).mpr
  exact ⟨(GeneralNominalSaturationState.initial_models context root assignment).mpr valid,
    every_source_model assignment valid⟩

theorem source_of_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) : GeneralNominalState.Models source assignment :=
  ((GeneralNominalFeedbackSites.install_models start.current packet _ rfl assignment).mp valid).1.1

theorem installed_models_iff (assignment : GeneralNominalCommonBridge.Assignment) :
    Models installed.current assignment ↔ GeneralNominalState.Models source assignment :=
  ⟨source_of_models assignment,models_of_source assignment⟩

theorem final_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Evidence registry installed.current.context assignment root payload :=
  GeneralDictionaryOrdinaryTrace.evidence_extension registry context installed.current.context
    (GeneralDictionaryOrdinaryTrace.packet_extension packet) assignment valid.1 root payload
    (full_evidence assignment (source_of_models assignment valid))

theorem nonempty_journal : installed.current.packets ≠ [] := by
  change packet :: start.current.packets ≠ []
  simp

/-- A real initial-source transition, inhabited journal, exact one-child tree,
nonempty associated-output request, and semantic dictionary coexist. -/
theorem reachable_full_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ Evidence registry installed.current.context model root payload ∧
    installed.current.packets ≠ [] ∧ root.demand.outputs ≠ [] ∧ children.length = 1 :=
  ⟨installed_reachable,models_of_source model source_models,
    final_evidence model (models_of_source model source_models),nonempty_journal,named_request_present,actual_children_count⟩
end Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence
