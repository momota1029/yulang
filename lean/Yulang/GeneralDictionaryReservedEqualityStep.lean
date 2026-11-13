import Yulang.GeneralDictionaryReservedOutputEquality

/-! A genuine next equality-feedback step after installing a reserved output.
A dictionary may already exist while the raw context still needs saturation. -/
namespace Yulang.GeneralDictionaryReservedEqualityStep
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration model arguments)
open GeneralDictionaryReservedOutputEquality GeneralDictionaryReservedInstalledEvidence
open GeneralNominalSaturationState GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

theorem raw_countermodel : GeneralNominalState.Models installed.current.context.state model := by
  change GeneralNominalState.Models (privateState registry context root declaration [(1,1)]) model
  unfold privateState
  rw [report_exact]
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨source_models,?_,?_⟩,?_⟩
  · simp [bindings,GeneralNominalAllocation.Compatible]
  · simp [bindings,GeneralNominalAllocation.merges,GeneralDeclarations.Declaration.inputNames,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]
  · simp [selfChecks,PresenceNormalForm.All]
    exact subtype_refl _

theorem not_raw_equal : ¬ GeneralNominalFeedbackSteps.RawEqual installed.current 2 0 := by
  intro all
  have equal := all model raw_countermodel
  have below : Subtype (.base .int) (nominal 0 arguments) := equal.1
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) ⟨rfl,by simp⟩

noncomputable abbrev after :=
  { installed with current := GeneralNominalFeedbackSteps.equate installed.current 2 0 }

theorem equality_step : GeneralNominalValueSteps.Step registry root installed after := by
  refine ⟨root,.root,.administrative root _ (.equate root 2 0 ?_ ?_ journal_equal not_raw_equal)⟩
  · exact GeneralNominalRefinements.sources
      (GeneralNominalRefinements.installed registry context root declaration [(1,1)]) 2 reserved_source
  · exact GeneralNominalRefinements.sources
      (GeneralNominalRefinements.installed registry context root declaration [(1,1)]) 0
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩))))

theorem installed_not_stable : ¬ GeneralNominalValueSteps.Stable registry installed root := by
  intro stable
  exact stable equality_step.choose equality_step.choose_spec.1 after equality_step.choose_spec.2

theorem models_iff (assignment : GeneralNominalCommonBridge.Assignment) :
    Models after.current assignment ↔ Models installed.current assignment :=
  GeneralNominalFeedbackSteps.equate_models installed.current 2 0 journal_equal assignment

theorem reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root after := by
  obtain ⟨first,initial,path⟩ := value_reachable
  exact ⟨first,initial,.tail path equality_step⟩

theorem final_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context assignment root (.node declaration.id []) :=
  GeneralDictionaryOrdinaryTrace.evidence_extension registry installed.current.context after.current.context
    (GeneralDictionaryOrdinaryTrace.equate_extension installed.current 2 0) assignment valid.1 root _
    (current_evidence assignment ((models_iff assignment).mp valid))

theorem reachable_dictionary_after_feedback :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root after ∧
    Models after.current positive ∧
    (∀ assignment, Models after.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context assignment root (.node declaration.id [])) :=
  ⟨reachable,(models_iff positive).mpr installed_models,final_evidence⟩
end Yulang.GeneralDictionaryReservedEqualityStep
