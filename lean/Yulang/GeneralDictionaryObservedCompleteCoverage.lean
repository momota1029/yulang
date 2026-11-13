import Yulang.GeneralDictionaryObservedCompleteClassification
import Yulang.GeneralDictionaryObservedStableCoverage

/-! Instantiate the finite recursive coverage theorem on the actual stable
named-output parent journal and its unrecorded scalar child. -/
namespace Yulang.GeneralDictionaryObservedCompleteCoverage
open GeneralDictionaryObservedCompleteExample GeneralDictionaryObservedCompleteInstallation
open GeneralDictionaryObservedCompleteEvidence GeneralDictionaryObservedCompleteFinalEvidence
open GeneralDictionaryObservedCompleteClosure GeneralDictionaryObservedCompleteStable
open GeneralDictionaryObservedCompleteClassification
open GeneralNominalExamples (model intDisplay int_display_checked)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralNominalJointCandidates

noncomputable abbrev scalarShape : GeneralDictionaryScalarLeaf.ScalarLeafShape current child intDisplay where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := ⟨1,by change 1 < 2; decide⟩
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by change GeneralNominalInspection.queries source context.interpretation intDisplay = _; exact leafShape.query
  located := by change GeneralNominalRecursiveCandidates.arguments context child = _; exact child_arguments

theorem ordinary_trace : B4Target.Steps
    (GeneralDictionarySupportOrdinaryExecution.Step registry root) start installed :=
  .tail .refl ⟨root,.root,.install packet [] enabled novel guard⟩

theorem alias_equal {first last : Nat} (alias : Alias installed.current first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem related_child (site : GeneralNominalDemandMerging.Site roles)
    (related : Related installed.current child site) : site.occurrence = child := by
  have same := alias_equal related.2
  have member := related.1
  rw [sites_exact] at member
  rcases List.mem_cons.mp member with equal | rest
  · subst site
    have different : child.identity ≠ root.identity := by decide +kernel
    exact False.elim (different same)
  · have equal := List.mem_singleton.mp rest
    subst site
    rfl

theorem covered : GeneralDictionaryObservedStableCoverage.Covered registry installed root := by
  intro focus reached key kids selected
  rcases generated_cases focus reached with rfl | rfl
  · exact Or.inl ⟨packet,List.mem_singleton_self _,rfl⟩
  · refine Or.inr ⟨intDisplay,by simp,int_display_checked,Or.inr (Or.inr (Or.inr ⟨scalarShape⟩)),?_⟩
    intro site related
    rw [related_child site related]
    exact ⟨Or.inr (Or.inr (Or.inr ⟨scalarShape⟩)),intDisplay.id,[],supported_child⟩

/-- No coverage/trace/stability input remains assumed for this fixed example.
The named-output parent uses actual historical membership, the child structural coverage. -/
theorem every_model_from_coverage (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root payload :=
  GeneralDictionaryObservedStableCoverage.dictionary_evidence registry root context initial_source
    installed ordinary_trace stable covered assignment valid payload root .root classified

theorem actual_stable_named_coverage :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    GeneralNominalSupportSteps.Stable registry installed root ∧
    Models installed.current model ∧ GeneralDictionaryObservedStableCoverage.Covered registry installed root ∧
    root.demand.outputs ≠ [] ∧ children.length = 1 ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry current model root payload :=
  ⟨installed_reachable,stable,models_of_source model source_models,covered,named_request_present,
    actual_children_count,every_model_from_coverage model (models_of_source model source_models)⟩
end Yulang.GeneralDictionaryObservedCompleteCoverage
