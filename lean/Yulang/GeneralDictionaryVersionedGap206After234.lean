import Yulang.GeneralDictionaryVersionedGap206Selected234
import Yulang.GeneralNominalVersionedEquate234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206After234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Install233
open GeneralDictionaryVersionedGap206Feedback234
open GeneralNominalVersionedJournal232 GeneralNominalCenters
open GeneralNominalVersionedTransport231

abbrev equations := GeneralNominalAllocation.equations 0 (.var 1)
noncomputable def currentPlan := extendedPlan [] equations [] (GeneralNominalVersionedInstallation231.replayPlan plan)

theorem models_iff (assignment) : Models feedback assignment ↔ Models installed assignment :=
  GeneralNominalVersionedEquate234.models_iff installed_equal assignment

theorem model_retained : Models feedback model := (models_iff model).mpr installed_model

theorem counter_removed : ¬ Models feedback counter := fun valid => bottom_removed ((models_iff counter).mp valid)

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root feedback :=
  ⟨current,initial,.tail (.tail .refl GeneralDictionaryVersionedGap206Install233.step) feedback_step⟩

theorem holds (assignment) (valid : Models feedback assignment) : GeneralNominalVersionedPlans231.Holds currentPlan assignment := by
  apply (holds_iff [] equations [] _ _).mpr
  have old := (models_iff assignment).mp valid
  exact ⟨GeneralNominalVersionedInstalledEvidence233.replay_holds old,
    (GeneralNominalCaptureMerges.equations_exact assignment 0 (.var 1)).mpr (installed_equal assignment old)⟩

theorem core_eq : feedback.core = GeneralNominalCenteredSteps.refresh installed.core
    (GeneralDictionaryOrdinaryTransport.extend installed.core.erased.current.context [] equations []) := by
  simp only [feedback,GeneralNominalVersionedAdministrative232.equate,
    GeneralNominalVersionedAdministrative232.change,GeneralNominalCenteredHeadMatStepJournal.change,
    GeneralNominalFeedbackSteps.equate,GeneralNominalCenteredSteps.refresh,
    GeneralDictionaryOrdinaryTransport.extend,GeneralDictionaryOrdinaryTransport.extendState,
    GeneralNominalState.extend,GeneralNominalVersionedJournal232.State.core,List.append_nil]
  rfl

 theorem frame : GeneralNominalVersionedEvidence231.Frame registry feedback.core root 37 currentPlan := by
  rw [core_eq]
  apply GeneralNominalVersionedPreparedTransport231.frame_extended [] equations [] registry installed.core root 37
    (GeneralNominalVersionedInstallation231.replayPlan plan) GeneralDictionaryVersionedGap206Selected234.frame _ model
    (holds model model_retained)
  rw [show (GeneralNominalVersionedInstallation231.replayPlan plan).packet =
    extendedPacket (GeneralNominalVersionedInstallation231.reserved packet)
      (GeneralNominalVersionedInstallation231.atoms packet) (GeneralNominalVersionedInstallation231.allocated packet) packet from rfl,
      packet_bindings,bindings_empty]
  intro key member
  simp [GeneralNominalVersionedAllocation231.keys,GeneralNominalVersionedAllocation231.declarationKeys,
    GeneralDeclarations.Declaration.inputNames,GeneralDeclarations.Declaration.outputNames,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] at member

theorem terminal : GeneralNominalVersionedFrame231.children currentPlan.packet = [] := by
  rw [show currentPlan = extendedPlan [] equations [] (GeneralNominalVersionedInstallation231.replayPlan plan) from rfl,
    plan_packet,children_eq,GeneralNominalVersionedInstallation231.replay_children,children_empty]

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready feedback.core root currentPlan := by
  apply (GeneralNominalVersionedReplayEffects232.ready_iff [] equations [] feedback.core root _).mpr
  apply (GeneralNominalVersionedFrameTransport232.ready_iff
    (before := installed.core) (after := feedback.core) (root := root) (fun _ => ⟨fun h => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases (before := installed.core) (after := feedback.core) (root := root)
      (fun _ h => h) (fun _ h => h) h,fun h => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases (before := feedback.core) (after := installed.core) (root := root)
      (fun _ h => h) (fun _ h => h) h⟩)).mp
  exact GeneralNominalVersionedInstalledEvidence233.ready rfl children_empty

theorem effects (assignment) (valid : Models feedback assignment) :
    GeneralNominalVersionedEffects231.ClassEffects feedback.core root currentPlan assignment := by
  apply (GeneralNominalVersionedReplayEffects232.class_effects_iff [] equations [] feedback.core root _ assignment).mpr
  apply (GeneralNominalVersionedFrameTransport232.class_effects_iff
    (before := installed.core) (after := feedback.core) (root := root) (fun _ => ⟨fun h => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases (before := installed.core) (after := feedback.core) (root := root)
      (fun _ h => h) (fun _ h => h) h,fun h => GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases (before := feedback.core) (after := installed.core) (root := root)
      (fun _ h => h) (fun _ h => h) h⟩)).mp
  exact GeneralNominalVersionedInstalledEvidence233.class_effects ((models_iff assignment).mp valid)

theorem certificate (assignment) (valid : Models feedback assignment) :
    GeneralNominalVersionedEvidence231.Certificate registry feedback.core assignment root 37 [] currentPlan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame terminal.symm (holds assignment valid) ready (effects assignment valid)

theorem evidence (assignment) (valid : Models feedback assignment) :
    GeneralNominalVersionedEvidence231.Evidence registry feedback.core assignment root (.node 37 []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨currentPlan,certificate assignment valid⟩

end Yulang.GeneralDictionaryVersionedGap206After234
