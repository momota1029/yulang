import Yulang.GeneralDictionaryVersionedBothStage233
import Yulang.GeneralDictionaryVersionedPointSafety233
import Yulang.GeneralNominalVersionedInstalledEvidence233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedSecondInstall233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPointStage233
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232

noncomputable abbrev plan := GeneralDictionaryVersionedPoint233.plan allocated reserved ordinary

theorem terminal : GeneralNominalVersionedFrame231.children plan.packet = [] :=
  GeneralDictionaryVersionedPoint233.children_empty allocated reserved ordinary

noncomputable def effect : Effect roles where
  registry := registry
  snapshot := point.core
  plan := plan
  frame := GeneralDictionaryVersionedPointSafety233.frame
  unique := terminal ▸ GeneralDictionaryVersionedPointFrame233.unique allocated reserved ordinary
    GeneralDictionaryVersionedBothStage233.values GeneralDictionaryVersionedBothStage233.point_model.1.1
    (fun purpose _ => GeneralDictionaryVersionedPointFresh233.fresh_outside purpose)
  ready := GeneralDictionaryVersionedPointFrame233.ready allocated reserved ordinary raw_sites

noncomputable def installed := install point effect

theorem classes : GeneralNominalVersionedEffects231.ClassEffects point.core root plan extended :=
  GeneralDictionaryVersionedPointFrame233.class_effects allocated reserved ordinary
    GeneralDictionaryVersionedBothStage233.values.output raw_sites

theorem installation_models : InstallationModels point effect extended := by
  have valid := GeneralDictionaryVersionedBothStage233.point_model
  refine ⟨valid,GeneralDictionaryVersionedBothStage233.point_packet,
    ⟨GeneralNominalVersionedPlans231.head_models GeneralDictionaryVersionedBothStage233.point_packet,classes⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff terminal)).mpr classes
  · exact GeneralNominalVersionedTerminal232.legacy_live terminal valid.1
  · intro prior member
    exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff terminal)).mpr (valid.2.2 prior member).2

theorem installed_model : Models installed extended := (install_models rfl).mpr installation_models

theorem evidence {model : GeneralNominalCommonBridge.Assignment} (valid : Models installed model) :
    GeneralNominalVersionedEvidence231.Evidence registry installed.core model root (.node declaration.id []) :=
  GeneralNominalVersionedInstalledEvidence233.evidence rfl terminal valid

theorem old_and_new : GeneralDictionaryOptionalInstall229.plan ∈ installed.plans ∧ plan ∈ installed.plans :=
  ⟨List.mem_cons_of_mem _ original_plan_retained,List.mem_cons_self ..⟩

end Yulang.GeneralDictionaryVersionedSecondInstall233
