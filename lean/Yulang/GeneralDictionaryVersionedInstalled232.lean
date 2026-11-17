import Yulang.GeneralNominalVersionedTerminal232
import Yulang.GeneralDictionaryVersionedModelExtension231
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedInstalled232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCommonBridge (Assignment)

noncomputable def before : State roles := lift after

noncomputable def effect : Effect roles where
  registry := registry
  snapshot := after.core
  plan := currentPlan
  frame := GeneralDictionaryVersionedEvidence231.frame
  unique := by
    rw [GeneralDictionaryVersionedEvidence231.children_empty]
    exact GeneralDictionaryVersionedPrepared231.unique
  ready := GeneralDictionaryUpper230Selected.ready

noncomputable def installed : State roles := install before effect

theorem snapshot : effect.snapshot = before.core := rfl
theorem terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [] :=
  GeneralDictionaryVersionedEvidence231.children_empty

theorem requests_iff :
    output ∈ GeneralNominalCenteredHeadOutputs.requests installed.core root ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests after.core root :=
  GeneralNominalVersionedTerminal232.requests_iff terminal

theorem installation_models (valid : GeneralDictionaryVersionedCompletion231.InstallationModels m) :
    InstallationModels before effect m := by
  have branch := GeneralDictionaryVersionedCompletion231.packet_holds valid
  have classes := GeneralDictionaryVersionedCompletion231.class_effects valid
  refine ⟨(lift_models after m).mpr valid.1,branch,
    ⟨GeneralNominalVersionedPlans231.head_models branch,classes⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun output => requests_iff (output := output))).mpr classes
  · exact GeneralNominalVersionedTerminal232.legacy_live terminal valid.1
  · intro prior member; cases member

theorem models_iff (m : Assignment) : Models installed m ↔
    GeneralDictionaryVersionedCompletion231.InstallationModels m := by
  rw [installed,install_models snapshot]
  constructor
  · intro valid
    refine ⟨valid.1.1,?_⟩
    have merge := valid.2.1.2.1.1.2.1
    change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (GeneralNominalVersionedAllocation231.merges _ _ _ _ currentPacket.bindings) at merge
    rw [GeneralDictionaryUpper230Current.bindings_exact] at merge
    exact merge
  · exact installation_models

theorem inhabited : ∃ m, Models installed m := by
  obtain ⟨m,valid⟩ := GeneralDictionaryVersionedCompletion231.inhabited
  exact ⟨m,(models_iff m).mpr valid⟩

theorem actual_plan_recorded : currentPlan ∈ installed.plans := List.mem_cons_self ..
theorem actual_effect_recorded : effect ∈ installed.effects := List.mem_cons_self ..
theorem legacy_plans_retained : installed.core.plans = after.core.plans := rfl
theorem legacy_effects_retained : installed.legacy.effects = after.effects := rfl

theorem every_model_extends (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m) :
    ∃ n, Models installed n ∧
      ∀ source ∈ GeneralDictionaryDefaultJournalSupport213.journalSources after, n source = m source := by
  refine ⟨GeneralDictionaryVersionedModelExtension231.extend m,?_,
    GeneralDictionaryVersionedModelExtension231.source_preserved m⟩
  exact (models_iff _).mpr
    ⟨GeneralDictionaryVersionedModelExtension231.retains valid,
      GeneralDictionaryVersionedModelExtension231.merges m⟩

end Yulang.GeneralDictionaryVersionedInstalled232
