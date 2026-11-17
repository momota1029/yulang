import Yulang.GeneralDictionaryVersionedGap206Safety233
import Yulang.GeneralNominalVersionedInstalledEvidence233
import Yulang.GeneralDictionaryDefaultRegression208
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206Install233
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Safety233
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCenters

noncomputable def effect : Effect roles where
  registry := registry
  snapshot := current.core
  plan := plan
  frame := frame
  unique := children_empty ▸ unique
  ready := GeneralDictionaryDefaultGap206State.ready

noncomputable def installed := install current effect

theorem classes : GeneralNominalVersionedEffects231.ClassEffects current.core root plan model :=
  (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr GeneralDictionaryDefaultGap206State.class_effects

theorem installation_models : InstallationModels current effect model := by
  refine ⟨current_model,packet_holds model current_model,
    ⟨GeneralNominalVersionedPlans231.head_models (packet_holds model current_model),classes⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr classes
  · intro prior member; cases member
  · intro prior member; cases member

theorem installed_model : Models installed model := (install_models rfl).mpr installation_models

theorem positions : GeneralNominalVersionedCycles232.Safe current plan := by
  constructor
  · exact GeneralDictionaryDefaultRegression208.enabled.positions.1
  · intro entry member
    rw [GeneralDictionaryDefaultGap206Local.inspection_exact] at member
    cases List.mem_singleton.mp member
    exact scalar_acyclic

theorem alternatives : GeneralNominalVersionedKernel232.AlternativesSafe registry current plan.input := by
  intro candidate _ framed
  rw [frame_plan framed]
  exact positions

theorem installable : GeneralNominalVersionedKernel232.Installable registry current effect := by
  refine ⟨rfl,rfl,safe,GeneralNominalCenteredHeadMatStepObservations.initial_cache context root,?_,?_,positions,alternatives,model,installation_models⟩
  · rw [show effect.plan = plan from rfl,emitted_empty]
  · intro prior member; cases member

theorem counter_model : Models current counter :=
  (lift_models start counter).mpr GeneralDictionaryDefaultGap206State.counter_inhabited

theorem not_committed : ¬ GeneralNominalVersionedKernel232.Committed current plan := by
  intro committed
  have effects := (committed.1 counter counter_model).2
  have cert := GeneralNominalVersionedEvidence231.certificate_of_semantics frame children_empty.symm
    (packet_holds counter counter_model) GeneralDictionaryDefaultGap206State.ready effects
  exact GeneralDictionaryDefaultGap206Counterexample.no_default_output
    (cert.outputs ⟨0,0⟩ (List.mem_singleton_self _))

theorem step : GeneralNominalVersionedKernel232.Step registry root current installed :=
  ⟨root,.root,.install effect installable not_committed⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root installed :=
  ⟨current,initial,.tail .refl step⟩

theorem evidence (assignment : GeneralNominalCommonBridge.Assignment) (valid : Models installed assignment) :
    GeneralNominalVersionedEvidence231.Evidence registry installed.core assignment root (.node 37 []) :=
  GeneralNominalVersionedInstalledEvidence233.evidence rfl children_empty valid

theorem bottom_removed : ¬ Models installed counter := by
  intro valid
  have cert := GeneralNominalVersionedInstalledEvidence233.certificate rfl children_empty valid
  have witness := cert.outputs ⟨0,0⟩ (List.mem_singleton_self _)
  exact GeneralDictionaryDefaultGap206Counterexample.no_default_output
    ((GeneralNominalVersionedReplayEffects232.replay_output_witness_iff plan counter ⟨0,0⟩).mp witness)

theorem genuine_change : Models current counter ∧ ¬ GeneralNominalVersionedKernel232.Committed current plan ∧
    GeneralNominalVersionedKernel232.Step registry root current installed ∧ Models installed model ∧
    ¬ Models installed counter ∧ ∀ assignment, Models installed assignment →
      GeneralNominalVersionedEvidence231.Evidence registry installed.core assignment root (.node 37 []) :=
  ⟨counter_model,not_committed,step,installed_model,bottom_removed,evidence⟩

end Yulang.GeneralDictionaryVersionedGap206Install233
