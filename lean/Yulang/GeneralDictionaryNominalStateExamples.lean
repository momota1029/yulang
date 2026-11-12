import Yulang.GeneralDictionaryNominalStateEvidence
import Yulang.GeneralDictionaryNominalSourceExamples

/-! A full nominal state, its exact dictionary transaction, and a genuine
nominal witness. Equation recording retains the unresolved root observation. -/
namespace Yulang.GeneralDictionaryNominalStateExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryNominalExamples (nominalAssignment)
open GeneralDictionaryPayloadReconstructionExamples (payload)
open GeneralDictionaryPayloadPreparationExamples (raw_tree_prepared)
open GeneralSourceDictionaries

abbrev view : GeneralNormalizedObservation.Snapshot state where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro first; exact Fin.elim0 first
  canonical := by intro kind; exact Fin.elim0 kind
  heads := fun _ => .deferred .unresolved
  checked := by intro slot term impossible; cases impossible

abbrev fullState : GeneralNominalState.State :=
  GeneralNominalState.embed state view registry.constructors

theorem full_base_model : GeneralNominalState.Models fullState nominalAssignment := by
  refine ⟨GeneralDictionaryNominalExamples.base_model, ?_, ?_⟩
  · intro slot descriptor impossible; cases impossible
  · intro atom member; cases member

/-- One full-state model satisfies every actual dictionary equation. -/
theorem full_record_model :
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record fullState tree.items) nominalAssignment := by
  apply (GeneralDictionaryNominalRecording.record_models fullState tree.items nominalAssignment).mpr
  exact ⟨full_base_model, ((GeneralDictionaryNominalEquations.batch_models tree.items nominalAssignment).mp
    GeneralDictionaryNominalExamples.tree_joint_model).2⟩

/-- Full-state constraints and original-payload evidence hold in one model. -/
theorem full_nominal_nonvacuous :
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record fullState tree.items) nominalAssignment ∧
      GeneralDictionaryReadback.PayloadEvidence
        (GeneralDictionaryNominalSourceEvidence.Instance registry registry_checked (fun _ => frame) nominalAssignment)
        root payload :=
  ⟨full_record_model, GeneralDictionaryNominalStateEvidence.prepare_payload_evidence registry registry_checked
    fullState (fun _ => frame) payload root tree raw_tree_prepared nominalAssignment full_record_model⟩

theorem full_root_pending : GeneralNominalState.RootPending fullState rootDemand := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  rintro ⟨slot, _, known | ⟨descriptor, present⟩⟩
  · exact known rfl
  · cases present

/-- Dictionary recording is not a readiness transition. -/
theorem recorded_root_pending :
    GeneralNominalState.RootPending (GeneralDictionaryNominalRecording.record fullState tree.items) rootDemand :=
  (GeneralDictionaryNominalRecording.record_pending fullState tree.items rootDemand).mpr full_root_pending

end Yulang.GeneralDictionaryNominalStateExamples
