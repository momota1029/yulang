import Yulang.GeneralDictionaryNominalSourceEvidence
import Yulang.GeneralDictionaryNominalExamples
import Yulang.GeneralDictionaryPayloadPreparationExamples

/-! A concrete nominal model witnesses nonvacuous source evidence for the raw
selected-key payload. Preparation still leaves the source root pending. -/
namespace Yulang.GeneralDictionaryNominalSourceExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryPayloadReconstructionExamples (payload)
open GeneralDictionaryPayloadPreparationExamples (raw_tree_prepared)
open GeneralDictionaryNominalExamples (nominalAssignment tree_joint_model)
open GeneralSourceDictionaries
open GeneralDictionaryNominalSourceEvidence (Instance)

/-- An actual nominal assignment satisfies the fixed source dictionary witness. -/
theorem raw_nominal_nonvacuous :
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked state (fun _ => frame) payload root = some tree ∧
      GeneralNominalCommonBridge.Models (GeneralDictionaryBatchRecording.record tree.items) nominalAssignment ∧
      ∃ witness, Readback root payload witness ∧
        Evidence (Instance registry registry_checked (fun _ => frame) nominalAssignment) witness := by
  obtain ⟨witness, readback, uniform⟩ := GeneralDictionaryNominalSourceEvidence.prepare_uniform_source
    registry registry_checked state (fun _ => frame) payload root tree raw_tree_prepared
  exact ⟨raw_tree_prepared, tree_joint_model, witness, readback, uniform nominalAssignment tree_joint_model⟩

/-- The original key-only payload also has independent nominal source evidence. -/
theorem raw_nominal_payload_evidence :
    GeneralDictionaryReadback.PayloadEvidence
      (Instance registry registry_checked (fun _ => frame) nominalAssignment) root payload := by
  obtain ⟨_, _, witness, readback, evidence⟩ := raw_nominal_nonvacuous
  exact (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ⟨witness, readback, evidence⟩

end Yulang.GeneralDictionaryNominalSourceExamples
