import Yulang.GeneralDictionaryNominalRecording
import Yulang.GeneralDictionaryNominalSourceEvidence

/-!
# Actual-source dictionary evidence in the full nominal state

The dictionary's equation transaction preserves the original full-state model
obligations, including nominal descriptors and existing global atoms. The
compiler still handles only supported variable heads/RHSs at existing base slots.
-/
namespace Yulang.GeneralDictionaryNominalStateEvidence
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryTransactions (Frames Prepared)
open GeneralDictionaryNominalSourceEvidence (Instance)

/-- One fixed witness serves every model of the actual full-state transaction.
The original nominal state's constraints are retained, not projected away. -/
theorem prepare_uniform (registry : Registry) (checked : Checked registry)
    (state : GeneralNominalState.State) (frames : Frames registry.roles)
    (payload : GeneralDictionaryReadback.Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state.base)
    (success : GeneralDictionaryPayloadPreparation.prepare registry checked state.base frames payload root = some tree) :
    ∃ witness, Readback root payload witness ∧
      ∀ model, GeneralNominalState.Models (GeneralDictionaryNominalRecording.record state tree.items) model →
        GeneralNominalState.Models state model ∧ Evidence (Instance registry checked frames model) witness := by
  obtain ⟨witness, readback, uniform⟩ :=
    GeneralDictionaryNominalSourceEvidence.prepare_uniform_source registry checked state.base frames payload root tree success
  refine ⟨witness, readback, ?_⟩
  intro model valid
  exact ⟨GeneralDictionaryNominalRecording.record_preserves state tree.items model valid,
    uniform model (GeneralDictionaryNominalRecording.recorded_base_model state tree.items model valid)⟩

/-- The same raw payload is sound in every model of the full nominal transaction.
No source-state Step, candidate selection or total source compiler is asserted. -/
theorem prepare_payload_evidence (registry : Registry) (checked : Checked registry)
    (state : GeneralNominalState.State) (frames : Frames registry.roles)
    (payload : GeneralDictionaryReadback.Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state.base)
    (success : GeneralDictionaryPayloadPreparation.prepare registry checked state.base frames payload root = some tree)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (GeneralDictionaryNominalRecording.record state tree.items) model) :
    GeneralDictionaryReadback.PayloadEvidence (Instance registry checked frames model) root payload := by
  obtain ⟨witness, readback, uniform⟩ := prepare_uniform registry checked state frames payload root tree success
  exact (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ⟨witness, readback, (uniform model valid).2⟩

end Yulang.GeneralDictionaryNominalStateEvidence
