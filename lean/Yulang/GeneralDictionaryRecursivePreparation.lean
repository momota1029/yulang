import Yulang.GeneralDictionaryRecursiveReadback
import Yulang.GeneralDictionaryNominalStateEvidence

/-!
# Partial dictionary transactions over recursive candidate frames

The actual recursive source occurrence tree is retained. Existing supported-variable
materialization is still partial; nominal or compound head/RHS compilation is not
made total by this adapter. Per-model source meaning is proved for every model of
the explicitly recorded transaction state, never every unpropagated source model.
-/
namespace Yulang.GeneralDictionaryRecursivePreparation
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralNominalRecursiveCandidates (Context Survivor)
open GeneralDictionaryTransactions (Prepared)
open GeneralDictionaryRecursiveReadback (frames)

/-- Compute the existing candidate frames, then use the existing partial materializer. -/
def prepare (registry : Registry) (checked : Checked registry) (context : Context)
    (payload : Payload) (root : Occurrence registry.roles) : Option (Prepared registry.roles context.state.base) :=
  GeneralDictionaryPayloadPreparation.prepare registry checked context.state.base
    (frames registry context) payload root

/-- Materialization retains the independently justified candidate tree exactly. -/
theorem prepare_candidate_evidence (registry : Registry) (checked : Checked registry) (context : Context)
    (payload : Payload) (root : Occurrence registry.roles) (tree : Prepared registry.roles context.state.base)
    (candidate : PayloadEvidence (Survivor registry context) root payload)
    (success : prepare registry checked context payload root = some tree) :
    Evidence (Survivor registry context) tree.dictionary := by
  obtain ⟨source, reconstructed, prepared⟩ :=
    (GeneralDictionaryPayloadPreparation.prepare_exact registry checked context.state.base
      (frames registry context) payload root tree).mp success
  obtain ⟨candidateTree, recovered, _, evidence⟩ :=
    GeneralDictionaryRecursiveReadback.payload_candidate_readback registry checked context root payload candidate
  have same : source = candidateTree := Option.some.inj (reconstructed.symm.trans recovered)
  have fidelity := GeneralDictionaryRecipeFidelity.prepare_recipe_tree registry checked context.state.base
    (frames registry context) source tree prepared
  rw [fidelity, same]
  exact evidence

/-- Source equations are valid on the same concrete returned dictionary, not just
some independently chosen readback witness. -/
theorem prepare_source_evidence (registry : Registry) (checked : Checked registry) (context : Context)
    (payload : Payload) (root : Occurrence registry.roles) (tree : Prepared registry.roles context.state.base)
    (success : prepare registry checked context payload root = some tree)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (GeneralDictionaryNominalRecording.record context.state tree.items) model) :
    Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry checked (frames registry context) model)
      tree.dictionary := by
  obtain ⟨source, _, prepared⟩ :=
    (GeneralDictionaryPayloadPreparation.prepare_exact registry checked context.state.base
      (frames registry context) payload root tree).mp success
  obtain ⟨localized, _, built⟩ :=
    (GeneralDictionarySourceRecipe.prepare_exact registry checked context.state.base
      (frames registry context) _ tree).mp prepared
  exact GeneralDictionaryNominalSourceEvidence.transaction_evidence registry checked
    (frames registry context) tree
    (GeneralDictionaryHeadlessPreparation.prepare_built registry checked (frames registry context) localized tree built)
    model (GeneralDictionaryNominalRecording.recorded_base_model context.state tree.items model valid)

/-- One fixed witness jointly retains candidate evidence and actual-source
semantics for every full-state transaction model. Model existence is not assumed. -/
theorem prepare_uniform_joint (registry : Registry) (checked : Checked registry) (context : Context)
    (payload : Payload) (root : Occurrence registry.roles) (tree : Prepared registry.roles context.state.base)
    (candidate : PayloadEvidence (Survivor registry context) root payload)
    (success : prepare registry checked context payload root = some tree) :
    ∃ witness, Readback root payload witness ∧ Evidence (Survivor registry context) witness ∧
      ∀ model, GeneralNominalState.Models (GeneralDictionaryNominalRecording.record context.state tree.items) model →
        GeneralNominalState.Models context.state model ∧
          Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry checked (frames registry context) model) witness := by
  refine ⟨tree.dictionary,
    GeneralDictionaryPayloadPreparation.prepare_readback registry checked context.state.base
      (frames registry context) payload root tree success,
    prepare_candidate_evidence registry checked context payload root tree candidate success, ?_⟩
  intro model valid
  exact ⟨GeneralDictionaryNominalRecording.record_preserves context.state tree.items model valid,
    prepare_source_evidence registry checked context payload root tree success model valid⟩

end Yulang.GeneralDictionaryRecursivePreparation
