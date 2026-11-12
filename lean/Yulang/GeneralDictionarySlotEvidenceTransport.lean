import Yulang.GeneralDictionarySlotPreparationTransport
import Yulang.GeneralDictionaryNominalBatchTransport
import Yulang.GeneralDictionaryNominalStateEvidence

/-!
# The same prepared source dictionary across a certified slot enlargement

Successful raw preparation, the entire finite equation batch and its full nominal
model set are transported together. One unchanged source dictionary witnesses
actual declaration meaning at every joint model. Registry, global frames and
raw payload stay fixed. This does not supply the target snapshot or discover a
candidate forest, and does not compare contexts whose inspection views differ.
-/
namespace Yulang.GeneralDictionarySlotEvidenceTransport
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryTransactions (Prepared Frames childItems)
open GeneralDictionaryNominalSlotTransport (Transport)
open GeneralDictionarySlotPreparationTransport (prepared)
open GeneralDictionaryNominalBatchTransport (items item)
open GeneralNominalCommonBridge (Assignment)
variable {before after : GeneralNominalState.State} {roles : Roles.RoleDecls}

private theorem childItems_flatten (children : List (Prepared roles state)) :
    childItems children = (children.map Prepared.items).flatten := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp only [childItems, List.map_cons, List.flatten_cons, ih]

/-- No child obligations are lost or deduplicated in the transported transaction. -/
theorem prepared_items (transport : Transport before after) (tree : Prepared roles before.base) :
    (prepared transport tree).items = items transport tree.items := by
  cases tree with
  | node root key located children =>
    simp only [prepared, Prepared.items, items, List.map_cons]
    congr 1
    rw [childItems_flatten, childItems_flatten, List.map_flatten]
    simp only [List.map_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro child member
    exact prepared_items transport child
termination_by sizeOf tree

/-- Exact model equivalence includes the whole source state's nominal descriptor
constraints and every repeated dictionary obligation at one global assignment. -/
theorem recorded_models (transport : Transport before after) (tree : Prepared roles before.base)
    (model : Assignment) :
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record after (prepared transport tree).items) model ↔
      GeneralNominalState.Models (GeneralDictionaryNominalRecording.record before tree.items) model := by
  rw [prepared_items]
  exact GeneralDictionaryNominalBatchTransport.record_models transport tree.items model

/-- Successful preparation justifies the actual returned tree, rather than a
separate existential witness unrelated to the transported transaction. -/
theorem source_evidence (registry : Registry) (checked : Checked registry)
    (state : GeneralNominalState.State) (frames : Frames registry.roles)
    (raw : GeneralDictionaryReadback.Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state.base)
    (success : GeneralDictionaryPayloadPreparation.prepare registry checked state.base frames raw root = some tree)
    (model : Assignment)
    (valid : GeneralNominalState.Models (GeneralDictionaryNominalRecording.record state tree.items) model) :
    Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry checked frames model) tree.dictionary := by
  obtain ⟨source, _, sourcePrepared⟩ :=
    (GeneralDictionaryPayloadPreparation.prepare_exact registry checked state.base frames raw root tree).mp success
  obtain ⟨localized, _, built⟩ :=
    (GeneralDictionarySourceRecipe.prepare_exact registry checked state.base frames _ tree).mp sourcePrepared
  exact GeneralDictionaryNominalSourceEvidence.transaction_evidence registry checked frames tree
    (GeneralDictionaryHeadlessPreparation.prepare_built registry checked frames localized tree built) model
    (GeneralDictionaryNominalRecording.recorded_base_model state tree.items model valid)

/-- One unchanged readback works for all target-transaction models. The source
snapshot and target snapshot are both retained, not projected to bare equations. -/
theorem prepare_uniform_transport (transport : Transport before after)
    (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
    (raw : GeneralDictionaryReadback.Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles before.base)
    (success : GeneralDictionaryPayloadPreparation.prepare registry checked before.base frames raw root = some tree) :
    GeneralDictionaryPayloadPreparation.prepare registry checked after.base frames raw root =
      some (prepared transport tree) ∧
    (prepared transport tree).dictionary = tree.dictionary ∧
    ∃ witness, Readback root raw witness ∧ witness = tree.dictionary ∧
      ∀ model,
        GeneralNominalState.Models
          (GeneralDictionaryNominalRecording.record after (prepared transport tree).items) model →
        GeneralNominalState.Models before model ∧ GeneralNominalState.Models after model ∧
          Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry checked frames model) witness := by
  refine ⟨GeneralDictionarySlotPreparationTransport.payload_prepare_success transport registry checked frames raw root tree success,
    GeneralDictionarySlotPreparationTransport.prepared_dictionary transport tree, tree.dictionary,
    GeneralDictionaryPayloadPreparation.prepare_readback registry checked before.base frames raw root tree success,
    rfl, ?_⟩
  intro model valid
  have old := (recorded_models transport tree model).mp valid
  exact ⟨GeneralDictionaryNominalRecording.record_preserves before tree.items model old,
    GeneralDictionaryNominalRecording.record_preserves after (prepared transport tree).items model valid,
    source_evidence registry checked before frames raw root tree success model old⟩

end Yulang.GeneralDictionarySlotEvidenceTransport
