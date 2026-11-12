import Yulang.GeneralDictionaryPayloadReconstruction
import Yulang.GeneralDictionaryRecipeFidelity

/-!
# Raw dictionary payloads to uniform actual-source evidence

Inputs no longer include any descendant occurrence recipe. The checked registry
and frames reconstruct those obligations before computing locations, variable
heads, output equations and the whole recorded batch. This validates an existing
selected-key tree; it is not an implementation of candidate selection.
-/
namespace Yulang.GeneralDictionaryPayloadPreparation
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralSourceState (State Models)
open GeneralDictionaryPayloadReconstruction (reconstruct)
open GeneralDictionaryRecipeFidelity (recipe)

def prepare (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (payload : Payload) (root : Occurrence registry.roles) :
    Option (Prepared registry.roles state) :=
  (reconstruct registry checked frames payload root).bind fun source =>
    GeneralDictionarySourceRecipe.prepare registry checked state frames (recipe source)

/-- The two phases have separate contracts: exact declaration-plan recovery,
then supported variable materialization. Neither phase checks role readiness. -/
theorem prepare_exact (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (payload : Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state) :
    prepare registry checked state frames payload root = some tree ↔
      ∃ source, reconstruct registry checked frames payload root = some source ∧
        GeneralDictionarySourceRecipe.prepare registry checked state frames (recipe source) = some tree :=
  Option.bind_eq_some_iff

/-- The prepared dictionary reads back the original raw payload, with all keys,
child positions and repeated obligations retained. -/
theorem prepare_readback (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (payload : Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state)
    (success : prepare registry checked state frames payload root = some tree) :
    Readback root payload tree.dictionary := by
  obtain ⟨source, reconstructed, prepared⟩ := (prepare_exact registry checked state frames payload root tree).mp success
  have same := GeneralDictionaryRecipeFidelity.prepare_recipe_tree registry checked state frames source tree prepared
  rw [same]
  exact (GeneralDictionaryPayloadReconstruction.reconstruct_sound registry checked frames payload root source reconstructed).1

/-- One fixed source-indexed witness for the input raw payload works in every
joint model. No recursive occurrence, location, head, RHS or realization input
is required. Selected keys, frames and root readiness are not derived here. -/
theorem prepare_uniform_source (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (payload : Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state)
    (success : prepare registry checked state frames payload root = some tree) :
    ∃ witness, Readback root payload witness ∧
      ∀ assignment, Models (GeneralDictionaryBatchRecording.record tree.items) assignment →
        Evidence (GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) witness := by
  obtain ⟨source, reconstructed, prepared⟩ := (prepare_exact registry checked state frames payload root tree).mp success
  obtain ⟨witness, readback, uniform⟩ :=
    GeneralDictionarySourceRecipe.prepare_uniform_source registry checked state frames (recipe source) tree prepared
  have sourceReadback := (GeneralDictionaryPayloadReconstruction.reconstruct_sound registry checked frames payload root source reconstructed).1
  have treeReadback := prepare_readback registry checked state frames payload root tree success
  refine ⟨witness, ⟨?_, readback.2.trans treeReadback.2⟩, uniform⟩
  exact readback.1.trans ((GeneralDictionaryRecipeFidelity.recipe_root source).trans sourceReadback.1)

/-- The key-only Evidence relation now refers to the same raw input, not a
possibly different dictionary produced by preparation. This is soundness only. -/
theorem prepare_payload_evidence (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (payload : Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles state)
    (success : prepare registry checked state frames payload root = some tree)
    (assignment : GeneralSourceState.Assignment)
    (model : Models (GeneralDictionaryBatchRecording.record tree.items) assignment) :
    PayloadEvidence (GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) root payload := by
  obtain ⟨witness, readback, uniform⟩ := prepare_uniform_source registry checked state frames payload root tree success
  exact (payload_iff_erased _ _ _).mpr ⟨witness, readback, uniform assignment model⟩

end Yulang.GeneralDictionaryPayloadPreparation
