import Yulang.GeneralDictionaryPayloadPreparation
import Yulang.GeneralDictionaryPayloadReconstructionExamples
import Yulang.GeneralDictionarySourceRecipeExamples
import Yulang.GeneralDictionaryHeadlessPendingBoundary

/-!
# Raw payload preparation, source semantics, and remaining boundaries

The same raw key tree produces actual-source evidence in a concrete joint model.
Successful materialization neither resolves a pending root nor invents an absent
source slot. Descendant occurrences are reconstructed rather than supplied.
-/
namespace Yulang.GeneralDictionaryPayloadPreparationExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryPayloadPreparation
open GeneralDictionaryPayloadReconstructionExamples (payload sourceTree tree_reconstructed leaf_reconstructed)
open GeneralSourceDictionaries
open GeneralSourceState (Models RootPending)
open GeneralDictionaryBatchRecording (record)
open GeneralDictionaryHeadlessSourceEvidence (Instance)

theorem raw_tree_prepared :
    prepare registry registry_checked state (fun _ => frame) payload root = some tree := by
  apply (prepare_exact registry registry_checked state (fun _ => frame) payload root tree).mpr
  refine ⟨sourceTree, tree_reconstructed, ?_⟩
  simpa only [sourceTree, GeneralDictionaryRecipeFidelity.recipe, List.map_cons, List.map_nil] using
    GeneralDictionarySourceRecipeExamples.tree_prepared

/-- The witness reads back the input payload, not only the prepared output. -/
theorem raw_uniform_source :
    ∃ witness, Readback root payload witness ∧
      ∀ model, Models (record tree.items) model →
        Evidence (Instance registry registry_checked (fun _ => frame) model) witness :=
  prepare_uniform_source registry registry_checked state (fun _ => frame) payload root tree raw_tree_prepared

theorem raw_source_nonvacuous :
    prepare registry registry_checked state (fun _ => frame) payload root = some tree ∧
      Models (record tree.items) assignment ∧
      ∃ witness, Readback root payload witness ∧
        Evidence (Instance registry registry_checked (fun _ => frame) assignment) witness := by
  obtain ⟨witness, readback, uniform⟩ := raw_uniform_source
  exact ⟨raw_tree_prepared, tree_joint_model, witness, readback, uniform assignment tree_joint_model⟩

theorem raw_payload_evidence :
    GeneralDictionaryReadback.PayloadEvidence
      (Instance registry registry_checked (fun _ => frame) assignment) root payload :=
  prepare_payload_evidence registry registry_checked state (fun _ => frame) payload root tree
    raw_tree_prepared assignment tree_joint_model

/-- Materializing every equation still does not discharge all-input readiness. -/
theorem raw_preparation_with_pending :
    prepare registry registry_checked state (fun _ => frame) payload root = some tree ∧
      RootPending state rootDemand GeneralDictionaryHeadlessPendingBoundary.allInputs :=
  ⟨raw_tree_prepared, GeneralDictionaryHeadlessPendingBoundary.root_still_pending⟩

open GeneralDictionarySourceRecipeExamples (absentOutputRoot absentOutputRecipe)

private theorem absent_root_reconstructed :
    GeneralDictionaryPayloadReconstruction.reconstruct registry registry_checked (fun _ => frame)
      payload absentOutputRoot = some (.node absentOutputRoot 2 [.node child 3 []]) := by
  have found : GeneralDictionaryPlanLookup.lookup registry registry_checked frame absentOutputRoot 2 =
      some [child] := by
    apply (GeneralDictionaryPlanLookup.lookup_exact registry registry_checked frame absentOutputRoot 2 [child]).mpr
    exact ⟨binderWrap, by simp, rfl, rfl, root_actual_children.symm⟩
  apply GeneralDictionaryPayloadReconstruction.reconstruct_complete registry registry_checked (fun _ => frame)
    (.node absentOutputRoot 2 [.node child 3 []])
  apply Evidence.node
  · exact (GeneralDictionaryPlanLookup.lookup_exact registry registry_checked frame absentOutputRoot 2 [child]).mp found
  · intro tree member
    have same := List.mem_singleton.mp member
    subst tree
    exact (GeneralDictionaryPayloadReconstruction.reconstruct_sound registry registry_checked (fun _ => frame)
      (.node 3 []) child _ leaf_reconstructed).2

/-- Plan recovery succeeds, but an absent output slot still defers materialization. -/
theorem absent_output_preparation_defers :
    prepare registry registry_checked state (fun _ => frame) payload absentOutputRoot = none := by
  rw [prepare, absent_root_reconstructed]
  simpa only [Option.bind_some, GeneralDictionaryRecipeFidelity.recipe, List.map_cons, List.map_nil] using
    GeneralDictionarySourceRecipeExamples.absent_output_preparation_defers

end Yulang.GeneralDictionaryPayloadPreparationExamples
