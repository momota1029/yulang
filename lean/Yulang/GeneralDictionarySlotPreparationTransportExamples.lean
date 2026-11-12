import Yulang.GeneralDictionarySlotPreparationTransport
import Yulang.GeneralDictionaryNominalSlotTransportExamples
import Yulang.GeneralDictionaryNominalStateEvidence
import Yulang.GeneralDictionaryHeadlessFixture

/-!
# Successful raw materialization across a strict nominal slot enlargement

A checked terminal variable-head declaration requests the same explicit output
twice. The supplied mixed nominal snapshot grows from two to three slots while
retaining a real nominal descriptor with separate type and row bounds. Frames
are held fixed. This is not a candidate-survival or readiness regression.
-/
namespace Yulang.GeneralDictionarySlotPreparationTransportExamples
open GeneralDictionaryNominalSlotTransportExamples
open GeneralDictionaryHeadlessFixture (roles registry registry_checked leaf)
open GeneralSourceDictionaries
open GeneralDictionarySlotPreparationTransport (prepared)

abbrev demand : GeneralSourceState.Demand roles where
  role := 2
  arguments := fun _ => (10, 10)
  outputs := [⟨1, 10⟩, ⟨1, 10⟩]
  declared := by
    intro output member
    have same : output = ⟨1, 10⟩ := by simpa using member
    subst output
    exact ⟨none, rfl⟩

abbrev root : Occurrence roles := ⟨300, demand⟩
abbrev payload : GeneralDictionaryReadback.Payload := .node 3 []
abbrev frame : GeneralDictionaryEmissionPlans.Frame roles :=
  { GeneralDictionaryHeadlessFixture.frame with capture := fun _ => ⟨fun _ => (10, 10), fun _ => 10⟩ }
abbrev frames : GeneralDictionaryTransactions.Frames roles := fun _ => frame

abbrev located : GeneralDictionaryStateEquations.Located mixedBefore.base demand where
  lower := fun _ => 0
  upper := fun _ => 0
  head := fun _ => .var 0
  target := fun _ => 0
  output := fun _ => .var 0
  arguments := by intro _; rfl
  targets := by
    rintro ⟨index, bound⟩
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

/-- The source dictionary retains both output occurrences in its root demand. -/
abbrev sourceTree : Dictionary roles := .node root 3 []
abbrev tree : GeneralDictionaryTransactions.Prepared roles mixedBefore.base := .node root 3 located []
abbrev movedTree := prepared mixedTransport tree

private abbrev headless : GeneralDictionaryVariableHeads.HeadlessInputs mixedBefore.base demand where
  lower := located.lower
  upper := located.upper
  target := located.target
  arguments := located.arguments
  targets := located.targets

private abbrev inputs : GeneralDictionaryBinderLocations.Inputs mixedBefore.base demand where
  lower := located.lower
  upper := located.upper
  head := located.head
  target := located.target
  arguments := located.arguments
  targets := located.targets

private abbrev result : GeneralDictionaryHeadlessPlans.Result mixedBefore.base root :=
  ⟨inputs, ⟨[], located⟩⟩

private theorem no_children :
    GeneralDictionaryEmissionPlans.children frame root leaf GeneralDictionaryHeadlessFixture.leaf_checked = [] := by
  simp [GeneralDictionaryEmissionPlans.children, GeneralCanonicalChildOrder.canonicalEmit,
    GeneralCanonicalChildOrder.canonicalDeclaration, GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll, leaf]

private theorem lookup_success :
    GeneralDictionaryHeadlessPlans.lookup registry registry_checked frame root 3 headless = some result := by
  apply (GeneralDictionaryHeadlessPlans.lookup_exact registry registry_checked frame root 3 headless result).mpr
  refine ⟨leaf, by simp, rfl, rfl, rfl, rfl, rfl, ?_, ?_, no_children.symm⟩
  · refine ⟨rfl, rfl, ?_⟩
    intro index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    refine ⟨.var 0, 0, 0, ?_, rfl, ?_, rfl, rfl, rfl⟩
    · simp only [zero]; rfl
    · decide +kernel
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    intro index
    refine ⟨0, rfl, ?_⟩
    apply (GeneralDictionaryVariableMaterialization.compile_slot_exact roles mixedBefore.base leaf _
      GeneralDictionaryHeadlessFixture.leaf_checked.identified.2.2.1 _ 0).mp
    obtain ⟨index, bound⟩ := index
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

/-- The actual raw executor succeeds; neither local package is its input. -/
theorem preparation_success :
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedBefore.base frames payload root = some tree := by
  have reconstructed : GeneralDictionaryPayloadReconstruction.reconstruct registry registry_checked frames payload root =
      some sourceTree := by
    apply GeneralDictionaryPayloadReconstruction.reconstruct_complete registry registry_checked frames sourceTree
    apply Evidence.node
    · exact ⟨leaf, by simp, rfl, rfl, no_children.symm⟩
    · intro child impossible; cases impossible
  apply (GeneralDictionaryPayloadPreparation.prepare_exact registry registry_checked mixedBefore.base frames
    payload root tree).mpr
  refine ⟨sourceTree, reconstructed, ?_⟩
  apply (GeneralDictionarySourceRecipe.prepare_exact registry registry_checked mixedBefore.base frames _ tree).mpr
  refine ⟨.node root 3 headless [], ?_, ?_⟩
  · simp only [sourceTree, GeneralDictionaryRecipeFidelity.recipe, List.map_nil]
    rw [GeneralDictionarySourceRecipe.localize, GeneralDictionaryHeadlessLocations.locate_inputs headless]
    rfl
  · apply (GeneralDictionaryHeadlessPreparation.prepare_node_exact registry registry_checked frames root 3
      headless [] tree).mpr
    exact ⟨result, lookup_success, [], rfl, rfl, rfl⟩

theorem moved_preparation_success :
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedAfter.base frames payload root = some movedTree :=
  GeneralDictionarySlotPreparationTransport.payload_prepare_success mixedTransport registry registry_checked
    frames payload root tree preparation_success

theorem exact_shared_dictionary : tree.dictionary = sourceTree ∧ movedTree.dictionary = sourceTree :=
  ⟨rfl, GeneralDictionarySlotPreparationTransport.prepared_dictionary mixedTransport tree⟩

/-- These are nonempty constraints: one nominal descriptor has both type and row
bounds, and the prepared root has an input plus two output occurrences. -/
theorem nonempty_obligations :
    mixedBefore.nominals 0 = some mixedDescriptor ∧ mixedDescriptor.arguments.length = 2 ∧
    demand.outputs.length = 2 ∧ tree.items.length = 1 ∧
    GeneralDictionaryBatchRecording.batchAtoms tree.items ≠ [] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp [GeneralDictionaryTransactions.Prepared.items, GeneralDictionaryBatchRecording.batchAtoms,
    GeneralDictionaryEquationRecording.atoms]

/-- The same genuine nominal assignment satisfies the entire old dictionary batch. -/
theorem recorded_model : GeneralNominalState.Models
    (GeneralDictionaryNominalRecording.record mixedBefore tree.items) mixedAssignment := by
  apply (GeneralDictionaryNominalRecording.record_models _ _ _).mpr
  refine ⟨mixed_nominal_nonvacuous.1, ?_⟩
  intro item member
  have same : item = ⟨demand, located⟩ := List.mem_singleton.mp member
  subst item
  constructor
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · rintro ⟨index, bound⟩
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;>
      exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩

theorem moved_recorded_model : GeneralNominalState.Models
    (GeneralDictionaryNominalRecording.record mixedAfter movedTree.items) mixedAssignment := by
  apply (GeneralDictionaryNominalRecording.record_models _ _ _).mpr
  refine ⟨mixed_nominal_nonvacuous.2, ?_⟩
  intro item member
  have same : item = ⟨demand, GeneralDictionarySlotMaterializationTransport.located mixedTransport located⟩ := by
    simpa only [movedTree, tree, prepared, List.map_nil, GeneralDictionaryTransactions.Prepared.items,
      GeneralDictionaryTransactions.childItems, List.append_nil, List.mem_singleton] using member
  subst item
  constructor
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · rintro ⟨index, bound⟩
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;>
      exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩

/-- The actual returned source tree has declaration meaning in the same joint
nominal model. No independent candidate applicability is assumed or concluded. -/
theorem shared_source_evidence :
    Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry registry_checked frames mixedAssignment) sourceTree := by
  obtain ⟨source, _, sourcePrepared⟩ :=
    (GeneralDictionaryPayloadPreparation.prepare_exact registry registry_checked mixedBefore.base frames
      payload root tree).mp preparation_success
  obtain ⟨localized, _, built⟩ :=
    (GeneralDictionarySourceRecipe.prepare_exact registry registry_checked mixedBefore.base frames _ tree).mp sourcePrepared
  exact GeneralDictionaryNominalSourceEvidence.transaction_evidence registry registry_checked frames tree
    (GeneralDictionaryHeadlessPreparation.prepare_built registry registry_checked frames localized tree built)
    mixedAssignment (GeneralDictionaryNominalRecording.recorded_base_model mixedBefore tree.items
      mixedAssignment recorded_model)

/-- Strict growth, both successful raw executions, nonvacuous joint recorded
models and one unchanged readback witness hold simultaneously. -/
theorem strict_preparation_joint :
    mixedBefore.base.slots < mixedAfter.base.slots ∧
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedBefore.base frames payload root = some tree ∧
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedAfter.base frames payload root = some movedTree ∧
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record mixedBefore tree.items) mixedAssignment ∧
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record mixedAfter movedTree.items) mixedAssignment ∧
    Readback root payload sourceTree ∧ tree.dictionary = sourceTree ∧ movedTree.dictionary = sourceTree ∧
    Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry registry_checked frames mixedAssignment) sourceTree :=
  ⟨by decide, preparation_success, moved_preparation_success, recorded_model, moved_recorded_model,
    ⟨rfl, rfl⟩, exact_shared_dictionary.1, exact_shared_dictionary.2, shared_source_evidence⟩

end Yulang.GeneralDictionarySlotPreparationTransportExamples
