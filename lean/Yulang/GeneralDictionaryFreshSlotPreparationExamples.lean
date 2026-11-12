import Yulang.GeneralDictionarySlotEvidenceTransport
import Yulang.GeneralDictionaryNominalSlotTransportExamples
import Yulang.GeneralDictionaryNominalStateEvidence
import Yulang.GeneralDictionaryHeadlessFixture

/-!
# Raw dictionary materialization actually uses a newly represented reserved ID

A checked terminal variable-head declaration requests the same explicit output
twice at reserved identity88. The old snapshot has no type slot for that ID. The supplied mixed nominal snapshot grows from two to three slots while
retaining a real nominal descriptor with separate type and row bounds. Frames
are held fixed. This is not a candidate-survival or readiness regression.
-/
namespace Yulang.GeneralDictionaryFreshSlotPreparationExamples
open GeneralDictionaryNominalSlotTransportExamples
open GeneralDictionaryHeadlessFixture (roles registry registry_checked leaf)
open GeneralSourceDictionaries
open GeneralDictionarySlotPreparationTransport (prepared)

abbrev demand : GeneralSourceState.Demand roles where
  role := 2
  arguments := fun _ => (88, 88)
  outputs := [⟨1, 88⟩, ⟨1, 88⟩]
  declared := by
    intro output member
    have same : output = ⟨1, 88⟩ := by simpa using member
    subst output
    exact ⟨none, rfl⟩

abbrev root : Occurrence roles := ⟨301, demand⟩
abbrev payload : GeneralDictionaryReadback.Payload := .node 3 []
abbrev frame : GeneralDictionaryEmissionPlans.Frame roles :=
  { GeneralDictionaryHeadlessFixture.frame with capture := fun _ => ⟨fun _ => (88, 88), fun _ => 88⟩ }
abbrev frames : GeneralDictionaryTransactions.Frames roles := fun _ => frame

abbrev located : GeneralDictionaryStateEquations.Located mixedAfter.base demand where
  lower := fun _ => 2
  upper := fun _ => 2
  head := fun _ => .var 2
  target := fun _ => 2
  output := fun _ => .var 2
  arguments := by intro _; rfl
  targets := by
    rintro ⟨index, bound⟩
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

/-- The source dictionary retains both output occurrences in its root demand. -/
abbrev sourceTree : Dictionary roles := .node root 3 []
abbrev tree : GeneralDictionaryTransactions.Prepared roles mixedAfter.base := .node root 3 located []

private abbrev headless : GeneralDictionaryVariableHeads.HeadlessInputs mixedAfter.base demand where
  lower := located.lower
  upper := located.upper
  target := located.target
  arguments := located.arguments
  targets := located.targets

private abbrev inputs : GeneralDictionaryBinderLocations.Inputs mixedAfter.base demand where
  lower := located.lower
  upper := located.upper
  head := located.head
  target := located.target
  arguments := located.arguments
  targets := located.targets

private abbrev result : GeneralDictionaryHeadlessPlans.Result mixedAfter.base root :=
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
    refine ⟨.var 0, 0, 2, ?_, rfl, ?_, rfl, rfl, rfl⟩
    · simp only [zero]; rfl
    · decide +kernel
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    intro index
    refine ⟨2, rfl, ?_⟩
    apply (GeneralDictionaryVariableMaterialization.compile_slot_exact roles mixedAfter.base leaf _
      GeneralDictionaryHeadlessFixture.leaf_checked.identified.2.2.1 _ 2).mp
    obtain ⟨index, bound⟩ := index
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

/-- The actual raw executor succeeds; neither local package is its input. -/
theorem preparation_success :
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedAfter.base frames payload root = some tree := by
  have reconstructed : GeneralDictionaryPayloadReconstruction.reconstruct registry registry_checked frames payload root =
      some sourceTree := by
    apply GeneralDictionaryPayloadReconstruction.reconstruct_complete registry registry_checked frames sourceTree
    apply Evidence.node
    · exact ⟨leaf, by simp, rfl, rfl, no_children.symm⟩
    · intro child impossible; cases impossible
  apply (GeneralDictionaryPayloadPreparation.prepare_exact registry registry_checked mixedAfter.base frames
    payload root tree).mpr
  refine ⟨sourceTree, reconstructed, ?_⟩
  apply (GeneralDictionarySourceRecipe.prepare_exact registry registry_checked mixedAfter.base frames _ tree).mpr
  refine ⟨.node root 3 headless [], ?_, ?_⟩
  · simp only [sourceTree, GeneralDictionaryRecipeFidelity.recipe, List.map_nil]
    rw [GeneralDictionarySourceRecipe.localize, GeneralDictionaryHeadlessLocations.locate_inputs headless]
    rfl
  · apply (GeneralDictionaryHeadlessPreparation.prepare_node_exact registry registry_checked frames root 3
      headless [] tree).mpr
    exact ⟨result, lookup_success, [], rfl, rfl, rfl⟩

/-- Before representation, actual raw preparation cannot locate identity88. -/
theorem before_preparation_defers :
    GeneralDictionaryPayloadPreparation.prepare registry registry_checked mixedBefore.base frames payload root = none := by
  have absent : GeneralDictionaryHeadlessLocations.locate mixedBefore.base demand = none := by
    apply (GeneralDictionaryHeadlessLocations.locate_none_iff _ _).mpr
    intro available
    obtain ⟨slot, source⟩ := available.1 ⟨0, by decide⟩
    change (if slot.val = 0 then 10 else 77) = 88 at source
    split at source <;> contradiction
  have reconstructed : GeneralDictionaryPayloadReconstruction.reconstruct registry registry_checked frames payload root =
      some sourceTree := by
    apply GeneralDictionaryPayloadReconstruction.reconstruct_complete registry registry_checked frames sourceTree
    apply Evidence.node
    · exact ⟨leaf, by simp, rfl, rfl, no_children.symm⟩
    · intro child impossible; cases impossible
  simp only [GeneralDictionaryPayloadPreparation.prepare, reconstructed, Option.bind_some,
    sourceTree, GeneralDictionaryRecipeFidelity.recipe, List.map_nil,
    GeneralDictionarySourceRecipe.prepare, GeneralDictionarySourceRecipe.localize, absent]
  rfl

/-- The target type coordinate is new but its persistent source ID was reserved. -/
theorem new_reserved_slot :
    88 ∈ mixedBefore.reserved ∧ mixedAfter.base.source 2 = 88 ∧
      (∀ slot, mixedBefore.base.source slot ≠ 88) := by
  refine ⟨by simp, rfl, ?_⟩
  intro slot
  change (if slot.val = 0 then 10 else 77) ≠ 88
  split <;> decide

/-- Newly materialized ordinary obligations have a real full nominal joint model. -/
theorem recorded_model : GeneralNominalState.Models
    (GeneralDictionaryNominalRecording.record mixedAfter tree.items) mixedAssignment := by
  apply (GeneralDictionaryNominalRecording.record_models _ _ _).mpr
  refine ⟨mixed_nominal_nonvacuous.2, ?_⟩
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

/-- One source tree witnesses meaning at the newly represented source, not only
at old coordinates carried unchanged through the extension. -/
theorem fresh_source_evidence :
    Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry registry_checked frames mixedAssignment) sourceTree := by
  exact GeneralDictionarySlotEvidenceTransport.source_evidence registry registry_checked mixedAfter frames
    payload root tree preparation_success mixedAssignment recorded_model

/-- This is dictionary materialization, not completed candidate inspection. -/
theorem still_pending : GeneralNominalState.RootPending mixedAfter demand := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  rintro ⟨slot, source, known⟩
  obtain ⟨i, bound⟩ := slot
  change i < 3 at bound
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · change (10 : Nat) = 88 at source; cases source
  · change (77 : Nat) = 88 at source; cases source
  · change (CommonRoleRegularGraph.Node.unresolved ≠ CommonRoleRegularGraph.Node.unresolved ∨
        ∃ descriptor, (none : Option (GeneralNominalState.Descriptor 3)) = some descriptor) at known
    simp at known

end Yulang.GeneralDictionaryFreshSlotPreparationExamples
