import Yulang.GeneralDictionarySourceRecipe
import Yulang.GeneralDictionaryHeadlessSourceExamples

/-!
# Source-only producer recipes and missing-source deferral

The recipe supplies only occurrences, selected keys and child shape. Existing
source positions, variable heads and output terms are computed. Binder values
are constructed by the soundness theorem for each assignment.
The nonidentity source map and repeated distinct root output targets are retained.
Missing output locations defer; no fresh slot allocation is silently introduced.
-/
namespace Yulang.GeneralDictionarySourceRecipeExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionarySourceRecipe
open GeneralSourceDictionaries
open GeneralSourceState (Models Demand)
open GeneralDictionaryBatchRecording (record)
open GeneralDictionaryHeadlessSourceEvidence (Instance)

abbrev leafRecipe : Recipe roles := .node child 3 []
abbrev recipe : Recipe roles := .node root 2 [leafRecipe]

theorem leaf_localizes :
    localize state leafRecipe = some GeneralDictionaryHeadlessExamples.leafRecipe := by
  rw [localize, GeneralDictionaryHeadlessLocations.locate_inputs childHeadless]
  rfl

theorem tree_localizes :
    localize state recipe = some GeneralDictionaryHeadlessExamples.recipe := by
  rw [localize, GeneralDictionaryHeadlessLocations.locate_inputs rootHeadless]
  simp [leaf_localizes]

theorem tree_prepared :
    prepare registry registry_checked state (fun _ => frame) recipe = some tree :=
  (prepare_exact registry registry_checked state (fun _ => frame) recipe tree).mpr
    ⟨GeneralDictionaryHeadlessExamples.recipe, tree_localizes,
      GeneralDictionaryHeadlessExamples.tree_prepared⟩

/-- One fixed dictionary witness satisfies actual source evidence in every
joint model, without caller-supplied source-slot, head or output vectors. -/
theorem tree_uniform_source :
    ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
      ∀ model, Models (record tree.items) model →
        Evidence (Instance registry registry_checked (fun _ => frame) model) witness :=
  prepare_uniform_source registry registry_checked state (fun _ => frame) recipe tree tree_prepared

/-- The concrete all-int joint assignment witnesses nonvacuity. -/
theorem tree_source_nonvacuous :
    prepare registry registry_checked state (fun _ => frame) recipe = some tree ∧
      Models (record tree.items) assignment ∧
      ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
        Evidence (Instance registry registry_checked (fun _ => frame) assignment) witness := by
  obtain ⟨witness, readback, uniform⟩ := tree_uniform_source
  exact ⟨tree_prepared, tree_joint_model, witness, readback, uniform assignment tree_joint_model⟩

abbrev absentOutputDemand : Demand roles :=
  { rootDemand with
    outputs := [⟨0, 999⟩]
    declared := by
      intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨none, rfl⟩ }

abbrev absentOutputRoot : Occurrence roles := ⟨root.identity, absentOutputDemand⟩
abbrev absentOutputRecipe : Recipe roles := .node absentOutputRoot 2 [leafRecipe]

/-- A declared output name does not license inventing its absent source slot. -/
theorem absent_output_location_defers :
    GeneralDictionaryHeadlessLocations.locate state absentOutputDemand = none := rfl

theorem absent_output_localization_defers : localize state absentOutputRecipe = none := by
  rw [localize, absent_output_location_defers]
  rfl

theorem absent_output_preparation_defers :
    prepare registry registry_checked state (fun _ => frame) absentOutputRecipe = none := by
  rw [prepare, absent_output_localization_defers]
  rfl

/-- Computing locations does not weaken the complete actual-child check. -/
theorem omitted_child_defers :
    prepare registry registry_checked state (fun _ => frame) (.node root 2 []) = none := by
  have localized : localize state (.node root 2 []) =
      some (GeneralDictionaryHeadlessPreparation.Recipe.node root 2 rootHeadless []) := by
    rw [localize, GeneralDictionaryHeadlessLocations.locate_inputs rootHeadless]
    rfl
  rw [prepare, localized]
  exact GeneralDictionaryHeadlessExamples.omitted_child_defers

end Yulang.GeneralDictionarySourceRecipeExamples
