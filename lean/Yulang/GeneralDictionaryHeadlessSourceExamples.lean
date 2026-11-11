import Yulang.GeneralDictionaryHeadlessSourceEvidence
import Yulang.GeneralDictionaryHeadlessExamples

/-!
# Source evidence is sound, but broader than exact-identity compilation

The successful producer tree has a concrete joint model and one source-evidence
witness valid in every joint model. Conversely, a compatible captured interval
with distinct source identities can satisfy the independent source relation
while this deliberately partial compiler defers. Neither result establishes
candidate selection or a successful general head match.
-/
namespace Yulang.GeneralDictionaryHeadlessSourceExamples
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralSourceDictionaries
open GeneralSourceState (Models)
open GeneralDictionaryBatchRecording (record)
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryHeadlessExamples (recipe tree_prepared unequalCapture unequalFrame)
open GeneralDictionaryHeadlessSourceEvidence (Instance prepare_uniform_source)
open GeneralDictionaryVariableRealization (Realizes)

/-- One source witness is fixed independently of the joint assignment. -/
theorem tree_uniform_source :
    ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
      ∀ model, Models (record tree.items) model →
        Evidence (Instance registry registry_checked (fun _ => frame) model) witness :=
  prepare_uniform_source registry registry_checked (fun _ => frame) recipe tree tree_prepared

/-- The universal evidence statement is not made true by an empty model set. -/
theorem tree_source_nonvacuous :
    Models (record tree.items) assignment ∧
      ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
        Evidence (Instance registry registry_checked (fun _ => frame) assignment) witness := by
  obtain ⟨witness, readback, uniform⟩ := tree_uniform_source
  exact ⟨tree_joint_model, witness, readback, uniform assignment tree_joint_model⟩

abbrev binderValues : Nat → Common.Ty := fun _ => .base .int

/-- Distinct endpoint identities need not denote distinct types. -/
theorem unequal_capture_realizes : Realizes leaf unequalCapture assignment binderValues := by
  constructor
  · intro binder _
    exact ⟨Common.subtype_refl _, Common.subtype_refl _⟩
  · intro binder _
    exact Common.equivalent_refl _

private theorem unequal_leaf_children :
    GeneralDictionaryEmissionPlans.children unequalFrame child leaf leaf_checked = [] := by
  have permuted := GeneralCanonicalChildOrder.canonicalEmit_perm child.identity leaf
    leaf_checked (unequalFrame.capture leaf.id) (unequalFrame.allocation leaf.id)
  have original : emitAll child.identity leaf leaf_checked.signature
      (unequalFrame.capture leaf.id) (unequalFrame.allocation leaf.id) = [] := rfl
  rw [original] at permuted
  have canonical := List.Perm.nil_eq permuted
  unfold GeneralDictionaryEmissionPlans.children
  rw [← canonical]
  rfl

/-- Actual declaration membership, captured binder values, positional head and
explicit RHS provenance satisfy the independent source instance relation. -/
theorem unequal_source_instance :
    Instance registry registry_checked (fun _ => unequalFrame) assignment child 3 [] := by
  refine ⟨leaf, by simp, rfl, rfl, unequal_leaf_children.symm, binderValues,
    unequal_capture_realizes, ?_, ?_⟩
  · intro index
    obtain ⟨index, bound⟩ := index
    change index < 1 at bound
    have same : index = 0 := by omega
    subst index
    exact ⟨.var 0, 0, rfl, rfl, Common.subtype_refl _, Common.subtype_refl _⟩
  · intro index
    obtain ⟨index, bound⟩ := index
    change index < 1 at bound
    have same : index = 0 := by omega
    subst index
    exact ⟨leafEquation, 0, .explicit leafEquation (by simp) rfl, rfl,
      Common.equivalent_refl _⟩

/-- Sound compilation has no converse for compatible unequal captured intervals.
This is deferred materialization, not semantic rejection. -/
theorem source_instance_while_lookup_defers :
    Instance registry registry_checked (fun _ => unequalFrame) assignment child 3 [] ∧
      GeneralDictionaryHeadlessPlans.lookup registry registry_checked unequalFrame child 3 childHeadless = none :=
  ⟨unequal_source_instance, GeneralDictionaryHeadlessExamples.unequal_capture_defers⟩

theorem unequal_leaf_preparation_defers :
    GeneralDictionaryHeadlessPreparation.prepare registry registry_checked (fun _ => unequalFrame)
      GeneralDictionaryHeadlessExamples.leafRecipe = none := by
  rw [GeneralDictionaryHeadlessPreparation.prepare,
    GeneralDictionaryHeadlessExamples.unequal_capture_defers]
  rfl

end Yulang.GeneralDictionaryHeadlessSourceExamples
