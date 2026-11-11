import Yulang.GeneralDictionaryHeadlessFixture
import Yulang.GeneralDictionaryHeadlessPreparation
import Yulang.GeneralDictionaryHeadExamples

/-!
# Headless checked lookup and whole-tree preparation regressions

The successful tree has a real producer where child and an explicit input-RHS
leaf. Neither the recipe nor the lookup call supplies a head or output vector.
Missing children, keys, and unsupported head captures defer materialization;
none of these failures is a candidate rejection judgment.
-/
namespace Yulang.GeneralDictionaryHeadlessExamples
open GeneralDictionaryHeadlessFixture
open GeneralDictionaryHeadlessPlans
open GeneralDictionaryHeadlessPreparation
open GeneralDictionaryVariableHeads (HeadlessInputs heads)
open GeneralSourceDictionaries
open GeneralSourceState (Models)
open GeneralDictionaryBatchRecording (record)

abbrev rootResult : Result state root := ⟨rootInputs, GeneralDictionaryHeadlessFixture.rootResult⟩
abbrev childResult : Result state child := ⟨childInputs, GeneralDictionaryHeadlessFixture.childResult⟩

theorem root_lookup : lookup registry registry_checked frame root 2 rootHeadless = some rootResult := by
  apply (lookup_build_exact registry registry_checked frame root 2 rootHeadless rootResult).mpr
  exact ⟨binderWrap, by simp, rfl, rfl, root_head_builds,
    GeneralDictionaryHeadlessFixture.root_lookup⟩

theorem child_lookup : lookup registry registry_checked frame child 3 childHeadless = some childResult := by
  apply (lookup_build_exact registry registry_checked frame child 3 childHeadless childResult).mpr
  exact ⟨leaf, by simp, rfl, rfl, child_head_builds,
    GeneralDictionaryHeadlessFixture.child_lookup⟩

abbrev leafRecipe : Recipe roles state := .node child 3 childHeadless []
abbrev recipe : Recipe roles state := .node root 2 rootHeadless [leafRecipe]
abbrev leafTree : GeneralDictionaryTransactions.Prepared roles state := .node child 3 childLocated []

theorem leaf_prepared : prepare registry registry_checked (fun _ => frame) leafRecipe = some leafTree := by
  apply (prepare_node_exact registry registry_checked (fun _ => frame) child 3 childHeadless [] leafTree).mpr
  exact ⟨childResult, child_lookup, [], rfl, rfl, rfl⟩

theorem tree_prepared : prepare registry registry_checked (fun _ => frame) recipe = some tree := by
  apply (prepare_node_exact registry registry_checked (fun _ => frame) root 2 rootHeadless [leafRecipe] tree).mpr
  refine ⟨rootResult, root_lookup, [leafTree], ?_, rfl, rfl⟩
  simp [leaf_prepared]

/-- The exact recipe succeeds, with a fixed readback witness for every model of
its one joint batch. `tree_joint_model` supplies a concrete model separately. -/
theorem prepared_uniform_completion :
    ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
      ∀ model, Models (record tree.items) model →
        Evidence (GeneralDictionaryVariableTransactions.SourceInstance registry registry_checked
          (fun _ => frame) (heads roles state) model) witness :=
  prepare_uniform registry registry_checked (fun _ => frame) recipe tree tree_prepared

theorem prepared_nonvacuous :
    prepare registry registry_checked (fun _ => frame) recipe = some tree ∧
      Models (record tree.items) assignment := ⟨tree_prepared, tree_joint_model⟩

/-- Dropping the actual producer child cannot manufacture a completed root. -/
theorem omitted_child_defers :
    prepare registry registry_checked (fun _ => frame) (.node root 2 rootHeadless []) = none := by
  rw [prepare, root_lookup]
  simp [rootResult, GeneralDictionaryHeadlessFixture.rootResult]

/-- A child key is not accepted as a root-role declaration. -/
theorem wrong_role_key_defers : lookup registry registry_checked frame root 3 rootHeadless = none := rfl

theorem absent_key_defers : lookup registry registry_checked frame root 99 rootHeadless = none := rfl

/-- The earlier nominal fixture is still outside variable-head materialization. -/
theorem nominal_root_still_defers :
    GeneralDictionaryVariableHeads.build
      GeneralDictionaryOutputBinderExamples.binderWrap
      GeneralDictionaryOutputBinderExamples.binderWrap_checked rfl
      GeneralDictionaryTerminalFixture.capture GeneralDictionaryHeadExamples.rootHeadless = none :=
  GeneralDictionaryHeadExamples.nominal_root_defers

abbrev unequalCapture : GeneralDeclarationDemands.Capture :=
  ⟨fun _ => (100, 101), fun _ => 102⟩
abbrev unequalFrame : GeneralDictionaryEmissionPlans.Frame roles :=
  { frame with capture := fun _ => unequalCapture }

/-- Existing endpoints can be distinct: that is deferred rather than treated
as an exact captured variable merely because a joint model equates their types. -/
theorem unequal_capture_defers :
    lookup registry registry_checked unequalFrame child 3 childHeadless = none := rfl

abbrev absentSecondCapture : GeneralDeclarationDemands.Capture :=
  ⟨fun binder => if binder = 2 then (999, 999) else (100, 100), fun _ => 102⟩
abbrev absentSecondFrame : GeneralDictionaryEmissionPlans.Frame roles :=
  { frame with capture := fun _ => absentSecondCapture }

/-- The first argument is supported, but the second source is absent. The
whole binary head must defer instead of keeping a partial head vector. -/
theorem absent_second_source_defers :
    lookup registry registry_checked absentSecondFrame root 2 rootHeadless = none := rfl

abbrev wrongChild : Occurrence roles := ⟨999, childDemand⟩
abbrev wrongLeafRecipe : Recipe roles state := .node wrongChild 3 childHeadless []
abbrev wrongLeafTree : GeneralDictionaryTransactions.Prepared roles state :=
  .node wrongChild 3 childLocated []
abbrev wrongChildResult : Result state wrongChild := ⟨childInputs, ⟨[], childLocated⟩⟩

private theorem wrong_child_lookup :
    lookup registry registry_checked frame wrongChild 3 childHeadless = some wrongChildResult := by
  apply (lookup_build_exact registry registry_checked frame wrongChild 3 childHeadless wrongChildResult).mpr
  refine ⟨leaf, by simp, rfl, rfl, child_head_builds, ?_⟩
  apply (GeneralDictionaryVariablePlans.lookup_exact registry registry_checked frame wrongChild 3
    childInputs wrongChildResult.plan).mpr
  refine ⟨leaf, by simp, rfl, rfl, child_build, ?_⟩
  have permuted := GeneralCanonicalChildOrder.canonicalEmit_perm wrongChild.identity leaf
    leaf_checked (frame.capture leaf.id) (frame.allocation leaf.id)
  have original : GeneralDeclarationDemands.emitAll wrongChild.identity leaf leaf_checked.signature
      (frame.capture leaf.id) (frame.allocation leaf.id) = [] := rfl
  rw [original] at permuted
  have canonical := List.Perm.nil_eq permuted
  unfold GeneralDictionaryEmissionPlans.children
  rw [← canonical]
  rfl

private theorem wrong_leaf_prepared :
    prepare registry registry_checked (fun _ => frame) wrongLeafRecipe = some wrongLeafTree := by
  apply (prepare_node_exact registry registry_checked (fun _ => frame) wrongChild 3 childHeadless []
    wrongLeafTree).mpr
  exact ⟨wrongChildResult, wrong_child_lookup, [], rfl, rfl, rfl⟩

/-- A well-formed leaf of the same role and demand is still not the root's
actual child occurrence. Full occurrence identity is retained. -/
theorem changed_child_identity_defers :
    prepare registry registry_checked (fun _ => frame)
      (.node root 2 rootHeadless [wrongLeafRecipe]) = none := by
  rw [prepare, root_lookup]
  simp only [List.mapM_cons, wrong_leaf_prepared, List.mapM_nil, Option.pure_def]
  have different : wrongLeafTree.root ≠ child := by
    intro same
    have identity := congrArg Occurrence.identity same
    cases identity
  simp [different]

/-- Source identity 100 localizes to slot 0, not slot 100. -/
theorem source_localization : state.source (0 : Fin state.slots) = 100 ∧
    GeneralDictionaryVariableHeads.compileAt state leaf capture 0 = some (.var 0) := ⟨rfl, rfl⟩

end Yulang.GeneralDictionaryHeadlessExamples
