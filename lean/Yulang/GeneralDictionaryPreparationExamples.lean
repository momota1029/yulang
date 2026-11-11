import Yulang.GeneralDictionaryVariablePreparation
import Yulang.GeneralDictionaryTerminalFixture

/-! # Executable preparation retains exact canonical children and output meaning -/
namespace Yulang.GeneralDictionaryPreparationExamples
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryTerminalFixture
open GeneralDictionaryVariablePreparation
open GeneralDictionaryVariablePlans (HeadInstances)
open GeneralDictionaryTransactions (Prepared)
open GeneralDictionaryOutputBinderExamples (binderWrap)

abbrev childRecipe : Recipe registry.roles state := .node child 3 childInputs []
abbrev recipe : Recipe registry.roles state := .node root 2 rootInputs [childRecipe]

theorem child_prepares : prepare registry registry_checked (fun _ => frame) childRecipe =
    some (.node child 3 childLocated []) := by
  apply (prepare_node_exact registry registry_checked (fun _ => frame) child 3 childInputs [] _).mpr
  exact ⟨childResult, child_lookup, [], rfl, rfl, rfl⟩

theorem tree_prepares : prepare registry registry_checked (fun _ => frame) recipe = some tree := by
  apply (prepare_node_exact registry registry_checked (fun _ => frame) root 2 rootInputs [childRecipe] _).mpr
  refine ⟨rootResult, root_lookup, [.node child 3 childLocated []], ?_, rfl, rfl⟩
  simp [child_prepares]

theorem missing_child_defers :
    prepare registry registry_checked (fun _ => frame) (.node root 2 rootInputs []) = none := by
  simp [prepare, root_lookup, rootResult]

theorem extra_child_defers :
    prepare registry registry_checked (fun _ => frame)
      (.node root 2 rootInputs [childRecipe, childRecipe]) = none := by
  rw [prepare]
  simp [root_lookup, child_prepares, rootResult]

abbrev wrongChild : Occurrence registry.roles := ⟨999, childDemand⟩

private theorem wrong_child_lookup :
    GeneralDictionaryVariablePlans.lookup registry registry_checked frame wrongChild 3 childInputs =
      some (⟨[], childLocated⟩ : GeneralDictionaryVariablePlans.Result state wrongChild) := by
  apply (GeneralDictionaryVariablePlans.lookup_exact registry registry_checked frame wrongChild 3 childInputs _).mpr
  refine ⟨leaf, by simp, rfl, rfl, child_build, ?_⟩
  have permuted := GeneralCanonicalChildOrder.canonicalEmit_perm wrongChild.identity leaf
    leaf_checked (frame.capture leaf.id) (frame.allocation leaf.id)
  have empty : GeneralDeclarationDemands.emitAll wrongChild.identity leaf leaf_checked.signature
      (frame.capture leaf.id) (frame.allocation leaf.id) = [] := rfl
  rw [empty] at permuted
  unfold GeneralDictionaryEmissionPlans.children
  rw [← List.Perm.nil_eq permuted]
  rfl

private theorem wrong_child_prepares :
    prepare registry registry_checked (fun _ => frame) (.node wrongChild 3 childInputs []) =
      some (.node wrongChild 3 childLocated []) := by
  apply (prepare_node_exact registry registry_checked (fun _ => frame) wrongChild 3 childInputs [] _).mpr
  exact ⟨⟨[], childLocated⟩, wrong_child_lookup, [], rfl, rfl, rfl⟩

/-- Same demand is insufficient: the full emitted occurrence identity is checked. -/
theorem wrong_identity_defers :
    prepare registry registry_checked (fun _ => frame)
      (.node root 2 rootInputs [.node wrongChild 3 childInputs []]) = none := by
  have childList : ([Recipe.node wrongChild 3 childInputs []].mapM
      (prepare registry registry_checked (fun _ => frame))) =
      some [Prepared.node wrongChild 3 childLocated []] := by
    rw [List.mapM_cons, wrong_child_prepares]
    rfl
  rw [prepare]
  change ((GeneralDictionaryVariablePlans.lookup registry registry_checked frame root 2 rootInputs).bind
    fun result => ([Recipe.node wrongChild 3 childInputs []].mapM
      (prepare registry registry_checked (fun _ => frame))).bind fun prepared =>
      if prepared.map Prepared.root = result.children then
        some (Prepared.node root 2 result.located prepared) else none) = none
  rw [root_lookup]
  simp only [Option.bind_some, childList]
  have different : [wrongChild] ≠ [child] := by
    intro same
    have identity := congrArg (fun xs => xs.map Occurrence.identity) same
    contradiction
  exact ite_eq_right different

theorem missing_key_defers :
    prepare registry registry_checked (fun _ => frame) (.node root 99 rootInputs [childRecipe]) = none := by
  rw [prepare]
  rfl

abbrev unequalFrame : GeneralDictionaryEmissionPlans.Frame registry.roles :=
  { frame with capture := fun _ => ⟨fun _ => (0, 1), fun _ => 2⟩ }

theorem unequal_leaf_defers :
    prepare registry registry_checked (fun _ => unequalFrame) childRecipe = none := by
  rw [prepare]
  rfl

/-- The only remaining certificate supplies the two declaration heads. -/
theorem recipe_heads (heads : HeadInstances registry.roles state)
    (rootHead : heads root binderWrap capture rootInputs.head)
    (childHead : heads child leaf capture childInputs.head) :
    Heads registry (fun _ => frame) heads recipe := by
  refine Heads.node (registry := registry) (frames := fun _ => frame) (heads := heads)
    (root := root) (key := 2) rootInputs [childRecipe] ?_ ?_
  · intro declaration present identity _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact rootHead
    · cases identity
  · intro child member
    have same := List.mem_singleton.mp member
    subst child
    refine Heads.node (registry := registry) (frames := fun _ => frame) (heads := heads)
      (root := GeneralDictionaryTerminalFixture.child) (key := 3) childInputs [] ?_ ?_
    · intro declaration present identity _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      · cases identity
      · exact childHead
    · intro child absent; cases absent

theorem prepared_built (heads : HeadInstances registry.roles state)
    (rootHead : heads root binderWrap capture rootInputs.head)
    (childHead : heads child leaf capture childInputs.head) :
    GeneralDictionaryVariableTransactions.Built registry registry_checked (fun _ => frame) heads tree :=
  prepare_built registry registry_checked (fun _ => frame) heads recipe
    (recipe_heads heads rootHead childHead) tree tree_prepares

end Yulang.GeneralDictionaryPreparationExamples
