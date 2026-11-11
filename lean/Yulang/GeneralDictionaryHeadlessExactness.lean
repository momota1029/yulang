import Yulang.GeneralDictionaryHeadlessPreparation

/-!
# Independent whole-tree materialization exactness

The recursive judgment refers only to actual declaration/head/RHS provenance,
retained locations and complete canonical children. It contains neither local
lookup success nor recursive execution success. Exactness is for this partial
variable materializer, not the language's full candidate solver.
-/
namespace Yulang.GeneralDictionaryHeadlessExactness
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryHeadlessPlans (MaterializesPlan)
open GeneralDictionaryHeadlessPreparation (Recipe prepare prepare_node_exact)
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralDictionaryVariableHeads (HeadlessInputs)
open GeneralSourceState (State)
variable {state : State}

/-- Positionwise relation over the complete finite child lists. -/
inductive Pairs {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Pairs relation [] []
  | cons {first rest value tail} : relation first value → Pairs relation rest tail →
      Pairs relation (first :: rest) (value :: tail)

/-- Actual node provenance and every canonical child obligation are retained. -/
inductive Materializes (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) :
    Recipe registry.roles state → Prepared registry.roles state → Prop where
  | node {root : Occurrence registry.roles} {key : Nat}
      (inputs : HeadlessInputs state root.demand)
      (recipes : List (Recipe registry.roles state))
      (result : GeneralDictionaryHeadlessPlans.Result state root)
      (trees : List (Prepared registry.roles state))
      (nodeMeaning : MaterializesPlan registry checked (frames root) root key inputs result)
      (children : Pairs (Materializes registry checked frames) recipes trees)
      (complete : trees.map Prepared.root = result.plan.children) :
      Materializes registry checked frames (.node root key inputs recipes)
        (.node root key result.plan.located trees)

private theorem mapM_forall₂ {α β : Type} (f : α → Option β)
    (inputs : List α) (outputs : List β) :
    inputs.mapM f = some outputs ↔ Pairs (fun input output => f input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil =>
    cases outputs with
    | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
    | cons value tail =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | cons first rest ih =>
    cases outputs with
    | nil =>
      rw [List.mapM_cons]
      constructor
      · intro impossible
        obtain ⟨value, _, rest⟩ := Option.bind_eq_some_iff.mp impossible
        obtain ⟨tail, _, impossible⟩ := Option.bind_eq_some_iff.mp rest
        cases impossible
      · intro impossible; cases impossible
    | cons value tail =>
      rw [List.mapM_cons]
      constructor
      · intro success
        obtain ⟨mapped, found, restSuccess⟩ := Option.bind_eq_some_iff.mp success
        obtain ⟨mappedTail, tailFound, equal⟩ := Option.bind_eq_some_iff.mp restSuccess
        cases equal
        exact .cons found ((ih _).mp tailFound)
      · intro related
        cases related with
        | cons head tail =>
          exact Option.bind_eq_some_iff.mpr ⟨_, head,
            Option.bind_eq_some_iff.mpr ⟨_, (ih _).mpr tail, rfl⟩⟩

private theorem forall₂_mono_mem {α β : Type} {R S : α → β → Prop}
    {inputs : List α} {outputs : List β} (related : Pairs R inputs outputs)
    (step : ∀ input ∈ inputs, ∀ output, R input output → S input output) :
    Pairs S inputs outputs := by
  induction related with
  | nil => exact .nil
  | @cons first rest value tail head related ih =>
    exact .cons (step first (by simp) value head)
      (ih fun input present output proof => step input (by simp [present]) output proof)

/-- All finite recursive obligations, not only the root node, follow from execution. -/
theorem prepare_materializes (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles state)
    (tree : Prepared registry.roles state)
    (success : prepare registry checked frames recipe = some tree) :
    Materializes registry checked frames recipe tree := by
  cases recipe with
  | node root key inputs recipes =>
    obtain ⟨result, found, trees, children, complete, rfl⟩ :=
      (prepare_node_exact registry checked frames root key inputs recipes tree).mp success
    refine .node inputs recipes result trees
      ((GeneralDictionaryHeadlessPlans.lookup_exact registry checked (frames root) root key inputs result).mp found)
      ?_ complete
    apply forall₂_mono_mem ((mapM_forall₂ _ recipes trees).mp children)
    intro recipe present tree computed
    exact prepare_materializes registry checked frames recipe tree computed
termination_by sizeOf recipe

/-- Completeness is restricted precisely by the independent supported-term judgment. -/
theorem materializes_prepare (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles state)
    (tree : Prepared registry.roles state)
    (materialized : Materializes registry checked frames recipe tree) :
    prepare registry checked frames recipe = some tree := by
  cases materialized with
  | node inputs recipes result trees nodeMeaning children complete =>
    apply (prepare_node_exact registry checked frames _ _ inputs recipes _).mpr
    refine ⟨result, (GeneralDictionaryHeadlessPlans.lookup_exact registry checked _ _ _ inputs result).mpr nodeMeaning,
      trees, ?_, complete, rfl⟩
    apply (mapM_forall₂ _ recipes trees).mpr
    apply forall₂_mono_mem children
    intro recipe present tree proof
    exact materializes_prepare registry checked frames recipe tree proof
termination_by sizeOf recipe

/-- Exact whole-tree iff, including complete ordered occurrence identity. -/
theorem prepare_exact (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles state)
    (tree : Prepared registry.roles state) :
    prepare registry checked frames recipe = some tree ↔
      Materializes registry checked frames recipe tree :=
  ⟨prepare_materializes registry checked frames recipe tree,
    materializes_prepare registry checked frames recipe tree⟩

/-- Partial materialization is functional at the complete Prepared-tree level. -/
theorem materializes_functional (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles state)
    (first last : Prepared registry.roles state)
    (one : Materializes registry checked frames recipe first)
    (two : Materializes registry checked frames recipe last) : first = last := by
  have left := materializes_prepare registry checked frames recipe first one
  have right := materializes_prepare registry checked frames recipe last two
  exact Option.some.inj (left.symm.trans right)

/-- Failure means no tree in this supported materialization judgment, not a
language rejection or lack of a model for the source program. -/
theorem prepare_none_exact (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles state) :
    prepare registry checked frames recipe = none ↔
      ∀ tree, ¬ Materializes registry checked frames recipe tree := by
  constructor
  · intro absent tree materialized
    have found := materializes_prepare registry checked frames recipe tree materialized
    rw [absent] at found
    cases found
  · intro absent
    cases found : prepare registry checked frames recipe with
    | none => rfl
    | some tree =>
        exact False.elim (absent tree (prepare_materializes registry checked frames recipe tree found))

end Yulang.GeneralDictionaryHeadlessExactness
