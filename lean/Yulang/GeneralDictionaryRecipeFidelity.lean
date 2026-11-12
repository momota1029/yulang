import Yulang.GeneralDictionarySourceRecipe

/-!
# Exact source-tree fidelity of dictionary preparation

Localization and variable materialization preserve the complete input source
tree, not merely its root or key count. These theorems expose the raw payload
link needed when a recipe was reconstructed from an existing dictionary.
-/
namespace Yulang.GeneralDictionaryRecipeFidelity
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralSourceState (State)

/-- Forget only materialization inputs, retaining every source occurrence. -/
def headlessTree : GeneralDictionaryHeadlessPreparation.Recipe roles state → Dictionary roles
  | .node root key _ children => .node root key (children.map headlessTree)
termination_by recipe => sizeOf recipe

def sourceTree : GeneralDictionarySourceRecipe.Recipe roles → Dictionary roles
  | .node root key children => .node root key (children.map sourceTree)
termination_by recipe => sizeOf recipe

/-- Repackage an already source-indexed tree without inventing any occurrence. -/
def recipe : Dictionary roles → GeneralDictionarySourceRecipe.Recipe roles
  | .node root key children => .node root key (children.map recipe)
termination_by tree => sizeOf tree

private theorem mapM_fidelity {α β γ : Type} (f : α → Option β) (g : β → γ) (h : α → γ)
    (inputs : List α) (outputs : List β) (success : inputs.mapM f = some outputs)
    (preserved : ∀ input ∈ inputs, ∀ output, f input = some output → g output = h input) :
    outputs.map g = inputs.map h := by
  induction inputs generalizing outputs with
  | nil => simp at success; subst outputs; rfl
  | cons first rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨value, found, tail⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨values, built, same⟩ := Option.bind_eq_some_iff.mp tail
    cases same
    simp only [List.map_cons, preserved first (by simp) value found,
      ih values built (fun input member output computed => preserved input (by simp [member]) output computed)]

/-- No source occurrence, key or child multiplicity changes during localization. -/
theorem localize_tree (state : State) (input : GeneralDictionarySourceRecipe.Recipe roles)
    (output : GeneralDictionaryHeadlessPreparation.Recipe roles state)
    (success : GeneralDictionarySourceRecipe.localize state input = some output) :
    headlessTree output = sourceTree input := by
  cases input with
  | node root key children =>
    rw [GeneralDictionarySourceRecipe.localize] at success
    obtain ⟨inputs, _, rest⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨localized, built, same⟩ := Option.bind_eq_some_iff.mp rest
    cases same
    have childTrees := mapM_fidelity (GeneralDictionarySourceRecipe.localize state) headlessTree sourceTree
      children localized built (fun child _ output computed => localize_tree state child output computed)
    simp only [headlessTree, sourceTree, childTrees]
termination_by sizeOf input

/-- Variable head/output preparation retains the full source dictionary exactly. -/
theorem headless_prepare_tree (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles)
    (input : GeneralDictionaryHeadlessPreparation.Recipe registry.roles state) (output : Prepared registry.roles state)
    (success : GeneralDictionaryHeadlessPreparation.prepare registry checked frames input = some output) :
    output.dictionary = headlessTree input := by
  cases input with
  | node root key inputs children =>
    obtain ⟨result, _, trees, built, _, rfl⟩ :=
      (GeneralDictionaryHeadlessPreparation.prepare_node_exact registry checked frames root key inputs children output).mp success
    have childTrees := mapM_fidelity (GeneralDictionaryHeadlessPreparation.prepare registry checked frames)
      Prepared.dictionary headlessTree children trees built
      (fun child _ output computed => headless_prepare_tree registry checked frames child output computed)
    simp only [Prepared.dictionary, GeneralDictionaryTransactions.dictionaries_map, headlessTree, childTrees]
termination_by sizeOf input

/-- Successful source preparation has exact tree fidelity, regardless of which
joint assignments satisfy the recorded equations. -/
theorem source_prepare_tree (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (input : GeneralDictionarySourceRecipe.Recipe registry.roles)
    (output : Prepared registry.roles state)
    (success : GeneralDictionarySourceRecipe.prepare registry checked state frames input = some output) :
    output.dictionary = sourceTree input := by
  obtain ⟨localized, located, prepared⟩ :=
    (GeneralDictionarySourceRecipe.prepare_exact registry checked state frames input output).mp success
  exact (headless_prepare_tree registry checked frames localized output prepared).trans
    (localize_tree state input localized located)

/-- The adapter is a lossless change of carrier. -/
theorem recipe_tree (tree : Dictionary roles) : sourceTree (recipe tree) = tree := by
  cases tree with
  | node root key children =>
    simp only [recipe, sourceTree, List.map_map]
    congr 1
    calc
      _ = children.map id := List.map_congr_left (fun child _ => recipe_tree child)
      _ = children := List.map_id children
termination_by sizeOf tree

theorem recipe_root (tree : Dictionary roles) : (recipe tree).root = tree.root := by
  cases tree <;> simp only [recipe, GeneralDictionarySourceRecipe.Recipe.root, Dictionary.root]

/-- A reconstructed source dictionary cannot be replaced by a different
selected-key payload during the subsequent materialization phase. -/
theorem prepare_recipe_tree (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (input : Dictionary registry.roles) (output : Prepared registry.roles state)
    (success : GeneralDictionarySourceRecipe.prepare registry checked state frames (recipe input) = some output) :
    output.dictionary = input :=
  (source_prepare_tree registry checked state frames (recipe input) output success).trans (recipe_tree input)

end Yulang.GeneralDictionaryRecipeFidelity
