import Yulang.GeneralDictionaryVariableTransactions

/-!
# Whole-tree preparation without caller-supplied output vectors

Keys, frames, head terms, source locations and recipe shape remain inputs.
Preparation computes every output package and checks the complete ordered child
occurrences, including argument intervals and repeated output targets. Failure
is deferred materialization, not semantic rejection or a candidate decision.
-/
namespace Yulang.GeneralDictionaryVariablePreparation
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryBinderLocations (Inputs)
open GeneralDictionaryVariablePlans
open GeneralDictionaryVariableTransactions (Built)
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralSourceState (State Demand Output)

variable {roles : Roles.RoleDecls} {state : State}

private instance outputDecidableEq : DecidableEq Output := by
  intro first last
  cases first with | mk fn ft =>
    cases last with | mk ln lt =>
      exact decidable_of_iff (fn = ln ∧ ft = lt) (by simp)

private instance demandDecidableEq : DecidableEq (Demand roles) := by
  intro first last
  cases first with | mk fr fa fo fp =>
    cases last with | mk lr la lo lp =>
      by_cases sameRole : fr = lr
      · subst lr
        letI : Decidable (fa = la) := decidable_of_iff (∀ index, fa index = la index)
          ⟨fun pointwise => funext pointwise, fun same index => congrFun same index⟩
        exact decidable_of_iff (fa = la ∧ fo = lo) (by simp)
      · exact isFalse (by intro same; cases same; exact sameRole rfl)

private instance occurrenceDecidableEq : DecidableEq (Occurrence roles) := by
  intro first last
  cases first with | mk fi fd =>
    cases last with | mk li ld =>
      exact decidable_of_iff (fi = li ∧ fd = ld) (by simp)

/-- No constructor field contains a computed output vector. -/
inductive Recipe (roles : Roles.RoleDecls) (state : State) where
  | node (root : Occurrence roles) (key : Nat) (inputs : Inputs state root.demand)
      (children : List (Recipe roles state))

def Recipe.root : Recipe roles state → Occurrence roles
  | .node root _ _ _ => root

def prepare (registry : Registry) (checked : Checked registry) (frames : Frames registry.roles) :
    Recipe registry.roles state → Option (Prepared registry.roles state)
  | .node root key inputs children => do
      let result ← lookup registry checked (frames root) root key inputs
      let prepared ← children.mapM (prepare registry checked frames)
      if prepared.map Prepared.root = result.children then
        some (.node root key result.located prepared)
      else none
termination_by recipe => sizeOf recipe

/-- Recursive head-only certificate; it contains no output or lookup premise. -/
inductive Heads (registry : Registry) (frames : Frames registry.roles)
    (heads : HeadInstances registry.roles state) : Recipe registry.roles state → Prop where
  | node {root : Occurrence registry.roles} {key : Nat} (inputs : Inputs state root.demand)
      (children : List (Recipe registry.roles state))
      (head : ∀ declaration ∈ registry.declarations,
        declaration.id = key → declaration.role = root.demand.role →
          heads root declaration ((frames root).capture declaration.id) inputs.head)
      (childrenHeads : ∀ child ∈ children, Heads registry frames heads child) :
      Heads registry frames heads (.node root key inputs children)

/-- Exact executable node contract, retaining the original key and occurrence. -/
theorem prepare_node_exact (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (root : Occurrence registry.roles) (key : Nat)
    (inputs : Inputs state root.demand) (children : List (Recipe registry.roles state))
    (tree : Prepared registry.roles state) :
    prepare registry checked frames (.node root key inputs children) = some tree ↔
      ∃ result, lookup registry checked (frames root) root key inputs = some result ∧
      ∃ prepared, children.mapM (prepare registry checked frames) = some prepared ∧
        prepared.map Prepared.root = result.children ∧
        tree = .node root key result.located prepared := by
  rw [prepare]
  change ((lookup registry checked (frames root) root key inputs).bind fun result =>
    (children.mapM (prepare registry checked frames)).bind fun prepared =>
      if prepared.map Prepared.root = result.children then
        some (Prepared.node root key result.located prepared) else none) = some tree ↔ _
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨result, found, prepared, childrenFound, success⟩
    split at success
    next complete =>
      cases success
      exact ⟨result, found, prepared, childrenFound, complete, rfl⟩
    next incomplete => cases success
  · rintro ⟨result, found, prepared, childrenFound, complete, rfl⟩
    exact ⟨result, found, prepared, childrenFound, by simp [complete]⟩

theorem prepare_root (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles state)
    (tree : Prepared registry.roles state) (success : prepare registry checked frames recipe = some tree) :
    tree.root = recipe.root := by
  cases recipe with
  | node root key inputs children =>
    obtain ⟨result, _, prepared, _, _, rfl⟩ :=
      (prepare_node_exact registry checked frames root key inputs children tree).mp success
    rfl

private theorem mapM_member {α β : Type} (f : α → Option β) (inputs : List α) (outputs : List β)
    (success : inputs.mapM f = some outputs) (output : β) (member : output ∈ outputs) :
    ∃ input ∈ inputs, f input = some output := by
  induction inputs generalizing outputs with
  | nil => simp at success; subst outputs; cases member
  | cons first rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨value, found, restSuccess⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨tail, tailFound, equal⟩ := Option.bind_eq_some_iff.mp restSuccess
    cases equal
    rcases List.mem_cons.mp member with same | later
    · subst output; exact ⟨first, by simp, found⟩
    · obtain ⟨input, present, mapped⟩ := ih tail tailFound later
      exact ⟨input, by simp [present], mapped⟩

/-- Every successful executable preparation is Built, given only head meaning. -/
theorem prepare_built (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (recipe : Recipe registry.roles state) (headOnly : Heads registry frames heads recipe)
    (tree : Prepared registry.roles state) (success : prepare registry checked frames recipe = some tree) :
    Built registry checked frames heads tree := by
  induction headOnly generalizing tree with
  | @node root key inputs children head childrenHeads ih =>
    obtain ⟨result, found, prepared, childrenFound, complete, rfl⟩ :=
      (prepare_node_exact registry checked frames root key inputs children tree).mp success
    refine Built.node inputs result prepared found head complete ?_
    intro child member
    obtain ⟨recipe, present, computed⟩ :=
      mapM_member (prepare registry checked frames) children prepared childrenFound child member
    exact ih recipe present child computed


/-- The executable whole-tree result gives one fixed source witness for every
model of the single recorded batch. Only head meaning remains a certificate;
all output vectors, canonical-child checks and storage evidence are computed. -/
theorem prepare_uniform (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (recipe : Recipe registry.roles state) (headOnly : Heads registry frames heads recipe)
    (tree : Prepared registry.roles state) (success : prepare registry checked frames recipe = some tree) :
    ∃ witness, GeneralSourceDictionaries.Readback recipe.root (erase tree.dictionary) witness ∧
      ∀ assignment, GeneralSourceState.Models (GeneralDictionaryBatchRecording.record tree.items) assignment →
        GeneralSourceDictionaries.Evidence
          (GeneralDictionaryVariableTransactions.SourceInstance registry checked frames heads assignment) witness := by
  have uniform := GeneralDictionaryVariableTransactions.transaction_uniform registry checked frames heads tree
    (prepare_built registry checked frames heads recipe headOnly tree success)
  rwa [prepare_root registry checked frames recipe tree success] at uniform

end Yulang.GeneralDictionaryVariablePreparation
