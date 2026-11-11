import Yulang.GeneralDictionaryHeadlessLocations
import Yulang.GeneralDictionaryHeadlessSourceEvidence
import Yulang.GeneralDictionaryHeadlessOrder

/-!
# Source-only finite dictionary recipes

Only actual occurrence, selected key and recursive child shape are supplied.
Existing source-slot positions, variable heads and output RHS terms are computed.
Compatible binder values are constructed by soundness for each assignment.
No fresh identity or allocation policy is chosen.
Missing source locations and unsupported materialization remain deferred.
-/
namespace Yulang.GeneralDictionarySourceRecipe
open GeneralDeclarations GeneralSourceDictionaries
open GeneralSourceState (State)
open GeneralDictionaryTransactions (Frames Prepared)

inductive Recipe (roles : Roles.RoleDecls) where
  | node (root : Occurrence roles) (key : Nat) (children : List (Recipe roles))

def Recipe.root : Recipe roles → Occurrence roles
  | .node root _ _ => root

def localize (state : State) : Recipe roles → Option (GeneralDictionaryHeadlessPreparation.Recipe roles state)
  | .node root key children => do
      let inputs ← GeneralDictionaryHeadlessLocations.locate state root.demand
      let localized ← children.mapM (localize state)
      pure (.node root key inputs localized)
termination_by recipe => sizeOf recipe

def prepare (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles) : Option (Prepared registry.roles state) :=
  (localize state recipe).bind (GeneralDictionaryHeadlessPreparation.prepare registry checked frames)

/-- Localization retains the source occurrence, not only the role demand. -/
theorem localize_root (state : State) (recipe : Recipe roles)
    (localized : GeneralDictionaryHeadlessPreparation.Recipe roles state)
    (success : localize state recipe = some localized) : localized.root = recipe.root := by
  cases recipe with
  | node root key children =>
    rw [localize] at success
    obtain ⟨inputs, _, rest⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨localizedChildren, _, same⟩ := Option.bind_eq_some_iff.mp rest
    cases same
    rfl

/-- Successful source-only preparation has an exact location-computing stage
and the already checked whole head/output materialization stage. -/
theorem prepare_exact (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles)
    (tree : Prepared registry.roles state) :
    prepare registry checked state frames recipe = some tree ↔
      ∃ localized, localize state recipe = some localized ∧
        GeneralDictionaryHeadlessPreparation.prepare registry checked frames localized = some tree :=
  Option.bind_eq_some_iff

/-- The dictionary witness is fixed across all joint models. The caller gives
no position, head, output or realization certificate. Captures and selected keys
remain supplied, and the source demand's readiness is not established here. -/
theorem prepare_uniform_source (registry : Registry) (checked : Checked registry) (state : State)
    (frames : Frames registry.roles) (recipe : Recipe registry.roles)
    (tree : Prepared registry.roles state)
    (success : prepare registry checked state frames recipe = some tree) :
    ∃ witness, Readback recipe.root (erase tree.dictionary) witness ∧
      ∀ assignment, GeneralSourceState.Models (GeneralDictionaryBatchRecording.record tree.items) assignment →
        Evidence (GeneralDictionaryHeadlessSourceEvidence.Instance registry checked frames assignment) witness := by
  obtain ⟨localized, located, built⟩ := (prepare_exact registry checked state frames recipe tree).mp success
  have uniform := GeneralDictionaryHeadlessSourceEvidence.prepare_uniform_source registry checked frames localized tree built
  rwa [localize_root state recipe localized located] at uniform

/-- Source localization is registry-independent. At fixed frames and source
recipe, allowed visible/where order preserves every successful or failed result. -/
theorem prepare_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (state : State) (frames : Frames roles) (recipe : Recipe roles) :
    prepare ⟨constructors, roles, first⟩ one state frames recipe =
      prepare ⟨constructors, roles, last⟩ two state frames recipe := by
  unfold prepare
  cases found : localize state recipe with
  | none => rfl
  | some localized =>
      simp only [Option.bind_some]
      exact GeneralDictionaryHeadlessOrder.prepare_reorders constructors roles first last one two order frames localized

end Yulang.GeneralDictionarySourceRecipe
