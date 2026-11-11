import Yulang.GeneralDictionaryHeadlessPreparation
import Yulang.GeneralDictionaryPayloadOrder

/-!
# Fixed-recipe order invariance of complete headless preparation

Visible and where enumeration can change while the state, invocation-specific
frames, chosen keys, source locations and complete recipe stay fixed. Canonical
child emission is invariant, so the same ordered child-root check is used on
both sides. This says nothing about candidate search or final-state uniqueness.
-/
namespace Yulang.GeneralDictionaryHeadlessOrder
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralDictionaryHeadlessPreparation (Recipe prepare)
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralDictionaryBatchRecording (record)
open GeneralSourceState (State)
variable {state : State}

private theorem mapM_congr_mem {α β : Type} (inputs : List α) (first last : α → Option β)
    (same : ∀ input ∈ inputs, first input = last input) : inputs.mapM first = inputs.mapM last := by
  induction inputs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons, List.mapM_cons, same head (by simp), ih]
    intro input present
    exact same input (by simp [present])

/-- Full executable equality, including failure anywhere in the finite recipe.
No head vector, output vector or local success certificate is supplied. -/
theorem prepare_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (recipe : Recipe roles state) :
    prepare ⟨constructors, roles, first⟩ one frames recipe =
      prepare ⟨constructors, roles, last⟩ two frames recipe := by
  cases recipe with
  | node root key inputs children =>
    have mapped : children.mapM (prepare ⟨constructors, roles, first⟩ one frames) =
        children.mapM (prepare ⟨constructors, roles, last⟩ two frames) := by
      apply mapM_congr_mem
      intro child present
      exact prepare_reorders constructors roles first last one two order frames child
    rw [prepare, prepare,
      GeneralDictionaryHeadlessPlans.lookup_reorders constructors roles first last one two order,
      mapped]
termination_by sizeOf recipe

/-- The entire dictionary output, including all source occurrence identities,
is literally unchanged, whether preparation succeeds or defers. -/
theorem dictionary_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (recipe : Recipe roles state) :
    (prepare ⟨constructors, roles, first⟩ one frames recipe).map Prepared.dictionary =
      (prepare ⟨constructors, roles, last⟩ two frames recipe).map Prepared.dictionary := by
  rw [prepare_reorders constructors roles first last one two order]

/-- The recorded state and every generated equation are identical, not merely
observationally related, at this fixed source state and recipe. -/
theorem record_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (recipe : Recipe roles state) :
    (prepare ⟨constructors, roles, first⟩ one frames recipe).map (fun tree => record tree.items) =
      (prepare ⟨constructors, roles, last⟩ two frames recipe).map (fun tree => record tree.items) := by
  rw [prepare_reorders constructors roles first last one two order]

/-- Two successful runs return the same dependent tree, including located terms. -/
theorem prepared_equal (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (recipe : Recipe roles state)
    (before after : Prepared roles state)
    (left : prepare ⟨constructors, roles, first⟩ one frames recipe = some before)
    (right : prepare ⟨constructors, roles, last⟩ two frames recipe = some after) :
    before = after := by
  have same := prepare_reorders constructors roles first last one two order frames recipe
  rw [left, right] at same
  exact Option.some.inj same

/-- Source and erased-payload structural observations follow without adding a
permutation-invariance premise for an unrelated semantic instance relation. -/
theorem dictionary_equivalent (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (recipe : Recipe roles state)
    (before after : Prepared roles state)
    (left : prepare ⟨constructors, roles, first⟩ one frames recipe = some before)
    (right : prepare ⟨constructors, roles, last⟩ two frames recipe = some after) :
    DictionaryEquivalent before.dictionary after.dictionary ∧
      GeneralDictionaryPayloadOrder.Equivalent (erase before.dictionary) (erase after.dictionary) := by
  have same := prepared_equal constructors roles first last one two order frames recipe before after left right
  subst after
  exact ⟨.refl _, .refl _⟩

end Yulang.GeneralDictionaryHeadlessOrder
