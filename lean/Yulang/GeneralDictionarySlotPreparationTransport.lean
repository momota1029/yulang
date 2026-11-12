import Yulang.GeneralDictionarySlotMaterializationTransport
import Yulang.GeneralDictionaryPayloadPreparation

/-!
# Finite source-dictionary preparation survives certified slot transport

The checked registry, invocation frames and source recipe/raw payload stay fixed.
Successful packages are reindexed, retaining all source occurrences and selected
keys. No old failure preservation or cross-context computed-frame equality is
asserted; target snapshot construction and candidate readiness remain separate.
-/
namespace Yulang.GeneralDictionarySlotPreparationTransport
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryNominalSlotTransport (Transport)
open GeneralDictionarySlotLocalizationTransport (headlessInputs headless_locate)
open GeneralDictionarySlotMaterializationTransport (located headlessResult headless_lookup_success)
open GeneralDictionaryTransactions (Prepared Frames)
open GeneralDictionaryHeadlessPreparation (Recipe)
variable {before after : GeneralNominalState.State} {roles : Roles.RoleDecls}

/-- Exact local renaming, with untouched global root and selected key. -/
def recipe (transport : Transport before after) : Recipe roles before.base → Recipe roles after.base
  | .node root key inputs children =>
      .node root key (headlessInputs transport inputs) (children.map (recipe transport))
termination_by value => sizeOf value

def prepared (transport : Transport before after) : Prepared roles before.base → Prepared roles after.base
  | .node root key value children =>
      .node root key (located transport value) (children.map (prepared transport))
termination_by value => sizeOf value

theorem prepared_root (transport : Transport before after) (tree : Prepared roles before.base) :
    (prepared transport tree).root = tree.root := by cases tree; simp only [prepared, Prepared.root]

theorem prepared_dictionary (transport : Transport before after) (tree : Prepared roles before.base) :
    (prepared transport tree).dictionary = tree.dictionary := by
  cases tree with
  | node root key value children =>
    simp only [prepared, Prepared.dictionary, GeneralDictionaryTransactions.dictionaries_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro child member
    exact prepared_dictionary transport child
termination_by sizeOf tree

private theorem mapM_success {α β γ : Type} (first : α → Option β) (last : α → Option γ)
    (rename : β → γ) (xs : List α) (ys : List β)
    (found : xs.mapM first = some ys)
    (each : ∀ x ∈ xs, ∀ y, first x = some y → last x = some (rename y)) :
    xs.mapM last = some (ys.map rename) := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at found; subst ys; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at found ⊢
    obtain ⟨value, one, rest⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨values, more, equal⟩ := Option.bind_eq_some_iff.mp rest
    cases equal
    rw [each head (by simp) value one]
    have rest := ih values more (fun x member y found => each x (by simp [member]) y found)
    rw [rest]
    rfl

/-- Every finite child's success is transported, and the canonical child-root
check is identical because local reindexing does not change occurrences. -/
theorem headless_prepare_success (transport : Transport before after) (registry : Registry)
    (checked : Checked registry) (frames : Frames registry.roles)
    (old : Recipe registry.roles before.base) (tree : Prepared registry.roles before.base)
    (success : GeneralDictionaryHeadlessPreparation.prepare registry checked frames old = some tree) :
    GeneralDictionaryHeadlessPreparation.prepare registry checked frames (recipe transport old) =
      some (prepared transport tree) := by
  cases old with
  | node root key inputs children =>
    obtain ⟨result, found, trees, childrenFound, complete, rfl⟩ :=
      (GeneralDictionaryHeadlessPreparation.prepare_node_exact registry checked frames root key inputs children tree).mp success
    rw [recipe, prepared]
    apply (GeneralDictionaryHeadlessPreparation.prepare_node_exact registry checked frames root key
      (headlessInputs transport inputs) (children.map (recipe transport)) _).mpr
    refine ⟨headlessResult transport result, headless_lookup_success transport registry checked
      (frames root) root key inputs result found, trees.map (prepared transport), ?_, ?_, rfl⟩
    · rw [List.mapM_map]
      apply mapM_success _ _ (prepared transport) children trees childrenFound
      intro child member result childFound
      exact headless_prepare_success transport registry checked frames child result childFound
    · simpa only [List.map_map, Function.comp_def, prepared_root, headlessResult,
        GeneralDictionarySlotMaterializationTransport.planResult] using complete
termination_by sizeOf old

/-- Source-only localization returns the exact renamed finite recipe. -/
theorem source_localize_success (transport : Transport before after)
    (source : GeneralDictionarySourceRecipe.Recipe roles) (old : Recipe roles before.base)
    (success : GeneralDictionarySourceRecipe.localize before.base source = some old) :
    GeneralDictionarySourceRecipe.localize after.base source = some (recipe transport old) := by
  cases source with
  | node root key children =>
    rw [GeneralDictionarySourceRecipe.localize] at success ⊢
    obtain ⟨inputs, found, rest⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨localized, childrenFound, equal⟩ := Option.bind_eq_some_iff.mp rest
    cases equal
    rw [headless_locate transport root.demand inputs]
    have childrenMoved := mapM_success (GeneralDictionarySourceRecipe.localize before.base)
      (GeneralDictionarySourceRecipe.localize after.base) (recipe transport) children localized childrenFound
      (fun child member result childFound => source_localize_success transport child result childFound)
    rw [childrenMoved, recipe]
    rfl
termination_by sizeOf source

/-- Complete existing source-recipe preparation succeeds with every local term
renamed. No locations, head terms or output terms are supplied to this executor. -/
theorem source_prepare_success (transport : Transport before after) (registry : Registry)
    (checked : Checked registry) (frames : Frames registry.roles)
    (source : GeneralDictionarySourceRecipe.Recipe registry.roles) (tree : Prepared registry.roles before.base)
    (success : GeneralDictionarySourceRecipe.prepare registry checked before.base frames source = some tree) :
    GeneralDictionarySourceRecipe.prepare registry checked after.base frames source = some (prepared transport tree) := by
  obtain ⟨old, localized, built⟩ :=
    (GeneralDictionarySourceRecipe.prepare_exact registry checked before.base frames source tree).mp success
  exact (GeneralDictionarySourceRecipe.prepare_exact registry checked after.base frames source _).mpr
    ⟨recipe transport old, source_localize_success transport source old localized,
      headless_prepare_success transport registry checked frames old tree built⟩

/-- Raw selected-key payload preparation is likewise monotone in certified slot
representation, with the invocation frames explicitly fixed. -/
theorem payload_prepare_success (transport : Transport before after) (registry : Registry)
    (checked : Checked registry) (frames : Frames registry.roles)
    (raw : GeneralDictionaryReadback.Payload) (root : Occurrence registry.roles)
    (tree : Prepared registry.roles before.base)
    (success : GeneralDictionaryPayloadPreparation.prepare registry checked before.base frames raw root = some tree) :
    GeneralDictionaryPayloadPreparation.prepare registry checked after.base frames raw root = some (prepared transport tree) := by
  obtain ⟨source, reconstructed, built⟩ :=
    (GeneralDictionaryPayloadPreparation.prepare_exact registry checked before.base frames raw root tree).mp success
  exact (GeneralDictionaryPayloadPreparation.prepare_exact registry checked after.base frames raw root _).mpr
    ⟨source, reconstructed, source_prepare_success transport registry checked frames _ tree built⟩

end Yulang.GeneralDictionarySlotPreparationTransport
