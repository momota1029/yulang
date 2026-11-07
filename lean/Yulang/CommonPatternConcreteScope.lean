import Yulang.CommonPatternScopeRenaming
import Yulang.CommonPatternBindingAlignment
import Yulang.CommonPatternEnvironment

/-! A computable name permutation supplies the full semantic EnvInstances
premise, retaining arbitrary captured polymorphic outer bindings. -/

namespace Yulang.CommonPatternConcreteScope

open CommonPatternBindingAlignment (lookup reorder LookupEq)
open CommonPatternScopeRenaming (EnvInstances)
open CommonPatternEnvironment (NamedTypes semanticPrefix)
open Core.PresenceGeneration

def findName (name : Nat) : List (Nat × A) → Nat
  | [] => 0
  | (current, _) :: rest => if name = current then 0 else findName name rest + 1

theorem get_findName (name : Nat) (bindings : List (Nat × A))
    (found : lookup name bindings = some value) : bindings[findName name bindings]? = some (name, value) := by
  induction bindings with
  | nil => cases found
  | cons binding rest ih =>
      rcases binding with ⟨current, item⟩
      by_cases same : name = current
      · subst current
        have equal : item = value := by simpa [lookup] using found
        subst item
        simp [findName]
      · simpa [findName, same] using ih (by simpa [lookup, same] using found)

theorem lookup_of_get (bindings : List (Nat × A)) (distinct : (bindings.map Prod.fst).Nodup)
    (index : Nat) (found : bindings[index]? = some (name, value)) : lookup name bindings = some value := by
  induction bindings generalizing index with
  | nil => cases found
  | cons binding rest ih =>
      rcases binding with ⟨current, item⟩
      have apart := List.nodup_cons.mp distinct
      cases index with
      | zero =>
          have equal : (current, item) = (name, value) := by simpa using found
          cases equal
          simp [lookup]
      | succ index =>
          have tail : lookup name rest = some value := ih apart.2 index found
          have member := (CommonPatternBindingAlignment.lookup_isSome name rest).mp (by simp [tail])
          have different : name ≠ current := by intro same; subst name; exact apart.1 member
          simpa [lookup, different] using tail

def reindex (source target : List (Nat × A)) (index : Nat) : Nat :=
  if inside : index < source.length then findName (source[index]).1 target
  else target.length + (index - source.length)

/-- Named prefix entries are reindexed literally; all suffix indices still
refer to the same arbitrary outer binding, rather than a copied instance. -/
theorem mapped_prefix_reindex (source target : List (Nat × A))
    (distinct : (source.map Prod.fst).Nodup) (same : LookupEq source target)
    (map : Nat × A → B) (outer : List B) (index : Nat) :
    (source.map map ++ outer)[index]? = (target.map map ++ outer)[reindex source target index]? := by
  by_cases inside : index < source.length
  · have sourceGet := List.getElem?_eq_getElem inside
    have original := lookup_of_get source distinct index sourceGet
    have targetLookup := (same (source[index]).1).symm.trans original
    have targetGet := get_findName (source[index]).1 target targetLookup
    obtain ⟨targetBound, _⟩ := List.getElem?_eq_some_iff.mp targetGet
    simp only [reindex, dite_eq_left inside]
    rw [List.getElem?_append_left (by simpa using inside), List.getElem?_map, sourceGet,
      List.getElem?_append_left (by simpa using targetBound), List.getElem?_map, targetGet]
    rfl
  · rw [reindex, dite_eq_right inside]
    rw [List.getElem?_append_right (by simp only [List.length_map]; omega),
      List.getElem?_append_right (by simp only [List.length_map]; omega)]
    simp

theorem concrete_instances (source target : NamedTypes)
    (distinct : (source.map Prod.fst).Nodup) (same : LookupEq source target)
    (outer : List (Binding Common.model)) :
    EnvInstances Common.model (semanticPrefix source ++ outer) (semanticPrefix target ++ outer)
      (reindex source target) := by
  intro index result
  unfold BindingLookup semanticPrefix
  rw [mapped_prefix_reindex source target distinct same
    (fun binding => Binding.mono (Comp.pure Common.model binding.2)) outer index]

/-- The concrete name-based reorder supplies every source/target binding
instance correspondence required by expression reindexing, including an
arbitrary captured polymorphic suffix. No successful typing is assumed. -/
theorem reordered_instances (bindings : NamedTypes) (names : List Nat)
    (distinct : (bindings.map Prod.fst).Nodup)
    (retained : ∀ name ∈ bindings.map Prod.fst, name ∈ names)
    (outer : List (Binding Common.model)) :
    EnvInstances Common.model (semanticPrefix bindings ++ outer)
      (semanticPrefix (reorder names bindings) ++ outer) (reindex bindings (reorder names bindings)) :=
  concrete_instances bindings (reorder names bindings) distinct
    (fun name => (CommonPatternBindingAlignment.reorder_lookup_eq names bindings retained name).symm) outer

theorem typing_reordered_exact (expression : Inference.Expr) (bindings : NamedTypes) (names : List Nat)
    (distinct : (bindings.map Prod.fst).Nodup)
    (retained : ∀ name ∈ bindings.map Prod.fst, name ∈ names)
    (outer : List (Binding Common.model)) (result : Comp Common.model) :
    Typing Common.model (semanticPrefix bindings ++ outer) expression result ↔
      Typing Common.model (semanticPrefix (reorder names bindings) ++ outer)
        (CommonPatternScopeRenaming.renameExpr (reindex bindings (reorder names bindings)) expression) result :=
  CommonPatternScopeRenaming.typing_rename_exact expression Common.model _ _ _
    (reordered_instances bindings names distinct retained outer) result

/-- Concrete named-prefix reindexing, rather than an externally supplied
EnvInstances hypothesis, is used for both real finite generators. -/
theorem generation_reordered_exact (expression : Inference.Expr) (bindings : NamedTypes) (names : List Nat)
    (distinct : (bindings.map Prod.fst).Nodup)
    (retained : ∀ name ∈ bindings.map Prod.fst, name ∈ names)
    (outer : List (Binding Common.model))
    (sourceSlots : α → Comp Common.model) (targetSlots : β → Comp Common.model)
    (sourceEnv : SchemeEnv α) (targetEnv : SchemeEnv β)
    (sourceRelated : EnvRel Common.model sourceSlots sourceEnv (semanticPrefix bindings ++ outer))
    (targetRelated : EnvRel Common.model targetSlots targetEnv (semanticPrefix (reorder names bindings) ++ outer))
    (sourceResult : CompTerm α) (targetResult : CompTerm β)
    (resultSame : sourceResult.eval Common.model sourceSlots = targetResult.eval Common.model targetSlots) :
    (generate sourceEnv expression sourceResult).Holds Common.model sourceSlots ↔
      (generate targetEnv
        (CommonPatternScopeRenaming.renameExpr (reindex bindings (reorder names bindings)) expression)
        targetResult).Holds Common.model targetSlots :=
  CommonPatternScopeRenaming.generation_rename_exact expression Common.model _ _ _
    (reordered_instances bindings names distinct retained outer) sourceSlots targetSlots sourceEnv targetEnv
    sourceRelated targetRelated sourceResult targetResult resultSame

end Yulang.CommonPatternConcreteScope
