import Yulang.CommonPatternMatchPaths

/-! Returned bindings are a permutation of the canonical interface only
when the raw name list has no duplicates and exactly the source name set.
This prevents canonical projection from discarding extra/hidden payloads. -/

namespace Yulang.CommonPatternReturnedNames

open CommonPatternBindingAlignment (lookup reorder)
open CaseValues (Bindings Value)
open EvaluationTrace
open CasePatterns (Pattern)

def Valid (names : List Nat) (returned : List (Nat × A)) : Prop :=
  (returned.map Prod.fst).Nodup ∧ ∀ name, name ∈ returned.map Prod.fst ↔ name ∈ names

def check (names : List Nat) (returned : List (Nat × A)) : Bool :=
  decide (returned.map Prod.fst).Nodup && CasePatterns.sameNames (returned.map Prod.fst) names

theorem check_exact (names : List Nat) (returned : List (Nat × A)) : check names returned = true ↔ Valid names returned := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, CasePatterns.sameNames_exact, Valid]

theorem lookup_of_mem (returned : List (Nat × A)) (distinct : (returned.map Prod.fst).Nodup)
    (member : (name, value) ∈ returned) : lookup name returned = some value := by
  induction returned with
  | nil => cases member
  | cons binding rest ih =>
      rcases binding with ⟨current, item⟩
      have apart := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | tail
      · cases same; simp [lookup]
      · have nameInRest : name ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(name, value), tail, rfl⟩
        have different : name ≠ current := by intro same; exact apart.1 (same ▸ nameInRest)
        simpa only [lookup, different, ↓reduceIte] using ih apart.2 tail

theorem entries_nodup (returned : List (Nat × A)) (distinct : (returned.map Prod.fst).Nodup) : returned.Nodup := by
  induction returned with
  | nil => exact .nil
  | cons binding rest ih =>
      have apart := List.nodup_cons.mp distinct
      exact List.nodup_cons.mpr ⟨fun member => apart.1 (List.mem_map_of_mem member), ih apart.2⟩

/-- Every raw pair and literal payload is retained, with multiplicity one;
no hidden duplicate or extra name can disappear through reordering. -/
theorem reorder_perm (names : List Nat) (distinct : names.Nodup) (returned : List (Nat × A))
    (valid : Valid names returned) : (reorder names returned).Perm returned := by
  have canonicalNames := CommonPatternBindingAlignment.reorder_names names returned (fun name member => (valid.2 name).mpr member)
  apply (List.perm_ext_iff_of_nodup (entries_nodup _ (canonicalNames.symm ▸ distinct)) (entries_nodup returned valid.1)).mpr
  intro binding
  constructor
  · intro member
    exact CommonPatternBindingAlignment.reorder_mem names returned member
  · intro member
    have named : binding.1 ∈ returned.map Prod.fst := List.mem_map_of_mem member
    have selected := (valid.2 binding.1).mp named
    have original : lookup binding.1 returned = some binding.2 := lookup_of_mem returned valid.1 member
    have found : lookup binding.1 (reorder names returned) = some binding.2 := by
      rw [CommonPatternBindingAlignment.lookup_reorder, ite_eq_left selected, original]
    exact CommonPatternBindingAlignment.lookup_mem _ _ found

theorem actual_return_valid (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (valid : PatternBindingChecks.NamesValid pattern) (environment : Bindings F)
    (value : Value F) (returned : Bindings F)
    (matched : (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some returned)) :
    Valid pattern.names returned := by
  have path := CommonPatternMatchPaths.run_binding_path floatCheck defaultEval pattern environment value returned matched
  exact ⟨valid.path_nodup path, path.names valid⟩

theorem actual_return_perm (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (pattern : Pattern F D)
    (valid : PatternBindingChecks.NamesValid pattern) (environment : Bindings F)
    (value : Value F) (returned : Bindings F)
    (matched : (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some returned)) :
    (reorder pattern.names returned).Perm returned :=
  reorder_perm pattern.names (CommonPatternMatchPaths.source_names_nodup pattern valid) returned
    (actual_return_valid floatCheck defaultEval pattern valid environment value returned matched)

end Yulang.CommonPatternReturnedNames
