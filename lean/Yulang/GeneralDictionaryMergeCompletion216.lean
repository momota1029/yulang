import Yulang.GeneralDictionaryMergeSlots216

/-! A simultaneous merge completion with an explicit protected-support premise.
This premise is not asserted for arbitrary historical allocations. -/
namespace Yulang.GeneralDictionaryMergeCompletion216
open GeneralDeclarations GeneralNominalAllocation GeneralNominalAllocationSupport
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension CommonNominalFullCarrier
open GeneralDictionaryMergeSlots216

def Separate (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) : Prop :=
  ∀ i, names state registry invocation declaration bindings 0 i ∉ pool ∧
    names state registry invocation declaration bindings 1 i ∉ pool

theorem preserves (separate : Separate state registry invocation declaration bindings pool)
    (previous : Assignment) (name : Nat) (member : name ∈ pool) :
    patch state registry invocation declaration bindings previous name = previous name := by
  apply patch_outside
  · intro i equal; exact (separate i).1 (equal ▸ member)
  · intro i equal; exact (separate i).2 (equal ▸ member)

theorem lower_preserves (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (previous : Assignment) (name : Nat) :
    (lower (occurrences bindings name)).eval model (patch state registry invocation declaration bindings previous) =
      (lower (occurrences bindings name)).eval model previous := by
  apply type_eval_same
  intro n member
  exact preserves separate previous n (lower_sources _ (occurrences_endpoints supported name) member)

theorem upper_preserves (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (previous : Assignment) (name : Nat) :
    (upper (occurrences bindings name)).eval model (patch state registry invocation declaration bindings previous) =
      (upper (occurrences bindings name)).eval model previous := by
  apply type_eval_same
  intro n member
  exact preserves separate previous n (upper_sources _ (occurrences_endpoints supported name) member)

theorem active_member (declared : name ∈ declaration.inputNames)
    (nonsingle : ∀ pair, occurrences bindings name ≠ [pair]) : name ∈ active declaration bindings := by
  apply List.mem_filter.mpr
  refine ⟨declared,?_⟩
  simp only [bne_iff_ne,ne_eq]
  intro length
  cases observed : occurrences bindings name with
  | nil => simp [observed] at length
  | cons first rest =>
    cases rest with
    | nil => exact nonsingle first observed
    | cons second tail => simp [observed] at length

theorem extrema (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (previous : Assignment) :
    GeneralNominalMergeResidual178.CaptureExtrema state registry invocation declaration bindings
      (patch state registry invocation declaration bindings previous) := by
  intro name declared bounds observed nonsingle
  have activeName := active_member declared (fun pair equal => nonsingle pair (observed.symm.trans equal))
  obtain ⟨i,bound,found⟩ := List.mem_iff_getElem.mp activeName
  have foundFin : (active declaration bindings)[(⟨i,bound⟩ : Fin (active declaration bindings).length)] = name := found
  have low := patch_lower state registry invocation declaration bindings previous ⟨i,bound⟩
  have high := patch_upper state registry invocation declaration bindings previous ⟨i,bound⟩
  simp only [names,values,foundFin,Bool.false_eq_true,↓reduceIte] at low
  simp only [names,values,foundFin,↓reduceIte] at high
  have captured : (capture state registry invocation declaration.id bindings).inputs name =
      (slot state registry invocation declaration 0 name,slot state registry invocation declaration 1 name) := by
    simp only [capture]
    split
    · exact False.elim (nonsingle _ (observed.symm.trans (by assumption)))
    · rfl
  rw [captured]
  change Equivalent ((patch state registry invocation declaration bindings previous) (slot state registry invocation declaration 0 name)).1 _ ∧
    Equivalent ((patch state registry invocation declaration bindings previous) (slot state registry invocation declaration 1 name)).1 _
  rw [low,high,← observed,lower_preserves separate supported previous name,upper_preserves separate supported previous name]
  exact ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩⟩

theorem merges_valid (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (previous : Assignment) :
    PresenceNormalForm.All model (patch state registry invocation declaration bindings previous)
      (merges state registry invocation declaration bindings) :=
  (GeneralNominalMergeResidual178.merges_iff_extrema ..).mpr (extrema separate supported previous)


theorem compatible_preserves (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (previous : Assignment)
    (valid : Compatible bindings previous) :
    Compatible bindings (patch state registry invocation declaration bindings previous) := by
  intro first one last two same
  rw [preserves separate previous _ (supported first one).1,
    preserves separate previous _ (supported last two).2]
  exact valid first one last two same

/-- Complete propagation while preserving all protected assignments. This is a
usable constructor only after separation from the actual live support is proved. -/
theorem propagation (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool)
    (oldSupport : GeneralNominalState.sources state ⊆ pool) (previous : Assignment)
    (valid : GeneralNominalState.Models state previous) (compatible : Compatible bindings previous) :
    GeneralNominalState.Models (propagate state registry invocation declaration bindings)
      (patch state registry invocation declaration bindings previous) := by
  apply (propagate_models ..).mpr
  exact ⟨source_models_same state (fun n h => (preserves separate previous n (oldSupport h)).symm) valid,
    compatible_preserves separate supported previous compatible,merges_valid separate supported previous⟩

/-- Preserve an additional semantic predicate by its finite support, rather than
silently replacing its satisfying assignment with another branch witness. -/
theorem joint (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (previous : Assignment) (predicate : Assignment → Prop)
    (depends : ∀ first last, (∀ n ∈ pool, first n = last n) → predicate first → predicate last)
    (valid : predicate previous) :
    predicate (patch state registry invocation declaration bindings previous) ∧
    PresenceNormalForm.All model (patch state registry invocation declaration bindings previous)
      (merges state registry invocation declaration bindings) := by
  exact ⟨depends previous _ (fun n h => (preserves separate previous n h).symm) valid,
    merges_valid separate supported previous⟩

end Yulang.GeneralDictionaryMergeCompletion216
