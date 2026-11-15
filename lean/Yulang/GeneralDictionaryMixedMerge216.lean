import Yulang.GeneralDictionaryOwnedMerges216

/-! Keep protected aggregate values, assign only unprotected ones, and require
semantic extrema agreement exactly on the overlap. This is a constructive
finite-support amalgamation criterion, not a global reachability invariant. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedMerge216
open GeneralDeclarations GeneralNominalAllocation CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension GeneralNominalAllocationSupport
open GeneralDictionaryMergeSlots216

noncomputable def keptValues (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) (previous : Assignment)
    (purpose : Nat) (upperSide : Bool) (i : Fin (active declaration bindings).length) : Ty :=
  if names state registry invocation declaration bindings purpose i ∈ pool then
    (previous (names state registry invocation declaration bindings purpose i)).1
  else values previous declaration bindings upperSide i

noncomputable def patch (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) (previous : Assignment) : Assignment :=
  assign (assign previous (names state registry invocation declaration bindings 0)
    (keptValues state registry invocation declaration bindings pool previous 0 false))
    (names state registry invocation declaration bindings 1)
    (keptValues state registry invocation declaration bindings pool previous 1 true)

theorem coherent (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) (previous : Assignment)
    (purpose : Nat) (upperSide : Bool) :
    ∀ i j, names state registry invocation declaration bindings purpose i = names state registry invocation declaration bindings purpose j →
      keptValues state registry invocation declaration bindings pool previous purpose upperSide i =
        keptValues state registry invocation declaration bindings pool previous purpose upperSide j := by
  intro i j equal
  have same := GeneralDictionaryMergeSlots216.coherent state registry invocation declaration bindings previous purpose upperSide i j equal
  simp only [keptValues,equal,same]

theorem preserves (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) (previous : Assignment)
    (name : Nat) (member : name ∈ pool) : patch state registry invocation declaration bindings pool previous name = previous name := by
  have low : assign previous (names state registry invocation declaration bindings 0)
      (keptValues state registry invocation declaration bindings pool previous 0 false) name = previous name := by
    apply assign_preserves
    intro i equal
    simp only [keptValues,equal,member,↓reduceIte]
  unfold patch
  rw [assign_preserves _ _ _ (by
    intro i equal
    simp only [keptValues,equal,member,↓reduceIte,low])]
  exact low

def Overlap (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) (previous : Assignment) : Prop :=
  (∀ i, names state registry invocation declaration bindings 0 i ∈ pool →
    Equivalent (previous (names state registry invocation declaration bindings 0 i)).1
      (values previous declaration bindings false i)) ∧
  (∀ i, names state registry invocation declaration bindings 1 i ∈ pool →
    Equivalent (previous (names state registry invocation declaration bindings 1 i)).1
      (values previous declaration bindings true i))

theorem kept_equivalent (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat) (previous : Assignment)
    (purpose : Nat) (upperSide : Bool) (i : Fin (active declaration bindings).length)
    (compatible : names state registry invocation declaration bindings purpose i ∈ pool →
      Equivalent (previous (names state registry invocation declaration bindings purpose i)).1
        (values previous declaration bindings upperSide i)) :
    Equivalent (keptValues state registry invocation declaration bindings pool previous purpose upperSide i)
      (values previous declaration bindings upperSide i) := by
  unfold keptValues
  split
  · exact compatible (by assumption)
  · exact ⟨subtype_refl _,subtype_refl _⟩

theorem lower_value (overlap : Overlap state registry invocation declaration bindings pool previous)
    (i : Fin (active declaration bindings).length) :
    Equivalent ((patch state registry invocation declaration bindings pool previous)
      (names state registry invocation declaration bindings 0 i)).1 (values previous declaration bindings false i) := by
  unfold patch
  rw [assign_outside _ _ _ (fun j => (sides_separate state registry invocation declaration bindings i j).symm)]
  rw [assign_value _ _ _ (coherent state registry invocation declaration bindings pool previous 0 false)]
  exact kept_equivalent state registry invocation declaration bindings pool previous 0 false i (overlap.1 i)

theorem upper_value (overlap : Overlap state registry invocation declaration bindings pool previous)
    (i : Fin (active declaration bindings).length) :
    Equivalent ((patch state registry invocation declaration bindings pool previous)
      (names state registry invocation declaration bindings 1 i)).1 (values previous declaration bindings true i) := by
  unfold patch
  rw [assign_value _ _ _ (coherent state registry invocation declaration bindings pool previous 1 true)]
  exact kept_equivalent state registry invocation declaration bindings pool previous 1 true i (overlap.2 i)


theorem extrema (overlap : Overlap state registry invocation declaration bindings pool previous)
    (supported : Endpoints bindings pool) :
    GeneralNominalMergeResidual178.CaptureExtrema state registry invocation declaration bindings
      (patch state registry invocation declaration bindings pool previous) := by
  intro name declared bounds observed nonsingle
  have current : ∀ pair, occurrences bindings name ≠ [pair] :=
    fun pair equal => nonsingle pair (observed.symm.trans equal)
  obtain ⟨i,bound,found⟩ := List.mem_iff_getElem.mp (GeneralDictionaryMergeCompletion216.active_member declared current)
  have foundFin : (active declaration bindings)[(⟨i,bound⟩ : Fin (active declaration bindings).length)] = name := found
  have low := lower_value overlap ⟨i,bound⟩
  have high := upper_value overlap ⟨i,bound⟩
  simp only [names,values,foundFin,Bool.false_eq_true,↓reduceIte] at low
  simp only [names,values,foundFin,↓reduceIte] at high
  have lowerSame := type_eval_same (first := patch state registry invocation declaration bindings pool previous)
    (last := previous) (lower (occurrences bindings name))
    (fun n member => preserves state registry invocation declaration bindings pool previous n
      (lower_sources _ (occurrences_endpoints supported name) member))
  have upperSame := type_eval_same (first := patch state registry invocation declaration bindings pool previous)
    (last := previous) (upper (occurrences bindings name))
    (fun n member => preserves state registry invocation declaration bindings pool previous n
      (upper_sources _ (occurrences_endpoints supported name) member))
  rw [GeneralDictionaryOwnedMerges216.capture_slots state registry invocation declaration bindings name current,
    ← observed,lowerSame,upperSame]
  exact ⟨low,high⟩

theorem merges_valid (overlap : Overlap state registry invocation declaration bindings pool previous)
    (supported : Endpoints bindings pool) :
    PresenceNormalForm.All model (patch state registry invocation declaration bindings pool previous)
      (merges state registry invocation declaration bindings) :=
  (GeneralNominalMergeResidual178.merges_iff_extrema ..).mpr (extrema overlap supported)

theorem joint (overlap : Overlap state registry invocation declaration bindings pool previous)
    (supported : Endpoints bindings pool) (predicate : Assignment → Prop)
    (depends : ∀ first last, (∀ n ∈ pool, first n = last n) → predicate first → predicate last)
    (valid : predicate previous) :
    predicate (patch state registry invocation declaration bindings pool previous) ∧
    PresenceNormalForm.All model (patch state registry invocation declaration bindings pool previous)
      (merges state registry invocation declaration bindings) := by
  exact ⟨depends previous _ (fun n h => (preserves state registry invocation declaration bindings pool previous n h).symm) valid,
    merges_valid overlap supported⟩

end Yulang.GeneralDictionaryMixedMerge216
