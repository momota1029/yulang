import Yulang.GeneralDictionaryMixedMerge216

/-! Exact finite-support merge amalgamation criterion. With binding endpoints
protected, the protected aggregate values already agreeing with current extrema
is necessary and sufficient for a merge model preserving that support. -/
namespace Yulang.GeneralDictionaryMergeCriterion216
open GeneralDeclarations GeneralNominalAllocation GeneralNominalAllocationSupport
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension CommonNominalFullCarrier
open GeneralDictionaryMergeSlots216
open GeneralDictionaryMixedMerge216 (Overlap)

theorem active_declared (i : Fin (active declaration bindings).length) :
    (active declaration bindings)[i] ∈ declaration.inputNames ∧
      ∀ pair, occurrences bindings (active declaration bindings)[i] ≠ [pair] := by
  have member := List.mem_filter.mp (List.getElem_mem (l := active declaration bindings) i.isLt)
  refine ⟨member.1,?_⟩
  intro pair equal
  have length := member.2
  change ((occurrences bindings (active declaration bindings)[i]).length != 1) = true at length
  rw [equal] at length
  contradiction

theorem necessary (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat)
    (supported : Endpoints bindings pool) (previous extended : Assignment)
    (kept : ∀ n ∈ pool, extended n = previous n)
    (recorded : PresenceNormalForm.All model extended (merges state registry invocation declaration bindings)) :
    Overlap state registry invocation declaration bindings pool previous := by
  have exactValues (i : Fin (active declaration bindings).length) :=
    (GeneralNominalMergeResidual178.merges_iff_extrema ..).mp recorded _ (active_declared i).1
      (occurrences bindings (active declaration bindings)[i]) rfl (active_declared i).2
  have lowerSame (i : Fin (active declaration bindings).length) :=
    type_eval_same (first := extended) (last := previous) (lower (occurrences bindings (active declaration bindings)[i]))
      (fun n member => kept n (lower_sources _ (occurrences_endpoints supported _) member))
  have upperSame (i : Fin (active declaration bindings).length) :=
    type_eval_same (first := extended) (last := previous) (upper (occurrences bindings (active declaration bindings)[i]))
      (fun n member => kept n (upper_sources _ (occurrences_endpoints supported _) member))
  constructor
  · intro i member
    have value := (exactValues i).1
    rw [GeneralDictionaryOwnedMerges216.capture_slots state registry invocation declaration bindings _ (active_declared i).2] at value
    change Equivalent (extended (names state registry invocation declaration bindings 0 i)).1 _ at value
    rw [kept _ member,lowerSame i] at value
    exact value
  · intro i member
    have value := (exactValues i).2
    rw [GeneralDictionaryOwnedMerges216.capture_slots state registry invocation declaration bindings _ (active_declared i).2] at value
    change Equivalent (extended (names state registry invocation declaration bindings 1 i)).1 _ at value
    rw [kept _ member,upperSame i] at value
    exact value

theorem completion_iff (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (bindings : Bindings) (pool : List Nat)
    (supported : Endpoints bindings pool) (previous : Assignment) :
    (∃ extended, (∀ n ∈ pool, extended n = previous n) ∧
      PresenceNormalForm.All model extended (merges state registry invocation declaration bindings)) ↔
    Overlap state registry invocation declaration bindings pool previous := by
  constructor
  · rintro ⟨extended,kept,valid⟩
    exact necessary state registry invocation declaration bindings pool supported previous extended kept valid
  · intro overlap
    exact ⟨GeneralDictionaryMixedMerge216.patch state registry invocation declaration bindings pool previous,
      GeneralDictionaryMixedMerge216.preserves state registry invocation declaration bindings pool previous,
      GeneralDictionaryMixedMerge216.merges_valid overlap supported⟩

end Yulang.GeneralDictionaryMergeCriterion216
