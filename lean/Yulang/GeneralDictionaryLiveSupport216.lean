import Yulang.GeneralDictionaryMergeCompletion216
import Yulang.GeneralDictionaryDefaultRawSupport213

/-! Reservation alone is not a semantic constraint. The model support omits
reserved identities, while retaining every base type/row and ordinary atom. -/
namespace Yulang.GeneralDictionaryLiveSupport216
open GeneralNominalState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension

abbrev live := GeneralDictionaryDefaultRawSupport213.sources

theorem models_same (state : State) (first last : Assignment)
    (same : ∀ n ∈ live state, first n = last n) (valid : Models state first) : Models state last :=
  (GeneralDictionaryDefaultRawSupport213.models_iff state same).mp valid

open GeneralDeclarations GeneralNominalAllocation GeneralNominalAllocationSupport
open GeneralDictionaryMergeSlots216 GeneralDictionaryMergeCompletion216

theorem propagation (separate : Separate state registry invocation declaration bindings pool)
    (supported : Endpoints bindings pool) (oldSupport : live state ⊆ pool)
    (previous : Assignment) (valid : Models state previous) (compatible : Compatible bindings previous) :
    Models (propagate state registry invocation declaration bindings)
      (patch state registry invocation declaration bindings previous) := by
  apply (propagate_models ..).mpr
  exact ⟨models_same state previous _ (fun n h => (preserves separate previous n (oldSupport h)).symm) valid,
    compatible_preserves separate supported previous compatible,merges_valid separate supported previous⟩

end Yulang.GeneralDictionaryLiveSupport216
