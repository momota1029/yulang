import Yulang.GeneralLiveCompoundPost316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralLiveCompoundPostSupport316
open GeneralLiveCompoundPost316 (raw known_iff)
open GeneralLiveCompoundLeafInstall316 (after models setValue patch_before after_model)
open GeneralLiveCompoundLeafProof316 (w binderId)
open GeneralLiveCompoundLeafHead316 (plan)
open GeneralMixedCompoundUpperSupport307 (identity lower)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalState (sources Known)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev basePool : List Nat := [0,1,2,3,4,lower,upper,identity,lo,hi]
abbrev oldPool := GeneralDictionaryCompoundPointModel238.pool

theorem base_supported : basePool ⊆ sources GeneralMixedCompoundUpperSnapshot307.snap := by decide +kernel

theorem extra_raw : ∀ n ∈ sources raw, n ∈ basePool ∨
    (n ∉ oldPool ∧ n ≠ GeneralMixedCompoundChildEquality307.mid ∧ n ≠ binderId) := by
  decide +kernel

theorem exact_leaf_support :
    GeneralNominalVersionedPacketFrame236.sources plan ⊆ oldPool ++ [binderId] := by
  decide +kernel

theorem patch_after (first : Assignment) (valid : Models after first) (key : Nat) (replacement : Ty)
    (outside : key ∉ oldPool) (binder : key ≠ binderId) : Models after (setValue first key replacement) := by
  obtain ⟨old,holds⟩ := (models _).mp valid
  apply (models _).mpr
  refine ⟨patch_before _ old _ _ outside,?_⟩
  apply (GeneralNominalVersionedPacketFrame236.holds_iff plan ?_).mp holds
  intro name present
  have ne : key ≠ name := by
    intro eq; subst name
    rcases List.mem_append.mp (exact_leaf_support present) with prev|new
    · exact outside prev
    · exact binder (List.mem_singleton.mp new)
  rw [setValue,ite_eq_right ne]

theorem identity_outside : identity ∉ oldPool := by decide +kernel
theorem identity_binder : identity ≠ binderId := by decide +kernel

end Yulang.GeneralLiveCompoundPostSupport316
