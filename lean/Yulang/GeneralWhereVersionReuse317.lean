import Yulang.GeneralWhereVersionFrontier317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 35000000
namespace Yulang.GeneralWhereVersionReuse317
open GeneralWhereVersionRootReport317 (plan same)
open GeneralWhereVersionCase317 (lower upper expr)
open GeneralWhereVersionBase317 (loSlot hiSlot source_lo source_hi)
open GeneralWhereVersionSnapshot317 (snap)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralVersionedEndpointAddress315 (atCell)

theorem exact_addresses :
    atCell plan .lower otherChild.id 0 expr = lower ∧
    atCell plan .upper otherChild.id 0 expr = upper :=
  ⟨(GeneralWhereVersionRecompile317.address same _ _ _ _).symm,
    (GeneralWhereVersionRecompile317.address same _ _ _ _).symm⟩

theorem exact_slots :
    GeneralDictionaryBinderLocations.sourceSlot snap.base (atCell plan .lower otherChild.id 0 expr) = some loSlot ∧
    GeneralDictionaryBinderLocations.sourceSlot snap.base (atCell plan .upper otherChild.id 0 expr) = some hiSlot := by
  rw [exact_addresses.1,exact_addresses.2]
  exact ⟨(GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr source_lo,
    (GeneralDictionaryBinderLocations.sourceSlot_exact ..).mpr source_hi⟩

/-- An unmodified re-read needs the existing endpoint slots. The strict
first-install freshness premise cannot hold at these exact addresses. -/
theorem both_present :
    atCell plan .lower otherChild.id 0 expr ∈ GeneralNominalState.sources snap ∧
    atCell plan .upper otherChild.id 0 expr ∈ GeneralNominalState.sources snap := by
  rw [exact_addresses.1,exact_addresses.2]
  exact ⟨source_lo ▸ GeneralNominalAllocationSupport.slot_source snap loSlot,
    source_hi ▸ GeneralNominalAllocationSupport.slot_source snap hiSlot⟩

end Yulang.GeneralWhereVersionReuse317
