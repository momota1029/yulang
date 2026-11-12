import Yulang.GeneralDictionarySlotFreshnessTransport
import Yulang.GeneralDictionaryNominalSlotTransportExamples

/-! The concrete mixed nominal extension meets both coordinate bounds: type88
was reserved, while new row44 lies below the retained seed77. No authority to
introduce arbitrary type IDs follows from this collision-only certificate. -/
namespace Yulang.GeneralDictionarySlotFreshnessTransportExamples
open GeneralDictionaryNominalSlotTransportExamples
open GeneralDictionarySlotFreshnessTransport

/-- Both old type slots and the reserved new type coordinate are already listed.
All target row coordinates are bounded by the persistent old seed. -/
theorem mixed_coordinates_bounded : CoordinatesBound mixedBefore mixedAfter := by
  constructor
  · rintro ⟨index, bound⟩
    change index < 3 at bound
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · left; change 10 ∈ [10, 77, 42, 43, 88]; decide
    · left; change 77 ∈ [10, 77, 42, 43, 88]; decide
    · left; change 88 ∈ [10, 77, 42, 43, 88]; decide
  · rintro ⟨index, bound⟩
    change index < 3 at bound
    right
    change 42 + index ≤ 77
    omega

/-- In particular, the newly represented type and row use different justification. -/
theorem new_coordinates_justified :
    mixedAfter.base.source 2 = 88 ∧ 88 ∈ mixedBefore.reserved ∧
    mixedAfter.base.rowSource 2 = 44 ∧ 44 ≤ mixedBefore.seed := by
  exact ⟨rfl, by simp, rfl, by decide⟩

theorem mixed_sources_preserved (identity : Nat) (member : identity ∈ GeneralNominalState.sources mixedBefore) :
    identity ∈ GeneralNominalState.sources mixedAfter := sources_preserved mixedTransport identity member

theorem mixed_fresh_iff (registry : GeneralDeclarations.Registry) (root : Nat) :
    GeneralNominalAllocation.Fresh mixedAfter registry root ↔ GeneralNominalAllocation.Fresh mixedBefore registry root :=
  fresh_iff mixedTransport mixed_coordinates_bounded registry root

theorem mixed_unowned_absent (registry : GeneralDeclarations.Registry) (root : Nat)
    (fresh : GeneralNominalAllocation.Fresh mixedBefore registry root)
    (key : GeneralNominalAllocation.Origin) (listed : key ∈ GeneralNominalAllocation.keys registry root)
    (unowned : key ∉ mixedBefore.allocated) :
    GeneralNominalAllocation.source mixedAfter registry root key ∉ GeneralNominalState.sources mixedAfter :=
  unowned_generated_absent mixedTransport mixed_coordinates_bounded registry root fresh key listed unowned

end Yulang.GeneralDictionarySlotFreshnessTransportExamples
