import Yulang.GeneralDictionaryAggregateBasis256
namespace Yulang.GeneralDictionaryAggregateRows256
open Core.PresenceGeneration
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralDictionaryLooseIterationBook240 (context)
open GeneralDictionaryLooseFamilyBase240 (anchor)
open GeneralDictionaryAggregateHistory256 (history)
open GeneralPresenceOrderedSubstitution247 (mapping)

/-- Actual added slots carry the same numeric source in their row component.
Type-equation expansion deliberately does not replace that row reference. -/
theorem historical_row (n : Nat) :
 ((GeneralNominalRebaseRawView243.compile (context n).state (mapping (history n))).slot (anchor n)).row =
 .var (lower n) := by
 change (mapping (history n) (GeneralDictionaryLooseFamilyBase240.source n (anchor n))).row = _
 rw [GeneralDictionaryLooseFamilyBase240.source_anchor,GeneralPresenceOrderedAppend256.mapping_row]

theorem row_read_retained (n : Nat) : lower (n+1) ∈
 GeneralPresenceSubstitutionSupport244.rowSources
   (((GeneralNominalRebaseRawView243.compile (context (n+1)).state (mapping (history (n+1)))).slot (anchor (n+1))).row) := by
 rw [historical_row]
 exact List.mem_singleton_self _

theorem row_name_private (n : Nat) :
 lower (n+1) = GeneralNominalPublicBasis253.privateName 4 0 0 0 0
   (GeneralNominalAggregateVersion231.version (GeneralDictionaryLooseFamilyNames240.repeated (lower n)) 0) := by
 rfl

/-- The retained row label is not one of the initial source labels. This
asserts syntax only, not that an active source row constraint reads it. -/
theorem outside_initial_names (n : Nat) : lower (n+1) ∉ [0,1,2,3,4] := by
 have above := GeneralDictionaryLooseFamilyNames240.lower_above n
 simp only [List.mem_cons,List.not_mem_nil,or_false]
 omega
/-- Only the inactive paired slot metadata is erased; ordinary row atoms
and row parameters inside descriptors are retained literally. -/
def eraseSlotRows (view : GeneralNominalRebaseRawView243.View) : GeneralNominalRebaseRawView243.View :=
 { view with slot := fun index => ⟨(view.slot index).ty,.empty⟩ }

/-- Current View.Models never reads slot.row directly. This does not justify
erasing row-valued consumers or changing a future source transition. -/
theorem slot_rows_irrelevant (view : GeneralNominalRebaseRawView243.View)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 (eraseSlotRows view).Models assignment ↔ view.Models assignment := Iff.rfl

theorem erased_row_sources (view : GeneralNominalRebaseRawView243.View) (index : Fin view.slots) :
 GeneralPresenceSubstitutionSupport244.rowSources ((eraseSlotRows view).slot index).row = [] := rfl
end Yulang.GeneralDictionaryAggregateRows256
