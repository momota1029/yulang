import Yulang.CommonCaseRecordCells
import Yulang.CommonCaseBaseOrdered

/-! Independent Common required-field bounds supply the record coverage
domain internally, including regular input types and duplicate specification
labels. The domain is never identified with an extensional Common type. -/

namespace Yulang.CommonCaseRecordReadout

open Core
open PresenceGeneration (Comp)
open CommonCaseBaseOrdered (Tree)
open CommonCaseRecordCells (Domain)

abbrev Specification := List (Nat × Tree)

def shapes (specification : Specification) : CommonCaseRecordCells.Specification :=
  specification.map fun entry => (entry.1, entry.2.shape)

def type : Specification → Common.Ty
  | [] => Common.emptyRecord
  | (name, tree) :: rest => .inter (Common.required name tree.type) (type rest)

theorem type_width (specification : Specification) : Common.Subtype (type specification) Common.emptyRecord := by
  induction specification with
  | nil => exact Common.subtype_refl _
  | cons entry rest ih => exact Common.subtype_trans (CommonBoundCoalescing.inter_le_right _ _) ih

theorem type_field (specification : Specification) (entry : Nat × Tree) (member : entry ∈ specification) :
    Common.Subtype (type specification) (Common.required entry.1 entry.2.type) := by
  induction specification with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact CommonBoundCoalescing.inter_le_left _ _
      · exact Common.subtype_trans (CommonBoundCoalescing.inter_le_right _ _) (ih later)

/-- Arbitrary actual values and Common computations. The input type bound
alone supplies every field-domain premise; no successful pattern or finite
support oracle is required. -/
theorem readout (specification : Specification) (value : CommonData.Value) (result : Comp Common.model)
    (typed : CommonData.ValueTyping Common.model value result) (below : Common.Subtype result.1 (type specification)) :
    ∃ fields, value = .record fields ∧ Domain (shapes specification) fields := by
  obtain ⟨fields, rfl⟩ := CommonPatternLookup.records_of_width typed (Common.subtype_trans below (type_width specification))
  refine ⟨fields, rfl, ?_⟩
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨item, found, itemTyped⟩ := CommonPatternLookup.required_lookup fields result original.1 original.2.type typed
    (Common.subtype_trans below (type_field specification original originalMember))
  exact ⟨item, found, original.2.readout itemTyped (Common.subtype_refl _)⟩

theorem finite_representative (bounds : List Int) (texts : List String) (specification : Specification)
    (value : CommonData.Value) (result : Comp Common.model)
    (typed : CommonData.ValueTyping Common.model value result) (below : Common.Subtype result.1 (type specification)) :
    ∃ fields, value = .record fields ∧ ∃ samples ∈ CommonCaseRecordCells.representatives bounds texts (shapes specification),
      CommonCaseRecordCells.EntriesRelated bounds texts fields (shapes specification) samples := by
  obtain ⟨fields, same, domain⟩ := readout specification value result typed below
  obtain ⟨samples, member, related⟩ := CommonCaseRecordCells.representative_complete bounds texts (shapes specification) fields domain
  exact ⟨fields, same, samples, member, related⟩

end Yulang.CommonCaseRecordReadout
