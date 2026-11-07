import Yulang.CommonCaseIntegerCells
import Yulang.CaseValues

/-! Finite representative cells for integer products and closed structural
variant alternatives. Shape is a coverage-domain description, not a new
Common type or a replacement for the missing merged variant carrier. -/

namespace Yulang.CommonCaseStructuralCells

open CaseValues
open CommonCaseIntegerCells (SameComparisons)

inductive Shape where
  | integer
  | pair : Shape → Shape → Shape
  | variant : Nat → Shape → Shape
  | choice : Shape → Shape → Shape
  deriving DecidableEq, Repr

inductive InShape : Shape → Value F → Prop where
  | integer : InShape .integer (.literal (.int value))
  | pair : InShape first left → InShape last right → InShape (.pair first last) (.pair left right)
  | variant : InShape payload value → InShape (.variant tag payload) (.variant tag value)
  | left : InShape first value → InShape (.choice first last) value
  | right : InShape last value → InShape (.choice first last) value

inductive Supported : Value F → Prop where
  | integer : Supported (.literal (.int value))
  | pair : Supported left → Supported right → Supported (.pair left right)
  | variant : Supported value → Supported (.variant tag value)

theorem InShape.supported (valid : InShape shape value) : Supported value := by
  induction valid with
  | integer => exact .integer
  | pair left right ihl ihr => exact .pair ihl ihr
  | variant child ih => exact .variant ih
  | left child ih | right child ih => exact ih

inductive ValueEquivalent (bounds : List Int) : Value F → Value F → Prop where
  | integer : SameComparisons bounds first last →
      ValueEquivalent bounds (.literal (.int first)) (.literal (.int last))
  | pair : ValueEquivalent bounds first first' → ValueEquivalent bounds last last' →
      ValueEquivalent bounds (.pair first last) (.pair first' last')
  | variant : ValueEquivalent bounds first last →
      ValueEquivalent bounds (.variant tag first) (.variant tag last)

theorem ValueEquivalent.supported_left (same : ValueEquivalent bounds first last) : Supported first := by
  induction same with
  | integer => exact .integer
  | pair left right ihl ihr => exact .pair ihl ihr
  | variant child ih => exact .variant ih

theorem ValueEquivalent.supported_right (same : ValueEquivalent bounds first last) : Supported last := by
  induction same with
  | integer => exact .integer
  | pair left right ihl ihr => exact .pair ihl ihr
  | variant child ih => exact .variant ih

def representatives (bounds : List Int) : Shape → List (Value F)
  | .integer => (CommonCaseIntegerCells.representatives bounds).map (fun value => .literal (.int value))
  | .pair first last => (representatives bounds first).flatMap fun left =>
      (representatives bounds last).map fun right => .pair left right
  | .variant tag payload => (representatives bounds payload).map (.variant tag)
  | .choice first last => representatives bounds first ++ representatives bounds last

theorem representatives_sound (bounds : List Int) (shape : Shape) (value : Value F)
    (member : value ∈ representatives bounds shape) : InShape shape value := by
  induction shape generalizing value with
  | integer =>
      obtain ⟨integer, included, rfl⟩ := List.mem_map.mp member
      exact .integer
  | pair first last ihf ihl =>
      obtain ⟨left, included, rightMember⟩ := List.mem_flatMap.mp member
      obtain ⟨right, present, rfl⟩ := List.mem_map.mp rightMember
      exact .pair (ihf left included) (ihl right present)
  | variant tag payload ih =>
      obtain ⟨item, included, rfl⟩ := List.mem_map.mp member
      exact .variant (ih item included)
  | choice first last ihf ihl =>
      rcases List.mem_append.mp member with left | right
      · exact .left (ihf value left)
      · exact .right (ihl value right)

/-- All actual values in the domain, arbitrary finite endpoint sets and
every nested tuple/closed variant shape. No sampled-subject assumption. -/
theorem representative_complete (bounds : List Int) (valid : InShape shape value) :
    ∃ representative ∈ representatives bounds shape, ValueEquivalent bounds representative value := by
  induction valid with
  | @integer integer =>
      obtain ⟨representative, member, same⟩ := CommonCaseIntegerCells.representative_exact bounds integer
      exact ⟨.literal (.int representative), List.mem_map.mpr ⟨representative, member, rfl⟩, .integer same⟩
  | pair left right ihl ihr =>
      obtain ⟨first, firstMember, firstSame⟩ := ihl
      obtain ⟨last, lastMember, lastSame⟩ := ihr
      exact ⟨.pair first last,
        List.mem_flatMap.mpr ⟨first, firstMember, List.mem_map.mpr ⟨last, lastMember, rfl⟩⟩,
        .pair firstSame lastSame⟩
  | @variant payload value tag child ih =>
      obtain ⟨representative, member, same⟩ := ih
      exact ⟨.variant tag representative, List.mem_map.mpr ⟨representative, member, rfl⟩, .variant same⟩
  | left child ih =>
      obtain ⟨representative, member, same⟩ := ih
      exact ⟨representative, List.mem_append_left _ member, same⟩
  | right child ih =>
      obtain ⟨representative, member, same⟩ := ih
      exact ⟨representative, List.mem_append_right _ member, same⟩

end Yulang.CommonCaseStructuralCells
