import Yulang.CommonCaseLiteralCoverage

/-! Complete finite cells for products and closed tag alternatives whose
leaves are any of the four Common bases, including all decoded strings. The
choice constructor describes a coverage domain, not an old Common union. -/

namespace Yulang.CommonCaseBaseCells

open CaseValues
open LiteralValues (Literal)

inductive Shape where
  | base : Inference.Base → Shape
  | pair : Shape → Shape → Shape
  | variant : Nat → Shape → Shape
  | choice : Shape → Shape → Shape
  deriving DecidableEq, Repr

inductive InShape : Shape → Value Empty → Prop where
  | base : Core.CommonData.literalBase value = base → InShape (.base base) (.literal value)
  | pair : InShape first left → InShape last right → InShape (.pair first last) (.pair left right)
  | variant : InShape payload value → InShape (.variant tag payload) (.variant tag value)
  | left : InShape first value → InShape (.choice first last) value
  | right : InShape last value → InShape (.choice first last) value

inductive Supported : Value Empty → Prop where
  | literal : Supported (.literal value)
  | pair : Supported left → Supported right → Supported (.pair left right)
  | variant : Supported value → Supported (.variant tag value)

theorem InShape.supported (valid : InShape shape value) : Supported value := by
  induction valid with
  | base => exact .literal
  | pair left right ihl ihr => exact .pair ihl ihr
  | variant child ih => exact .variant ih
  | left child ih | right child ih => exact ih

inductive ValueEquivalent (bounds : List Int) (texts : List String) : Value Empty → Value Empty → Prop where
  | literal : CommonCaseLiteralCells.Equivalent bounds texts first last →
      ValueEquivalent bounds texts (.literal first) (.literal last)
  | pair : ValueEquivalent bounds texts first first' → ValueEquivalent bounds texts last last' →
      ValueEquivalent bounds texts (.pair first last) (.pair first' last')
  | variant : ValueEquivalent bounds texts first last →
      ValueEquivalent bounds texts (.variant tag first) (.variant tag last)

def representatives (bounds : List Int) (texts : List String) : Shape → List (Value Empty)
  | .base base => ((CommonCaseLiteralCells.representatives bounds texts).filter
      (fun literal => decide (Core.CommonData.literalBase literal = base))).map .literal
  | .pair first last => (representatives bounds texts first).flatMap fun left =>
      (representatives bounds texts last).map fun right => .pair left right
  | .variant tag payload => (representatives bounds texts payload).map (.variant tag)
  | .choice first last => representatives bounds texts first ++ representatives bounds texts last

theorem representatives_sound (bounds : List Int) (texts : List String) (shape : Shape) (value : Value Empty)
    (member : value ∈ representatives bounds texts shape) : InShape shape value := by
  induction shape generalizing value with
  | base base =>
      obtain ⟨literal, present, rfl⟩ := List.mem_map.mp member
      exact .base (of_decide_eq_true (List.mem_filter.mp present).2)
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

theorem representative_complete (bounds : List Int) (texts : List String) (valid : InShape shape value) :
    ∃ representative ∈ representatives bounds texts shape, ValueEquivalent bounds texts representative value := by
  induction valid with
  | @base literal base kind =>
      obtain ⟨sample, member, same⟩ := CommonCaseLiteralCells.representative_complete bounds texts literal
      have sampleBase := (CommonCaseLiteralCoverage.equivalent_base_eq same).trans kind
      exact ⟨.literal sample, List.mem_map.mpr ⟨sample, List.mem_filter.mpr ⟨member, by simp [sampleBase]⟩, rfl⟩, .literal same⟩
  | pair left right ihl ihr =>
      obtain ⟨first, firstMember, firstSame⟩ := ihl
      obtain ⟨last, lastMember, lastSame⟩ := ihr
      exact ⟨.pair first last,
        List.mem_flatMap.mpr ⟨first, firstMember, List.mem_map.mpr ⟨last, lastMember, rfl⟩⟩, .pair firstSame lastSame⟩
  | @variant payload value tag child ih =>
      obtain ⟨sample, member, same⟩ := ih
      exact ⟨.variant tag sample, List.mem_map.mpr ⟨sample, member, rfl⟩, .variant same⟩
  | left child ih =>
      obtain ⟨sample, member, same⟩ := ih
      exact ⟨sample, List.mem_append_left _ member, same⟩
  | right child ih =>
      obtain ⟨sample, member, same⟩ := ih
      exact ⟨sample, List.mem_append_right _ member, same⟩

end Yulang.CommonCaseBaseCells
