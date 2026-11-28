import Yulang.GeneralDeclarativeI65I74ExactSelectedCardChild484

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralCandidateInspection (Primitive)

theorem read_variant_card_has_a_selected_literal_payload
    {s : GeneralDeclarativeHead320.State} {t : Table} {m : Mode}
    {tag : Nat} {raw code : Expr} {child : ReadCard} {outerUses}
    (atRoot : runReadCard s t m (.variant tag raw) (.variant tag code) (.variant child) = some outerUses) :
    runReadCard s t m raw code child = some outerUses ∧
      Read (SourceExposure481.authoredView s t) m raw code outerUses := by
  cases found : checkedRead s t m raw code child with
  | none => simp [runReadCard,checkedRead,found] at atRoot
  | some actual =>
    have same : actual.seen = outerUses := by simpa [runReadCard,checkedRead,found] using atRoot
    exact ⟨by simp [runReadCard,found,same],same ▸ actual.valid⟩

theorem read_primitive_card_has_the_exact_requested_child
    {s : GeneralDeclarativeHead320.State} {t : Table} {m : Mode}
    {tag : Primitive} {raw code : List Expr} {children : ReadCards} {outerUses}
    (atRoot : runReadCard s t m (.primitive tag raw) (.primitive tag code) (.primitive children) = some outerUses)
    (ordinal : Nat) {a b : Expr} (left : raw[ordinal]? = some a) (right : code[ordinal]? = some b) :
    ∃ child uses, subCard (.arg ordinal) (.primitive children) = some child ∧
      runReadCard s t m a b child = some uses ∧ Read (SourceExposure481.authoredView s t) m a b uses := by
  cases found : checkedArgs s t m raw code children with
  | none => simp [runReadCard,checkedRead,found] at atRoot
  | some actual =>
    exact checked_argument_card_restricts_to_the_exact_independently_typed_child found ordinal left right

theorem read_nominal_point_card_has_the_exact_requested_child
    {s : GeneralDeclarativeHead320.State} {t : Table} {m : Mode}
    {tag : Nat} {raw code : Expr} {children : ReadCards} {outerUses}
    (atRoot : runReadCard s t m (.nominal tag [raw]) (.nominal tag [code]) (.nominal children) = some outerUses) :
    ∃ child uses, subCard (.arg 0) (.nominal children) = some child ∧
      runReadCard s t .actual raw code child = some uses ∧
      Read (SourceExposure481.authoredView s t) .actual raw code uses := by
  cases found : checkedArgs s t .actual [raw] [code] children with
  | none => simp [runReadCard,checkedRead,found] at atRoot
  | some actual =>
    exact checked_argument_card_restricts_to_the_exact_independently_typed_child found 0 rfl rfl

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
