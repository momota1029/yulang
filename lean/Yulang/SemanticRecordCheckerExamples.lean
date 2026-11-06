import Yulang.SemanticRecordQuotientDecisions

/-!
# Kernel execution checks for semantic record comparison

These examples run the complete finite-type checker for the explicitly
minimal congruence model. The last example records its known width boundary,
so accepting the decision-38 equivalence does not conceal a larger claim
about arbitrary admissible tails.
-/

namespace Yulang.SemanticRecordCheckerExamples

open StructuralBase (Ty)
open SemanticRecordChecker (check)

def pureRows (_ _ : Unit) : Bool := true

abbrev integer : Ty Unit := .base .int
abbrev string : Ty Unit := .base .str
abbrev proper : Ty Unit := .record 0 integer .emptyRecord
abbrev redundant : Ty Unit := .record 0 integer (.union .emptyRecord .bottom)
abbrev absorbed : Ty Unit :=
  .record 0 integer (.inter (.union .emptyRecord (.base .str)) .emptyRecord)
abbrev shadowed : Ty Unit :=
  .record 0 integer (.record 0 string (.union .emptyRecord .bottom))
abbrev unionTail : Ty Unit :=
  .union (.record 1 integer .emptyRecord) (.record 2 string .emptyRecord)
abbrev reverseTail : Ty Unit :=
  .union (.record 2 string .emptyRecord) (.record 1 integer .emptyRecord)

theorem redundant_forward : check pureRows proper redundant = true := by decide +kernel
theorem redundant_backward : check pureRows redundant proper = true := by decide +kernel
theorem absorption_forward : check pureRows proper absorbed = true := by decide +kernel
theorem absorption_backward : check pureRows absorbed proper = true := by decide +kernel
theorem shadowed_forward : check pureRows shadowed proper = true := by decide +kernel
theorem shadowed_backward : check pureRows proper shadowed = true := by decide +kernel
theorem shadowed_int_not_str :
    check pureRows shadowed (.record 0 string .emptyRecord) = false := by decide +kernel
theorem unrelated_field_rejected :
    check pureRows redundant (.record 1 integer .emptyRecord) = false := by decide +kernel
theorem union_tail_order_forward :
    check pureRows (.record 0 integer unionTail) (.record 0 integer reverseTail) = true := by decide +kernel
theorem union_tail_order_backward :
    check pureRows (.record 0 integer reverseTail) (.record 0 integer unionTail) = true := by decide +kernel
theorem nested_record_equivalence :
    check pureRows (.pair redundant shadowed) (.pair proper proper) = true := by decide +kernel
theorem plain_scalar_rejected : check pureRows integer string = false := by decide +kernel

def boolRows (left right : Bool) : Bool := !left || right

theorem input_row_contravariant :
    check boolRows (.arrow (.base .int) true (.base .int) false)
      (.arrow (.base .int) false (.base .int) false) = true := by decide +kernel
theorem input_row_reverse_rejected :
    check boolRows (.arrow (.base .int) false (.base .int) false)
      (.arrow (.base .int) true (.base .int) false) = false := by decide +kernel

/-- This is an explicit limitation of the minimal congruence foundation,
not a proposed rejection in the intended full source language. -/
theorem minimum_relation_does_not_supply_raw_width :
    check pureRows (.record 0 integer .bottom) .emptyRecord = false := by decide +kernel

def pureLe (_ _ : Unit) : Prop := True

theorem pureRows_exact (a b : Unit) : pureRows a b = true ↔ pureLe a b := by simp [pureRows, pureLe]
theorem pureRows_refl (a : Unit) : pureLe a a := trivial
theorem pureRows_trans {a b c : Unit} : pureLe a b → pureLe b c → pureLe a c := fun _ _ => trivial

abbrev quotientCheck : SemanticRecordQuotient.QTy pureLe → SemanticRecordQuotient.QTy pureLe → Bool :=
  SemanticRecordQuotientDecisions.check pureRows pureRows_exact pureRows_refl pureRows_trans

abbrev quotientEqual : SemanticRecordQuotient.QTy pureLe → SemanticRecordQuotient.QTy pureLe → Bool :=
  SemanticRecordQuotientDecisions.equal pureRows pureRows_exact pureRows_refl pureRows_trans

theorem quotient_redundant_tail_equal :
    quotientEqual (SemanticRecordQuotient.mk proper) (SemanticRecordQuotient.mk redundant) = true := by decide +kernel
theorem quotient_shadowed_order :
    quotientCheck (SemanticRecordQuotient.mk shadowed) (SemanticRecordQuotient.mk proper) = true := by decide +kernel
theorem quotient_distinct_scalars :
    quotientEqual (SemanticRecordQuotient.mk integer) (SemanticRecordQuotient.mk string) = false := by decide +kernel

def cases : List (String × Ty Unit × Ty Unit × Bool) :=
  [ ("redundant tail forward", proper, redundant, true)
  , ("redundant tail backward", redundant, proper, true)
  , ("absorbed tail forward", proper, absorbed, true)
  , ("absorbed tail backward", absorbed, proper, true)
  , ("first field after tail normalization", shadowed, proper, true)
  , ("hidden duplicate remains irrelevant", proper, shadowed, true)
  , ("shadowed int is not str", shadowed, .record 0 string .emptyRecord, false)
  , ("missing field", redundant, .record 1 integer .emptyRecord, false)
  , ("union tail order forward", .record 0 integer unionTail, .record 0 integer reverseTail, true)
  , ("union tail order backward", .record 0 integer reverseTail, .record 0 integer unionTail, true)
  , ("nested record equivalence", .pair redundant shadowed, .pair proper proper, true)
  , ("distinct scalars", integer, string, false)
  , ("minimum-relation width boundary", .record 0 integer .bottom, .emptyRecord, false)
  ]

end Yulang.SemanticRecordCheckerExamples
