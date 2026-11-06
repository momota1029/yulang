import Yulang.ShadowRecordChecker
import Yulang.ShadowRecordQuotientDecisions

/-!
# Kernel execution of arbitrary-tail hidden-field comparison

The positive cases exercise both directions of the new equation, semantic
head exposure through lattice syntax, and recursive payload normalization.
The negative cases retain visible fields, distinct scalars and the absence
of a branchwise record-distribution rule. They concern the explicitly defined
ground relation, not a source elaborator or general graph solver.
-/

namespace Yulang.ShadowRecordCheckerExamples

open StructuralBase (Ty)
open ShadowRecordChecker (check)

def pureRows (_ _ : Unit) : Bool := true
def pureLe (_ _ : Unit) : Prop := True

theorem pureRows_exact (a b : Unit) : pureRows a b = true ↔ pureLe a b := by
  simp [pureRows, pureLe]

theorem pureRows_refl (a : Unit) : pureLe a a := trivial
theorem pureRows_trans {a b c : Unit} (_ : pureLe a b) (_ : pureLe b c) : pureLe a c := trivial

abbrev integer : Ty Unit := .base .int
abbrev string : Ty Unit := .base .str
abbrev boolean : Ty Unit := .base .bool
abbrev opaqueTail : Ty Unit :=
  .union (.record 1 integer .emptyRecord) (.record 2 string .emptyRecord)
abbrev flat : Ty Unit := .record 0 integer opaqueTail
abbrev hidden : Ty Unit := .record 0 integer (.record 0 string opaqueTail)
abbrev latticeHidden : Ty Unit :=
  .record 0 integer (.union (.record 0 string opaqueTail) .bottom)
abbrev absorbedHidden : Ty Unit :=
  .record 0 integer (.union (.record 0 string opaqueTail)
    (.inter (.record 0 string opaqueTail) .emptyRecord))
abbrev branchwise : Ty Unit :=
  .record 0 boolean (.union (.record 0 integer .bottom) (.record 0 string .bottom))
abbrev branchwiseErased : Ty Unit := .record 0 boolean .bottom

theorem opaque_shadow_forward : check pureRows hidden flat = true := by decide +kernel
theorem opaque_shadow_backward : check pureRows flat hidden = true := by decide +kernel
theorem lattice_exposure_forward : check pureRows latticeHidden flat = true := by decide +kernel
theorem lattice_exposure_backward : check pureRows flat latticeHidden = true := by decide +kernel
theorem absorption_exposure : check pureRows absorbedHidden flat = true := by decide +kernel
theorem hidden_never_tail :
    check pureRows (.record 0 integer (.record 0 string .bottom))
      (.record 0 integer .bottom) = true := by decide +kernel
theorem nested_payload_shadow :
    check pureRows (.pair (.variant 7 hidden) (.arrow hidden () flat ()))
      (.pair (.variant 7 flat) (.arrow flat () hidden ())) = true := by decide +kernel
theorem visible_payload_rejected :
    check pureRows hidden (.record 0 string opaqueTail) = false := by decide +kernel
theorem distinct_scalars : check pureRows integer string = false := by decide +kernel
theorem nonrecord_tail_rejected :
    check pureRows (.record 0 integer string) .emptyRecord = false := by decide +kernel

/-- The primitive shadow equation does not silently distribute across the
two genuinely different opaque alternatives of a supplied tail. -/
theorem no_branchwise_erasure : check pureRows branchwise branchwiseErased = false := by decide +kernel

theorem quotient_hidden_equal :
    ShadowRecordQuotientDecisions.equal pureRows pureRows_exact pureRows_refl pureRows_trans
      (ShadowRecordQuotient.mk hidden) (ShadowRecordQuotient.mk flat) = true := by
  decide +kernel

def cases : List (String × Ty Unit × Ty Unit × Bool) :=
  [ ("opaque shadow forward", hidden, flat, true)
  , ("opaque shadow backward", flat, hidden, true)
  , ("lattice-exposed shadow forward", latticeHidden, flat, true)
  , ("lattice-exposed shadow backward", flat, latticeHidden, true)
  , ("absorption-exposed shadow", absorbedHidden, flat, true)
  , ("hidden field above never", .record 0 integer (.record 0 string .bottom),
      .record 0 integer .bottom, true)
  , ("normalization inside variant pair and function", .pair (.variant 7 hidden) (.arrow hidden () flat ()),
      .pair (.variant 7 flat) (.arrow flat () hidden ()), true)
  , ("visible payload mismatch", hidden, .record 0 string opaqueTail, false)
  , ("distinct scalar types", integer, string, false)
  , ("nonrecord tail", .record 0 integer string, .emptyRecord, false)
  , ("no invented branchwise erasure", branchwise, branchwiseErased, false)
  ]

end Yulang.ShadowRecordCheckerExamples
