import Yulang.RigidRecordQuotientDecisions
import Yulang.RigidRecordCheckerExamples

/-! Kernel execution of the actual quotient comparator. The opaque-demand
boundary remains separate; these examples exercise the selected rigid rule
and semantic identification of equivalent finite record spellings. -/

namespace Yulang.RigidRecordQuotientExamples

open StructuralBase (Ty)
open RigidRecordCheckerExamples (pureRows integer string singleton neverTail redundant)

def pureLe (_ _ : Unit) : Prop := True

theorem pureExact : ∀ a b, pureRows a b = true ↔ pureLe a b :=
  fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩

theorem pureRefl : ∀ row, pureLe row row := fun _ => trivial
theorem pureTrans : ∀ {a b c}, pureLe a b → pureLe b c → pureLe a c := fun _ _ => trivial

def neverWidth : Bool :=
  RigidRecordQuotientDecisions.check pureRows pureExact pureRefl pureTrans
    (RigidRecordQuotient.mk neverTail) (RigidRecordQuotient.mk .emptyRecord)

def tailUnit : Bool :=
  RigidRecordQuotientDecisions.equal pureRows pureExact pureRefl pureTrans
    (RigidRecordQuotient.mk singleton) (RigidRecordQuotient.mk redundant)

def hiddenProper : Bool :=
  RigidRecordQuotientDecisions.equal pureRows pureExact pureRefl pureTrans
    (RigidRecordQuotient.mk (.record 0 integer (.record 0 string .emptyRecord)))
    (RigidRecordQuotient.mk singleton)

theorem never_width_computed : neverWidth = true := by decide +kernel
theorem tail_unit_computed : tailUnit = true := by decide +kernel
theorem hidden_proper_computed : hiddenProper = true := by decide +kernel

def cases : List (String × Bool) :=
  [("quotient never-tail width", neverWidth),
   ("quotient union unit", tailUnit),
   ("quotient proper hidden field", hiddenProper)]

end Yulang.RigidRecordQuotientExamples
