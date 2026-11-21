import Yulang.GeneralDeclarativeRepeatedNode320
import Yulang.GeneralDictionaryDefaultExpression209

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 4400000
namespace Yulang.GeneralDeclarativeMergeAgreement320
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeMerge320 (Merge lower_exact upper_exact equality_sound shared_center)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatExtension (names)
open GeneralNominalMaterialization (Mode)

/-- The proof-producing choice of a representative occurrence and the order
of the join/meet folds do not affect the semantics of a *shared* capture.
This is local to capture facts, not a resolver order-independence claim. -/
theorem merge_agrees {s : State} {first second : Capture} {left right : List Capture}
    {one two : Capture}
    (a : Merge s first left one) (b : Merge s second right two)
    (same : ∀ entry, entry ∈ first :: left ↔ entry ∈ second :: right)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m one.lower).1 (m two.lower).1 ∧
    Equivalent (m one.center).1 (m two.center).1 ∧
    Equivalent (m one.upper).1 (m two.upper).1 := by
  have loA := equality_sound a.lowerEq m valid
  have loB := equality_sound b.lowerEq m valid
  have hiA := equality_sound a.upperEq m valid
  have hiB := equality_sound b.upperEq m valid
  have leLo1 := (lower_exact m first left _).mp loA.2
  have leLo2 := (lower_exact m second right _).mp loB.2
  have leHi1 := (upper_exact m first left _).mp hiA.1
  have leHi2 := (upper_exact m second right _).mp hiB.1
  have rootA := (shared_center a m valid).2 first List.mem_cons_self
  have rootB := (shared_center b m valid).2 first ((same first).mp List.mem_cons_self)
  refine ⟨⟨?_,?_⟩,eqv_trans (eqv_symm rootA) rootB,⟨?_,?_⟩⟩
  · exact subtype_trans loA.1 ((lower_exact m first left _).mpr (fun entry used => leLo2 entry ((same entry).mp used)))
  · exact subtype_trans loB.1 ((lower_exact m second right _).mpr (fun entry used => leLo1 entry ((same entry).mpr used)))
  · exact subtype_trans ((upper_exact m second right _).mpr (fun entry used => leHi1 entry ((same entry).mpr used))) hiB.2
  · exact subtype_trans ((upper_exact m first left _).mpr (fun entry used => leHi2 entry ((same entry).mp used))) hiA.2

/-- The same result applies after the checked expression is used at
an arbitrary mode, including invariant nominal subexpressions. -/
theorem same_compiled_value {s : State} {first last : Nat → Capture} {exp : Expr}
    (common : ∀ n ∈ names exp, ∃ a b left right,
      Merge s a left (first n) ∧ Merge s b right (last n) ∧
      ∀ entry, entry ∈ a :: left ↔ entry ∈ b :: right)
    (m : Assignment) (valid : Models s m) (mode : Mode) :
    Equivalent (value (variables first m) mode exp) (value (variables last m) mode exp) := by
  apply GeneralDictionaryDefaultExpression209.value_equivalent exp
  intro mu name used
  obtain ⟨a,b,left,right,one,two,same⟩ := common name used
  have points := merge_agrees one two same m valid
  cases mu
  · exact points.1
  · exact points.2.2
  · exact points.2.1

end Yulang.GeneralDeclarativeMergeAgreement320
