import Yulang.CommonCanonicalOpen
import Yulang.CommonBoundCoalescing
import Yulang.Casts

/-!
# Executable compatibility for closed common scalar expressions

The ground scalar grammar consists of the four existing base types, bottom,
top, union and intersection. It has no type/row variables. The executable
checker uses the already proved canonical scalar encoding. This module also
embeds that finite syntax into the existing cast syntax and proves exact
round-tripping; it does not reinterpret arbitrary `Casts.Ty` as a common type.
-/

namespace Yulang.CommonGroundScalarCasts

open ProducerCanonicalOpen (Expr)

abbrev Scalar := Expr 0

def meaning (expression : Scalar) : Common.Ty :=
  CommonCanonicalOpen.instantiate Fin.elim0 expression

def quote : Scalar → Casts.Ty
  | .atom (.base scalar) => .base scalar
  | .atom (.var index) => nomatch index
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (quote first) (quote last)
  | .inter first last => .inter (quote first) (quote last)

def read : Casts.Ty → Option Scalar
  | .base scalar => some (.atom (.base scalar))
  | .bottom => some .bottom
  | .top => some .top
  | .union first last => do return .union (← read first) (← read last)
  | .inter first last => do return .inter (← read first) (← read last)
  | _ => none

@[simp] theorem read_quote (expression : Scalar) : read (quote expression) = some expression := by
  induction expression with
  | atom atom => cases atom with
      | var index => exact Fin.elim0 index
      | base scalar => rfl
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl => simp [quote, read, ihf, ihl]

theorem quote_injective {first last : Scalar} (same : quote first = quote last) : first = last := by
  have same := congrArg read same
  simpa only [read_quote, Option.some.injEq] using same

theorem meaning_equivalent_iff (first last : Scalar) :
    Common.Equivalent (meaning first) (meaning last) ↔
      CommonCanonicalOpen.Equivalent first last := by
  constructor
  · intro same parameters
    have unique : parameters = Fin.elim0 := by funext index; exact Fin.elim0 index
    simpa only [unique, meaning] using same
  · intro same
    exact same Fin.elim0

theorem scalar_canonical_exact (first last : Scalar) :
    Common.Equivalent (meaning first) (meaning last) ↔
      CommonCanonicalOpen.canonicalEncoding first = CommonCanonicalOpen.canonicalEncoding last :=
  (meaning_equivalent_iff first last).trans (CommonCanonicalOpen.canonicalEncoding_exact first last)

theorem scalar_normalized_quote_exact (first last : Scalar) :
    Common.Equivalent (meaning first) (meaning last) ↔
      quote (CommonCanonicalOpen.normalize first) = quote (CommonCanonicalOpen.normalize last) := by
  rw [meaning_equivalent_iff, CommonCanonicalOpen.normalize_exact]
  exact ⟨congrArg quote, quote_injective⟩

def check (source target : Scalar) : Bool :=
  decide (CommonCanonicalOpen.canonicalEncoding (.union source target) =
    CommonCanonicalOpen.canonicalEncoding target)

/-- All ground scalar inputs; canonicalization is computed, not a premise. -/
theorem check_exact (source target : Scalar) :
    check source target = true ↔ Common.Subtype (meaning source) (meaning target) := by
  simp only [check, decide_eq_true_eq]
  rw [← scalar_canonical_exact]
  change Common.Equivalent (.union (meaning source) (meaning target)) (meaning target) ↔ _
  constructor
  · intro same
    exact (Common.common_union_is_join _ _ _).mp same.1 |>.1
  · intro below
    exact ⟨(Common.common_union_is_join _ _ _).mpr ⟨below, Common.subtype_refl _⟩,
      CommonBoundCoalescing.le_union_right _ _⟩

end Yulang.CommonGroundScalarCasts
