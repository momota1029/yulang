import Yulang.CommonCanonicalPositive

/-!
# Why parameter-family canonicalization needs more than alpha or intervals

Concrete kernel-checked examples separate four boundaries. Two scalar
families with the same two genuinely used parameters are instance-equivalent
but not alpha-equivalent. Exact images of a shared positive parameter under a
pair are not intervals. A parameter shared across negative and positive arrow
positions imposes a real relation between those positions. Captured slots
cannot be reclassified as independently generalized ones.

These are finite counterexamples to specific invalid extensions, not an
undecidability claim. The final positive-constructor example demonstrates the
valid simultaneous elimination while retaining shared captured identities.
-/

namespace Yulang.CommonCanonicalObstructions

open ProducerCanonicalOpen (Expr)
open CommonCanonicalInterface (Form)
open Common (Row Ty Subtype Equivalent)

private theorem top_not_below_bottom : ¬ Subtype (.top : Ty) .bottom := by
  intro below
  have same : CommonCanonicalOpen.Equivalent (.top : Expr 0) .bottom :=
    fun _ => ⟨below, CommonBoundCoalescing.bottom_le _⟩
  have code := (CommonCanonicalOpen.canonicalEncoding_exact (.top : Expr 0) .bottom).mp same
  have different : CommonCanonicalOpen.canonicalEncoding (.top : Expr 0) ≠
      CommonCanonicalOpen.canonicalEncoding (.bottom : Expr 0) := by decide +kernel
  exact different code

def joined : CommonCanonicalIntervals.Polynomial 0 2 :=
  .union (.atom (.var 0)) (.atom (.var 1))

def intersected : CommonCanonicalIntervals.Polynomial 0 2 :=
  .inter (.atom (.var 0)) (.atom (.var 1))

theorem both_families_use_both_parameters :
    CommonCanonicalNames.used (.scalar joined) = [0, 1] ∧
      CommonCanonicalNames.used (.scalar intersected) = [0, 1] := by decide +kernel

theorem same_exact_scalar_instances : CommonCanonicalIntervals.FamilyEquivalent joined intersected :=
  (CommonCanonicalIntervals.canonicalEncoding_exact joined intersected).mpr (by decide +kernel)

/-- Same arity and absence of unused variables do not repair alpha
incompleteness, even before constructors, rows or recursion are introduced. -/
theorem same_arity_used_parameters_not_alpha :
    ¬ CommonCanonicalAlpha.AlphaEquivalent (.scalar joined) (.scalar intersected) := by
  rintro ⟨permutation, valid, same⟩
  have scalarSame : CommonCanonicalOpen.Equivalent
      (.union (.atom (.var (permutation.forward 0))) (.atom (.var (permutation.forward 1))))
      intersected := (CommonCanonicalInterface.equivalent_scalar_iff _ _).mp same
  have evaluations := (CommonCanonicalOpen.common_scalar_profile_exact _ _).mp scalarSame
    [.var 0] (by decide +kernel)
  have both : permutation.forward 0 = 0 ∧ permutation.forward 1 = 0 := by
    simpa [Expr.eval, intersected] using evaluations
  have collision := congrArg permutation.backward (both.1.trans both.2.symm)
  rw [valid.1 0, valid.1 1] at collision
  have different : (0 : Fin 2) ≠ 1 := by decide +kernel
  exact different collision

theorem different_alpha_encodings :
    CommonCanonicalAlpha.canonicalEncoding (.scalar joined) ≠
      CommonCanonicalAlpha.canonicalEncoding (.scalar intersected) :=
  fun same => same_arity_used_parameters_not_alpha
    (CommonCanonicalAlpha.canonicalEncoding_exact _ _ |>.mpr same)

/-- The target lies between the two constructor endpoints but no single
shared parameter produces it. This is already a single positive output. -/
theorem positive_pair_image_not_interval :
    Subtype (Common.pair .bottom .bottom) (Common.pair .top .bottom) ∧
      Subtype (Common.pair .top .bottom) (Common.pair .top .top) ∧
      ¬ ∃ parameter : Ty,
        Equivalent (Common.pair parameter parameter) (Common.pair .top .bottom) := by
  refine ⟨(Common.common_pair_iff _ _ _ _).mpr
    ⟨CommonBoundCoalescing.bottom_le _, Common.subtype_refl _⟩,
    (Common.common_pair_iff _ _ _ _).mpr
      ⟨Common.subtype_refl _, CommonBoundCoalescing.le_top _⟩, ?_⟩
  rintro ⟨parameter, same⟩
  have parts := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same
  exact top_not_below_bottom (Common.subtype_trans parts.1.2 parts.2.1)

/-- Forgetting that the domain and result use the same generalized slot
would admit a target that the shared family excludes, even under subsumption. -/
theorem mixed_polarity_sharing_matters (incoming outgoing : Row) :
    (∃ input output : Ty, Equivalent (Common.arrow input incoming output outgoing)
      (Common.arrow .top incoming .bottom outgoing)) ∧
      ¬ ∃ parameter : Ty, Subtype (Common.arrow parameter incoming parameter outgoing)
        (Common.arrow .top incoming .bottom outgoing) := by
  refine ⟨⟨.top, .bottom, Common.equivalent_refl _⟩, ?_⟩
  rintro ⟨parameter, below⟩
  have parts := (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below
  exact top_not_below_bottom (Common.subtype_trans parts.1 parts.2.2.1)

/-- The simultaneous-bottom rule is invalid when generalized occurrences
include a negative position. The positive pass must retain its syntax check. -/
theorem negative_occurrence_prevents_bottom_elimination (incoming outgoing : Row) :
    (∃ parameter : Ty, Subtype (Common.arrow parameter incoming parameter outgoing)
      (Common.arrow .top incoming .top outgoing)) ∧
      ¬ Subtype (Common.arrow .bottom incoming .bottom outgoing)
        (Common.arrow .top incoming .top outgoing) := by
  refine ⟨⟨.top, Common.subtype_refl _⟩, ?_⟩
  intro below
  exact top_not_below_bottom ((Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below).1

def capturedSlot : CommonCanonicalIntervals.Polynomial 1 1 := .atom (.var 0)
def generalizedSlot : CommonCanonicalIntervals.Polynomial 1 1 := .atom (.var 1)

/-- Both sides have one ambient and one local slot. Only the classification
of the actual occurrence changes; ambient top cannot be instantiated as bottom. -/
theorem captured_slot_cannot_be_generalized :
    ¬ CommonCanonicalIntervals.SubtypeFamilyEquivalent capturedSlot generalizedSlot := by
  intro same
  have localInstance : ∃ parameters : Fin 1 → Ty,
      Subtype (CommonCanonicalIntervals.instantiate generalizedSlot (fun _ => .top) parameters) .bottom :=
    ⟨fun _ => .bottom, Common.subtype_refl _⟩
  obtain ⟨parameters, below⟩ := (same (fun _ => .top) .bottom).mpr localInstance
  exact top_not_below_bottom below

/-- The captured slot is used in both the domain and result. The two local
slots occur positively, one of them at two distinct constructor leaves. -/
def capturedArrow : Form (1 + 2) :=
  .arrow 3 7 (.atom (.var 0))
    (.pair (.scalar (.union (.atom (.var 1)) (.atom (.var 2))))
      (.pair (.scalar (.atom (.var 1))) (.scalar (.atom (.var 0)))))

def capturedArrowLower : Form (1 + 0) :=
  .arrow 3 7 (.atom (.var 0))
    (.pair (.scalar .bottom) (.pair (.scalar .bottom) (.scalar (.atom (.var 0)))))

theorem capturedArrow_positive : CommonCanonicalPositive.Positive (fixed := 1) capturedArrow := by
  simp [capturedArrow, CommonCanonicalPositive.Positive,
    CommonCanonicalPositive.CapturedOnly, CommonCanonicalNames.occurrencesExpr]

theorem capturedArrowLower_positive : CommonCanonicalPositive.Positive (fixed := 1) capturedArrowLower := by
  simp [capturedArrowLower, CommonCanonicalPositive.Positive,
    CommonCanonicalPositive.CapturedOnly, CommonCanonicalNames.occurrencesExpr]

/-- A valid different-arity elimination with correlation retained: all row
assignments and every arbitrary captured common type are still quantified. -/
theorem positive_constructor_elimination_keeps_captured_sharing :
    CommonCanonicalPositive.FamilyEquivalent (fixed := 1) capturedArrow capturedArrowLower :=
  (CommonCanonicalPositive.canonicalEncoding_exact capturedArrow capturedArrowLower
    capturedArrow_positive capturedArrowLower_positive).mpr (by decide +kernel)

end Yulang.CommonCanonicalObstructions
