import Yulang.Binary64Rounding

/-!
# Exact binary64 overflow boundary for nearest/ties-even rounding

The magnitude grid extends the finite format to the next power of two. This
is a virtual exact real value, not a numerical distance assigned to infinity.
At the midpoint between the largest finite value and that next value, the
even significand is the latter. Hence source decimal conversion succeeds
strictly below the midpoint and reports static overflow at or above it.

The characterization below quantifies over the independent global nearest-
even relation on that grid. It also covers magnitudes larger than the search
sentinel: no finite grid point can be the rounded result there.
-/

namespace Yulang.Binary64Overflow

open Binary64Rounding

/-- Exactly the magnitudes whose unbounded nearest-even result is finite.
The rational magnitude is `numerator / denominator` in subnormal units. -/
def FiniteRounding (numerator denominator : Nat) : Prop :=
  2 * numerator < (maxUnits + magnitude finiteLimit) * denominator

instance (n d : Nat) : Decidable (FiniteRounding n d) :=
  inferInstanceAs (Decidable (_ < _))

/-- A finite result must minimize distance on the extended grid, rather than
only among the finite bit patterns. This distinction detects overflow. -/
def Rounds (negative : Bool) (numerator denominator : Nat) (value : Binary64.Value) : Prop :=
  value.negative = negative ∧ Binary64.IsFinite value ∧
    NearestEven (fun index => magnitude index * denominator) numerator (rank value)

/-- Half an ulp above the largest finite magnitude. The scale is `2^-1074`,
so this is the exact real boundary `2^1024 - 2^970`. -/
def midpointUnits : Nat := maxUnits + 2 ^ 2044

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 4096 in
theorem midpoint_twice : 2 * midpointUnits = maxUnits + magnitude finiteLimit := by decide

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 4096 in
theorem midpoint_units : midpointUnits = 2 ^ 2098 - 2 ^ 2044 := by decide

theorem finiteRounding_iff_below_midpoint (numerator denominator : Nat) :
    FiniteRounding numerator denominator ↔ numerator < midpointUnits * denominator := by
  unfold FiniteRounding
  rw [← midpoint_twice, Nat.mul_assoc]
  omega

theorem midpoint_overflows (denominator : Nat) :
    ¬ FiniteRounding (midpointUnits * denominator) denominator := by
  rw [finiteRounding_iff_below_midpoint]
  omega

theorem nearest_ge_bound (grid : Nat → Nat)
    (strict : ∀ a b, a < b → grid a < grid b) (target result bound : Nat)
    (rounded : NearestEven grid target result) (lower : grid bound ≤ target) :
    bound ≤ result := by
  by_cases enough : bound ≤ result
  · exact enough
  have less := strict result bound (by omega)
  have best := rounded.1 bound
  unfold distance at best
  omega

/-- The boundary rank is even, so the midpoint itself belongs to the upper
side. This lemma does not assume a particular search implementation. -/
theorem nearest_below_even_boundary_iff (grid : Nat → Nat)
    (strict : ∀ a b, a < b → grid a < grid b) (target result boundary : Nat)
    (positive : 0 < boundary) (even : boundary % 2 = 0)
    (rounded : NearestEven grid target result) :
    result < boundary ↔ 2 * target < grid (boundary - 1) + grid boundary := by
  have adjacent := strict (boundary - 1) boundary (by omega)
  constructor
  · intro finite
    by_cases below : 2 * target < grid (boundary - 1) + grid boundary
    · exact below
    have best := rounded.1 boundary
    by_cases earlier : result < boundary - 1
    · have earlierGrid := strict result (boundary - 1) earlier
      unfold distance at best
      omega
    · have last : result = boundary - 1 := by omega
      have equal : distance target (grid boundary) = distance target (grid result) := by
        rw [last] at best ⊢
        unfold distance at best ⊢
        omega
      have parity := rounded.2 boundary (by omega) equal
      omega
  · intro below
    by_cases finite : result < boundary
    · exact finite
    have upper : grid boundary ≤ grid result := by
      rcases Nat.eq_or_lt_of_le (by omega : boundary ≤ result) with same | less
      · exact same ▸ Nat.le_refl _
      · exact Nat.le_of_lt (strict boundary result less)
    have best := rounded.1 (boundary - 1)
    unfold distance at best
    omega

theorem finiteRounding_upper (numerator denominator : Nat) (positive : 0 < denominator)
    (finite : FiniteRounding numerator denominator) :
    numerator < magnitude finiteLimit * denominator := by
  have adjacent := weighted_strict denominator positive (finiteLimit - 1) finiteLimit (by decide)
  unfold FiniteRounding maxUnits at finite
  rw [Nat.add_mul] at finite
  omega

theorem inFiniteRange_implies (numerator denominator : Nat) (positive : 0 < denominator)
    (within : InFiniteRange numerator denominator) : FiniteRounding numerator denominator := by
  have adjacent := weighted_strict denominator positive (finiteLimit - 1) finiteLimit (by decide)
  unfold InFiniteRange maxUnits at within
  unfold FiniteRounding maxUnits
  rw [Nat.add_mul]
  omega

theorem roundedRank_correct (numerator denominator : Nat) (positive : 0 < denominator)
    (finite : FiniteRounding numerator denominator) :
    NearestEven (fun index => magnitude index * denominator) numerator
      (Binary64Rounding.roundedRank numerator denominator) := by
  apply roundBracket_correct _ (weighted_strict denominator positive)
  · decide
  · simp [magnitude]
  · exact finiteRounding_upper numerator denominator positive finite

theorem nearest_finite_iff (numerator denominator result : Nat) (positive : 0 < denominator)
    (rounded : NearestEven (fun index => magnitude index * denominator) numerator result) :
    result < finiteLimit ↔ FiniteRounding numerator denominator := by
  have boundary := nearest_below_even_boundary_iff _ (weighted_strict denominator positive)
    numerator result finiteLimit (by decide) (by decide) rounded
  simpa only [FiniteRounding, maxUnits, Nat.add_mul] using boundary

theorem midpoint_rounds_to_sentinel (denominator : Nat) (positive : 0 < denominator) :
    NearestEven (fun index => magnitude index * denominator)
      (midpointUnits * denominator) finiteLimit := by
  have adjacent := weighted_strict denominator positive (finiteLimit - 1) finiteLimit (by decide)
  have midpoint := congrArg (fun value => value * denominator) midpoint_twice
  simp only [Nat.add_mul, Nat.mul_assoc, maxUnits] at midpoint
  let result := nearest (fun index => magnitude index * denominator)
    (midpointUnits * denominator) (finiteLimit - 1)
  have limitPositive : 0 < finiteLimit := by decide
  have successor : finiteLimit - 1 + 1 = finiteLimit := by omega
  have rounded : NearestEven (fun index => magnitude index * denominator)
      (midpointUnits * denominator) result :=
    nearest_correct _ (weighted_strict denominator positive) _ _ (by omega) (by rw [successor]; omega)
  have endpoints := nearest_endpoints (fun index => magnitude index * denominator)
    (midpointUnits * denominator) (finiteLimit - 1)
  have outside : ¬ result < finiteLimit := by
    intro finite
    exact midpoint_overflows denominator
      ((nearest_finite_iff _ denominator result positive rounded).mp finite)
  have same : result = finiteLimit := by dsimp only [result] at outside ⊢; omega
  simpa only [same] using rounded

theorem roundedRank_finite (numerator denominator : Nat) (positive : 0 < denominator)
    (finite : FiniteRounding numerator denominator) :
    Binary64Rounding.roundedRank numerator denominator < finiteLimit :=
  (nearest_finite_iff numerator denominator _ positive
    (roundedRank_correct numerator denominator positive finite)).mpr finite

/-- This is an exact characterization for every positive-denominator rational,
including values beyond the upper search sentinel. -/
theorem finiteRounding_iff_exists_nearest (numerator denominator : Nat) (positive : 0 < denominator) :
    FiniteRounding numerator denominator ↔
      ∃ result, result < finiteLimit ∧
        NearestEven (fun index => magnitude index * denominator) numerator result := by
  constructor
  · intro finite
    exact ⟨_, roundedRank_finite numerator denominator positive finite,
      roundedRank_correct numerator denominator positive finite⟩
  · rintro ⟨result, finite, rounded⟩
    exact (nearest_finite_iff numerator denominator result positive rounded).mp finite

def round (negative : Bool) (numerator denominator : Nat) (positive : 0 < denominator)
    (finite : FiniteRounding numerator denominator) : Binary64.Value :=
  ofFiniteRank negative ⟨Binary64Rounding.roundedRank numerator denominator,
    roundedRank_finite numerator denominator positive finite⟩

theorem round_correct (negative : Bool) (numerator denominator : Nat) (positive : 0 < denominator)
    (finite : FiniteRounding numerator denominator) :
    Rounds negative numerator denominator (round negative numerator denominator positive finite) := by
  refine ⟨rfl, ofFiniteRank_finite _ _, ?_⟩
  simpa only [round, rank_ofFiniteRank] using roundedRank_correct numerator denominator positive finite

theorem Rounds.finite_contract (negative : Bool) (numerator denominator : Nat) (value : Binary64.Value)
    (rounded : Rounds negative numerator denominator value) :
    RoundsToEven negative numerator denominator value := by
  refine ⟨rounded.1, rounded.2.1, ?_, ?_⟩
  · intro candidate _
    simpa only [magnitude_rank] using rounded.2.2.1 (rank candidate)
  · intro candidate _ different tied
    have tie : distance numerator (magnitude (rank candidate) * denominator) =
        distance numerator (magnitude (rank value) * denominator) := by
      simpa only [magnitude_rank] using tied
    simpa only [rank_parity] using rounded.2.2.2 (rank candidate) different tie

theorem finiteRounding_iff_exists_value (negative : Bool) (numerator denominator : Nat)
    (positive : 0 < denominator) :
    FiniteRounding numerator denominator ↔ ∃ value, Rounds negative numerator denominator value := by
  constructor
  · intro finite
    exact ⟨_, round_correct negative numerator denominator positive finite⟩
  · rintro ⟨value, _, finite, rounded⟩
    exact (nearest_finite_iff numerator denominator _ positive rounded).mp (rank_lt value finite)

theorem round_agrees_with_finite (negative : Bool) (numerator denominator : Nat)
    (positive : 0 < denominator) (within : InFiniteRange numerator denominator) :
    round negative numerator denominator positive (inFiniteRange_implies numerator denominator positive within) =
      roundFinite negative numerator denominator positive within := rfl

def largestFinite (negative : Bool) : Binary64.Value :=
  ofFiniteRank negative ⟨finiteLimit - 1, by decide⟩

theorem largestFinite_word (negative : Bool) :
    (Binary64.toWord (largestFinite negative)).val =
      (if negative then 2 ^ 63 else 0) + 0x7fefffffffffffff := by
  cases negative <;> decide

theorem round_above_max (negative : Bool) (numerator denominator : Nat) (positive : 0 < denominator)
    (finite : FiniteRounding numerator denominator) (above : maxUnits * denominator ≤ numerator) :
    round negative numerator denominator positive finite = largestFinite negative := by
  have lower := nearest_ge_bound _ (weighted_strict denominator positive) numerator
    (Binary64Rounding.roundedRank numerator denominator) (finiteLimit - 1)
    (roundedRank_correct numerator denominator positive finite) above
  have upper := roundedRank_finite numerator denominator positive finite
  have same : Binary64Rounding.roundedRank numerator denominator = finiteLimit - 1 := by omega
  unfold round largestFinite
  congr 1
  exact Fin.ext same

end Yulang.Binary64Overflow
