import Yulang.Binary64

/-!
# Exact nearest-even rounding on the binary64 magnitude grid

The ordered magnitude grid is indexed by the exponent/fraction word without
the sign. A binary search finds adjacent grid points; exact integer distances
then select the nearest, with an even low fraction bit at a midpoint. The
search decreases its interval, so it has no user-provided fuel or depth cap.

The generic search and rounding lemmas below use independent inequalities and
global distance minimization. They do not assume success of a float converter.
-/

namespace Yulang.Binary64Rounding

/-- Absolute distance on natural-number numerators. -/
def distance (a b : Nat) : Nat := (a - b) + (b - a)

/-- Search a half-open bracket, retaining its lower endpoint. -/
def floorSearch (grid : Nat → Nat) (target lo hi : Nat) : Nat :=
  if gap : lo + 1 < hi then
    let mid := (lo + hi) / 2
    if grid mid ≤ target then floorSearch grid target mid hi
    else floorSearch grid target lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

theorem floorSearch_spec (grid : Nat → Nat) (target lo hi : Nat)
    (ordered : lo < hi) (lower : grid lo ≤ target) (upper : target < grid hi) :
    let result := floorSearch grid target lo hi
    lo ≤ result ∧ result < hi ∧ grid result ≤ target ∧ target < grid (result + 1) := by
  rw [floorSearch]
  split
  · rename_i gap
    dsimp only
    split
    · rename_i hit
      have ih := floorSearch_spec grid target ((lo + hi) / 2) hi (by omega) hit upper
      dsimp only at ih ⊢
      exact ⟨by omega, ih.2⟩
    · rename_i miss
      have ih := floorSearch_spec grid target lo ((lo + hi) / 2) (by omega) lower (by omega)
      dsimp only at ih ⊢
      exact ⟨ih.1, by omega, ih.2.2⟩
  · rename_i gap
    dsimp only
    have next : hi = lo + 1 := by omega
    exact ⟨Nat.le_refl _, ordered, lower, next ▸ upper⟩
termination_by hi - lo
decreasing_by all_goals omega

/-- The selected endpoint of an adjacent bracket. -/
def nearest (grid : Nat → Nat) (target lower : Nat) : Nat :=
  let left := distance target (grid lower)
  let right := distance target (grid (lower + 1))
  if left < right ∨ (left = right ∧ lower % 2 = 0) then lower else lower + 1

/-- Global closest-point correctness, with even rank when a distinct point
ties. In binary64 the rank parity is the fraction's low bit. -/
def NearestEven (grid : Nat → Nat) (target result : Nat) : Prop :=
  (∀ candidate, distance target (grid result) ≤ distance target (grid candidate)) ∧
  (∀ candidate, candidate ≠ result →
    distance target (grid candidate) = distance target (grid result) → result % 2 = 0)

theorem nearest_endpoints (grid : Nat → Nat) (target lower : Nat) :
    nearest grid target lower = lower ∨ nearest grid target lower = lower + 1 := by
  unfold nearest
  dsimp only
  split <;> simp_all

theorem nearest_correct (grid : Nat → Nat) (strict : ∀ a b, a < b → grid a < grid b)
    (target lower : Nat) (left : grid lower ≤ target) (right : target < grid (lower + 1)) :
    NearestEven grid target (nearest grid target lower) := by
  have monotone (a b : Nat) (ordered : a ≤ b) : grid a ≤ grid b := by
    rcases Nat.lt_or_eq_of_le ordered with smaller | same
    · exact Nat.le_of_lt (strict a b smaller)
    · exact same ▸ Nat.le_refl _
  unfold nearest NearestEven
  dsimp only
  split
  · rename_i choose
    constructor
    · intro candidate
      by_cases before : candidate ≤ lower
      · have below := monotone candidate lower before
        unfold distance
        omega
      · have above := monotone (lower + 1) candidate (by omega)
        unfold distance at choose ⊢
        omega
    · intro candidate different tied
      by_cases before : candidate < lower
      · have below := strict candidate lower before
        unfold distance at tied
        omega
      · have above := monotone (lower + 1) candidate (by omega)
        unfold distance at choose tied
        omega
  · rename_i choose
    constructor
    · intro candidate
      by_cases after : lower + 1 ≤ candidate
      · have above := monotone (lower + 1) candidate after
        unfold distance
        omega
      · have below := monotone candidate lower (by omega)
        unfold distance at choose ⊢
        omega
    · intro candidate different tied
      by_cases after : lower + 1 < candidate
      · have above := strict (lower + 1) candidate after
        unfold distance at tied
        omega
      · have below := monotone candidate lower (by omega)
        have parity := Nat.mod_lt lower (by decide : 0 < 2)
        unfold distance at choose tied
        omega

def roundBracket (grid : Nat → Nat) (target lo hi : Nat) : Nat :=
  nearest grid target (floorSearch grid target lo hi)

theorem roundBracket_correct (grid : Nat → Nat)
    (strict : ∀ a b, a < b → grid a < grid b) (target lo hi : Nat)
    (ordered : lo < hi) (lower : grid lo ≤ target) (upper : target < grid hi) :
    NearestEven grid target (roundBracket grid target lo hi) := by
  have bracket := floorSearch_spec grid target lo hi ordered lower upper
  exact nearest_correct grid strict target _ bracket.2.2.1 bracket.2.2.2

theorem NearestEven.le_bound (grid : Nat → Nat)
    (strict : ∀ a b, a < b → grid a < grid b) (target result bound : Nat)
    (rounded : NearestEven grid target result) (upper : target ≤ grid bound) :
    result ≤ bound := by
  by_cases beyond : result ≤ bound
  · exact beyond
  have further := strict bound result (by omega)
  have best := rounded.1 bound
  unfold distance at best
  omega

/-- Exact finite binary64 magnitudes, extended beyond exponent 2046 only to
provide an upper search sentinel. No extended exponent is stored as a value. -/
def magnitude (rank : Nat) : Nat :=
  let exponent := rank / 2 ^ 52
  let fraction := rank % 2 ^ 52
  if exponent = 0 then fraction
  else (2 ^ 52 + fraction) * 2 ^ (exponent - 1)

theorem magnitude_strict (a b : Nat) (ordered : a < b) : magnitude a < magnitude b := by
  have fa := Nat.mod_lt a (by decide : 0 < 2 ^ 52)
  have fb := Nat.mod_lt b (by decide : 0 < 2 ^ 52)
  have ea := Nat.div_add_mod a (2 ^ 52)
  have eb := Nat.div_add_mod b (2 ^ 52)
  have expOrder : a / 2 ^ 52 ≤ b / 2 ^ 52 := Nat.div_le_div_right (Nat.le_of_lt ordered)
  unfold magnitude
  dsimp only
  by_cases same : a / 2 ^ 52 = b / 2 ^ 52
  · have fractions : a % 2 ^ 52 < b % 2 ^ 52 := by omega
    rw [same]
    split
    · exact fractions
    · apply Nat.mul_lt_mul_of_pos_right
      · omega
      · exact Nat.pow_pos (by decide)
  · have expLess : a / 2 ^ 52 < b / 2 ^ 52 := by omega
    have bNonzero : b / 2 ^ 52 ≠ 0 := by omega
    simp only [bNonzero, ite_false]
    split
    · have positive : 1 ≤ 2 ^ (b / 2 ^ 52 - 1) := Nat.pow_pos (by decide)
      have below := Nat.mul_le_mul_left (2 ^ 52 + b % 2 ^ 52) positive
      omega
    · rename_i aNonzero
      have bound : 2 ^ 52 + a % 2 ^ 52 < 2 ^ 52 * 2 := by omega
      have step := Nat.mul_lt_mul_of_pos_right bound (Nat.pow_pos (by decide : 0 < 2)
        (n := a / 2 ^ 52 - 1))
      have powers : 2 ^ (a / 2 ^ 52) ≤ 2 ^ (b / 2 ^ 52 - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have next := Nat.mul_le_mul_left (2 ^ 52) powers
      have payload := Nat.mul_le_mul_right (2 ^ (b / 2 ^ 52 - 1))
        (Nat.le_add_right (2 ^ 52) (b % 2 ^ 52))
      have ae : a / 2 ^ 52 - 1 + 1 = a / 2 ^ 52 := by omega
      have apow : 2 * 2 ^ (a / 2 ^ 52 - 1) = 2 ^ (a / 2 ^ 52) := by
        calc
          2 * 2 ^ (a / 2 ^ 52 - 1) = 2 ^ (a / 2 ^ 52 - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (a / 2 ^ 52 - 1 + 1) := (Nat.pow_succ 2 _).symm
          _ = 2 ^ (a / 2 ^ 52) := congrArg (fun e => 2 ^ e) ae
      calc
        (2 ^ 52 + a % 2 ^ 52) * 2 ^ (a / 2 ^ 52 - 1)
          < (2 ^ 52 * 2) * 2 ^ (a / 2 ^ 52 - 1) := step
        _ = 2 ^ 52 * 2 ^ (a / 2 ^ 52) := by rw [Nat.mul_assoc, apow]
        _ ≤ 2 ^ 52 * 2 ^ (b / 2 ^ 52 - 1) := next
        _ ≤ (2 ^ 52 + b % 2 ^ 52) * 2 ^ (b / 2 ^ 52 - 1) := payload

def finiteLimit : Nat := 2047 * 2 ^ 52

/-- Construct a finite bit pattern from its unsigned exponent/fraction rank. -/
def ofFiniteRank (negative : Bool) (rank : Fin finiteLimit) : Binary64.Value where
  negative := negative
  exponent := ⟨rank.val / 2 ^ 52, by
    have h := rank.isLt
    unfold finiteLimit at h
    omega⟩
  fraction := ⟨rank.val % 2 ^ 52, Nat.mod_lt _ (by decide)⟩

def rank (value : Binary64.Value) : Nat := value.exponent.val * 2 ^ 52 + value.fraction.val

theorem rank_lt (value : Binary64.Value) (finite : Binary64.IsFinite value) :
    rank value < finiteLimit := by
  have fraction := value.fraction.isLt
  unfold Binary64.IsFinite at finite
  unfold rank finiteLimit
  omega

@[simp] theorem rank_ofFiniteRank (negative : Bool) (index : Fin finiteLimit) :
    rank (ofFiniteRank negative index) = index.val := by
  simp only [rank, ofFiniteRank]
  omega

theorem ofFiniteRank_finite (negative : Bool) (index : Fin finiteLimit) :
    Binary64.IsFinite (ofFiniteRank negative index) := by
  have h := index.isLt
  unfold finiteLimit at h
  unfold Binary64.IsFinite ofFiniteRank
  dsimp only
  omega

@[simp] theorem units_ofFiniteRank (negative : Bool) (index : Fin finiteLimit) :
    Binary64.units (ofFiniteRank negative index) = magnitude index.val := rfl

theorem magnitude_rank (value : Binary64.Value) : magnitude (rank value) = Binary64.units value := by
  have fraction := value.fraction.isLt
  have div : rank value / 2 ^ 52 = value.exponent.val := by unfold rank; omega
  have mod : rank value % 2 ^ 52 = value.fraction.val := by unfold rank; omega
  simp only [magnitude, div, mod, Binary64.units]

theorem rank_parity (value : Binary64.Value) : rank value % 2 = value.fraction.val % 2 := by
  unfold rank
  omega

theorem ofFiniteRank_parity (negative : Bool) (index : Fin finiteLimit) :
    (ofFiniteRank negative index).fraction.val % 2 = index.val % 2 := by
  have same := rank_parity (ofFiniteRank negative index)
  simpa using same.symm

/-- The largest finite magnitude, in units of `2^-1074`. -/
def maxUnits : Nat := magnitude (finiteLimit - 1)

def InFiniteRange (numerator denominator : Nat) : Prop := numerator ≤ maxUnits * denominator

instance (n d : Nat) : Decidable (InFiniteRange n d) := inferInstanceAs (Decidable (_ ≤ _))

theorem weighted_strict (denominator : Nat) (positive : 0 < denominator) (a b : Nat)
    (ordered : a < b) : magnitude a * denominator < magnitude b * denominator :=
  Nat.mul_lt_mul_of_pos_right (magnitude_strict a b ordered) positive

theorem sentinel_upper (numerator denominator : Nat) (positive : 0 < denominator)
    (within : InFiniteRange numerator denominator) : numerator < magnitude finiteLimit * denominator := by
  have next := weighted_strict denominator positive (finiteLimit - 1) finiteLimit
    (by decide)
  exact Nat.lt_of_le_of_lt within next

def roundedRank (numerator denominator : Nat) : Nat :=
  roundBracket (fun index => magnitude index * denominator) numerator 0 finiteLimit

theorem roundedRank_correct (numerator denominator : Nat) (positive : 0 < denominator)
    (within : InFiniteRange numerator denominator) :
    NearestEven (fun index => magnitude index * denominator) numerator
      (roundedRank numerator denominator) := by
  apply roundBracket_correct _ (weighted_strict denominator positive)
  · decide
  · simp [magnitude]
  · exact sentinel_upper numerator denominator positive within

theorem roundedRank_finite (numerator denominator : Nat) (positive : 0 < denominator)
    (within : InFiniteRange numerator denominator) : roundedRank numerator denominator < finiteLimit := by
  have bounded := NearestEven.le_bound _ (weighted_strict denominator positive) numerator
    (roundedRank numerator denominator) (finiteLimit - 1)
    (roundedRank_correct numerator denominator positive within) within
  have limit : 0 < finiteLimit := by decide
  omega

def roundFinite (negative : Bool) (numerator denominator : Nat) (positive : 0 < denominator)
    (within : InFiniteRange numerator denominator) : Binary64.Value :=
  ofFiniteRank negative ⟨roundedRank numerator denominator,
    roundedRank_finite numerator denominator positive within⟩

/-- An independent rounding contract over all finite binary64 values. The
exact rational magnitude is `numerator / denominator` in subnormal units.
The sign is retained, including when rounding to zero. -/
def RoundsToEven (negative : Bool) (numerator denominator : Nat) (result : Binary64.Value) : Prop :=
  result.negative = negative ∧ Binary64.IsFinite result ∧
  (∀ candidate : Binary64.Value, Binary64.IsFinite candidate →
    distance numerator (Binary64.units result * denominator) ≤
      distance numerator (Binary64.units candidate * denominator)) ∧
  (∀ candidate : Binary64.Value, Binary64.IsFinite candidate →
    rank candidate ≠ rank result →
    distance numerator (Binary64.units candidate * denominator) =
      distance numerator (Binary64.units result * denominator) →
    result.fraction.val % 2 = 0)

theorem roundFinite_correct (negative : Bool) (numerator denominator : Nat)
    (positive : 0 < denominator) (within : InFiniteRange numerator denominator) :
    RoundsToEven negative numerator denominator (roundFinite negative numerator denominator positive within) := by
  let index : Fin finiteLimit := ⟨roundedRank numerator denominator,
    roundedRank_finite numerator denominator positive within⟩
  have nearest := roundedRank_correct numerator denominator positive within
  refine ⟨rfl, ofFiniteRank_finite negative index, ?_, ?_⟩
  · intro candidate _
    simpa only [roundFinite, units_ofFiniteRank, magnitude_rank] using nearest.1 (rank candidate)
  · intro candidate _ different tied
    have different' : rank candidate ≠ roundedRank numerator denominator := by
      simpa only [roundFinite, rank_ofFiniteRank] using different
    have tied' : distance numerator (magnitude (rank candidate) * denominator) =
        distance numerator (magnitude (roundedRank numerator denominator) * denominator) := by
      simpa only [roundFinite, units_ofFiniteRank, magnitude_rank] using tied
    simpa only [roundFinite, ofFiniteRank_parity] using nearest.2 (rank candidate) different' tied'

end Yulang.Binary64Rounding
