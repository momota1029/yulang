import Yulang.SemilinearDecisions

/-!
# Finite signed-binary words cover every integer vector

Each letter denotes one vector in `{-1, 0, 1}^n`. Words are read least
significant digit first. Trailing zeros are permitted and have their ordinary
meaning. Every integer vector has a finite word: signed halving strictly
decreases the sum of the coordinates' absolute values until it reaches zero.
-/

namespace Yulang.SemilinearDigits

open SemilinearWeights BinaryCarries

variable {n : Nat}

abbrev Letter (n : Nat) := Fin (SemilinearDecisions.box 1 n).length

def digit (letter : Letter n) : Weight n := (SemilinearDecisions.box 1 n).get letter

theorem digit_bounded (letter : Letter n) : Within 1 (digit letter) :=
  (SemilinearDecisions.box_exact _ _).mp (List.get_mem _ letter)

theorem digit_complete (weight : Weight n) (bounded : Within 1 weight) :
    ∃ letter, digit letter = weight :=
  List.get_of_mem ((SemilinearDecisions.box_exact _ weight).mpr bounded)

def value : List (Letter n) → Weight n
  | [] => zero
  | letter :: rest => add (digit letter) (scale 2 (value rest))

def half (weight : Weight n) : Weight n := fun coordinate =>
  if 0 ≤ weight coordinate then Int.ofNat ((weight coordinate).natAbs / 2)
  else -(Int.ofNat ((weight coordinate).natAbs / 2))

theorem half_abs (weight : Weight n) (coordinate : Fin n) :
    (half weight coordinate).natAbs = (weight coordinate).natAbs / 2 := by
  simp only [half]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_ofNat']

theorem half_norm (weight : Weight n) :
    norm (half weight) =
      ((List.ofFn fun coordinate => (weight coordinate).natAbs).map (fun count => count / 2)).sum := by
  simp [norm, half_abs, List.map_ofFn, Function.comp_def]

theorem half_decreases (weight : Weight n) (positive : 0 < norm weight) :
    norm (half weight) < norm weight := by
  rw [half_norm]
  exact halved_sum_lt _ positive

def remainder (weight : Weight n) : Weight n :=
  SemilinearDecisions.subtract weight (scale 2 (half weight))

theorem remainder_bounded (weight : Weight n) : Within 1 (remainder weight) := by
  intro coordinate
  simp only [remainder, SemilinearDecisions.subtract, scale, half, Int.ofNat_eq_natCast]
  split
  next nonnegative =>
    have absolute := Int.eq_natAbs_of_nonneg nonnegative
    omega
  next negative =>
    have absolute := Int.eq_neg_natAbs_of_nonpos (by omega : weight coordinate ≤ 0)
    omega

theorem remainder_split (weight : Weight n) :
    add (remainder weight) (scale 2 (half weight)) = weight := by
  funext coordinate
  simp [remainder, SemilinearDecisions.subtract, add]

theorem norm_zero (weight : Weight n) (empty : norm weight = 0) : weight = zero := by
  funext coordinate
  have bound := coordinate_le_norm weight coordinate
  have absolute : (weight coordinate).natAbs = 0 := by omega
  exact Int.natAbs_eq_zero.mp absolute

/-- Every integer vector, with arbitrary signs and magnitudes, has a finite
encoding over the same finite alphabet used by the semilinear automata. -/
theorem value_surjective (weight : Weight n) : ∃ word : List (Letter n), value word = weight := by
  by_cases empty : norm weight = 0
  · exact ⟨[], (norm_zero weight empty).symm⟩
  · obtain ⟨letter, chosen⟩ := digit_complete (remainder weight) (remainder_bounded weight)
    obtain ⟨word, represented⟩ := value_surjective (half weight)
    refine ⟨letter :: word, ?_⟩
    simp only [value, chosen, represented]
    exact remainder_split weight
termination_by norm weight
decreasing_by exact half_decreases weight (by omega)

end Yulang.SemilinearDigits
