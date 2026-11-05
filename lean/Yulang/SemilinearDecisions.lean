import Yulang.BinaryCarries
import Yulang.FiniteBooleanReachability
import Yulang.SemilinearNormalization

/-!
# Total membership decisions for finite semilinear integer sets

For arbitrary signed generators, the natural coefficients of a linear
combination are read one binary digit at a time. A transition has the exact
equation `current = digit + 2 * next`, where `digit` selects each generator at
most once. Every carry coordinate lies in a finite box derived from the input
and generators. This is a bound on a finite automaton's states, not a bound on
coefficients, digits, graph path lengths, or recursive-row unfoldings.

Finite matrix reachability therefore decides membership completely, including
zero generators, mixed signs, cancellation, zero dimensions and empty input.
The final theorems refer directly to `SemilinearWeights.Span` and `Meaning`.
This module does not yet decide containment/equality of two semilinear sets.
-/

namespace Yulang.SemilinearDecisions

open SemilinearWeights BinaryCarries
open FiniteBooleanReachability (Path)

variable {n : Nat}

/-- All integer vectors inside the specified closed coordinate box. -/
def box (bound : Nat) : (dimension : Nat) → List (Weight dimension)
  | 0 => [fun coordinate => Fin.elim0 coordinate]
  | dimension + 1 => (List.range (2 * bound + 1)).flatMap fun head =>
      (box bound dimension).map (Fin.cases ((head : Int) - bound))

theorem box_exact (bound : Nat) (weight : Weight n) :
    weight ∈ box bound n ↔ Within bound weight := by
  induction n with
  | zero =>
      have unique : weight = fun coordinate => Fin.elim0 coordinate := by
        funext coordinate
        exact Fin.elim0 coordinate
      simp [box, unique, Within]
  | succ dimension ih =>
      constructor
      · intro member
        obtain ⟨head, inRange, tailMember⟩ := List.mem_flatMap.mp member
        obtain ⟨tail, tailPresent, rfl⟩ := List.mem_map.mp tailMember
        have rangeBound := List.mem_range.mp inRange
        have tailBound := (ih tail).mp tailPresent
        intro coordinate
        refine Fin.cases ?_ (fun index => ?_) coordinate
        · simp only [Fin.cases_zero]
          omega
        · simpa using tailBound index
      · intro bounded
        have first := bounded 0
        have firstNonnegative : 0 ≤ weight 0 + (bound : Int) := by omega
        have cast : ((weight 0 + (bound : Int)).toNat : Int) = weight 0 + bound :=
          Int.toNat_of_nonneg firstNonnegative
        apply List.mem_flatMap.mpr
        refine ⟨(weight 0 + (bound : Int)).toNat, List.mem_range.mpr (by omega), ?_⟩
        apply List.mem_map.mpr
        refine ⟨fun coordinate => weight coordinate.succ,
          (ih _).mpr (fun coordinate => bounded coordinate.succ), ?_⟩
        funext coordinate
        refine Fin.cases ?_ (fun index => ?_) coordinate
        · simp only [Fin.cases_zero]
          omega
        · rfl

/-- The bit pattern is finite, and each edge compares all coordinates. -/
def edge (generators : List (Weight n)) (values : List (Weight n))
    (source target : Fin values.length) : Bool :=
  (digits generators).any fun digit =>
    decide (∀ coordinate, (values.get source) coordinate =
      digit coordinate + 2 * (values.get target) coordinate)

theorem edge_exact (generators : List (Weight n)) (values : List (Weight n))
    (source target : Fin values.length) : edge generators values source target = true ↔
      ∃ digit ∈ digits generators,
        values.get source = add digit (scale 2 (values.get target)) := by
  simp only [edge, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨digit, selected, equality⟩
    exact ⟨digit, selected, funext equality⟩
  · rintro ⟨digit, selected, equality⟩
    exact ⟨digit, selected, congrFun equality⟩

theorem path_sound (generators : List (Weight n)) (values : List (Weight n))
    {source target : Fin values.length} (path : Path (edge generators values) source target)
    (last : Span generators (values.get target)) : Span generators (values.get source) := by
  induction path with
  | nil => exact last
  | @cons source middle target step rest ih =>
      obtain ⟨digit, selected, equality⟩ := (edge_exact generators values source middle).mp step
      rw [equality]
      exact (digit_span generators digit selected).append
        (scale_span generators 2 _ (ih last))

/-- Repeated halving of every coefficient constructs a path in any finite
enumeration containing the carry box. Its recursion decreases the coefficient
sum; it is not an input to the decision algorithm. -/
theorem coefficients_path (generators : List (Weight n)) (bound : Nat)
    (large : budget generators ≤ bound) (values : List (Weight n))
    (complete : ∀ weight, Within bound weight → ∃ index, values.get index = weight)
    (target : Fin values.length) (atZero : values.get target = zero)
    (counts : List Nat) (length : counts.length = generators.length)
    (source : Fin values.length) (current : values.get source = combine generators counts)
    (bounded : Within bound (values.get source)) : Path (edge generators values) source target := by
  by_cases empty : counts.sum = 0
  · have atStart : values.get source = zero := current.trans (combine_sum_zero generators counts empty)
    apply Path.cons (middle := target) ?_ (.nil target)
    apply (edge_exact generators values source target).mpr
    refine ⟨zero, zero_digit generators, ?_⟩
    rw [atStart, atZero]
    funext coordinate
    simp [zero, add, scale]
  · let nextCounts := counts.map (fun count => count / 2)
    let digit := combine generators (counts.map (fun count => count % 2))
    have chosen : digit ∈ digits generators := coefficient_digit generators counts length
    have step : values.get source = add digit (scale 2 (combine generators nextCounts)) :=
      current.trans (coefficient_split generators counts)
    have nextBound : Within bound (combine generators nextCounts) :=
      step_bounded generators bound large _ digit _ bounded chosen step
    obtain ⟨next, nextValue⟩ := complete _ nextBound
    apply Path.cons (middle := next)
    · apply (edge_exact generators values source next).mpr
      exact ⟨digit, chosen, by rw [nextValue]; exact step⟩
    · exact coefficients_path generators bound large values complete target atZero
        nextCounts (by simp [nextCounts, length]) next nextValue
        (by rw [nextValue]; exact nextBound)
termination_by counts.sum
decreasing_by exact halved_sum_lt counts (by omega)

def carryBound (generators : List (Weight n)) (weight : Weight n) : Nat :=
  max (norm weight) (budget generators)

def states (generators : List (Weight n)) (weight : Weight n) : List (Weight n) :=
  weight :: zero :: box (carryBound generators weight) n

def first (generators : List (Weight n)) (weight : Weight n) : Fin (states generators weight).length :=
  ⟨0, by simp [states]⟩

def last (generators : List (Weight n)) (weight : Weight n) : Fin (states generators weight).length :=
  ⟨1, by simp [states]⟩

@[simp] theorem first_value (generators : List (Weight n)) (weight : Weight n) :
    (states generators weight).get (first generators weight) = weight := rfl

@[simp] theorem last_value (generators : List (Weight n)) (weight : Weight n) :
    (states generators weight).get (last generators weight) = zero := rfl

theorem states_complete (generators : List (Weight n)) (weight candidate : Weight n)
    (bounded : Within (carryBound generators weight) candidate) :
    ∃ index, (states generators weight).get index = candidate := by
  apply List.get_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  exact (box_exact _ candidate).mpr bounded

def checkSpanRaw (generators : List (Weight n)) (weight : Weight n) : Bool :=
  FiniteBooleanReachability.entry
    (FiniteBooleanReachability.closure (edge generators (states generators weight)))
    (first generators weight) (last generators weight)

/-- Arbitrary natural coefficients are decided by a finite binary-carry graph.
No positivity, linear independence, pointedness or input bound is assumed. -/
theorem checkSpanRaw_exact (generators : List (Weight n)) (weight : Weight n) :
    checkSpanRaw generators weight = true ↔ Span generators weight := by
  rw [checkSpanRaw, FiniteBooleanReachability.closure_exact]
  constructor
  · intro path
    have ending : Span generators ((states generators weight).get (last generators weight)) := by
      rw [last_value]
      exact .nil
    simpa only [first_value] using path_sound generators (states generators weight) path ending
  · intro member
    obtain ⟨counts, length, equality⟩ := span_coefficients generators weight member
    exact coefficients_path generators (carryBound generators weight)
      (Nat.le_max_right _ _) (states generators weight) (states_complete generators weight)
      (last generators weight) (last_value generators weight) counts length
      (first generators weight) (by rw [first_value, equality])
      (by rw [first_value]; exact (within_norm weight).mono (Nat.le_max_left _ _))

/-- Redundant periods are removed before constructing the carry box or digit
alphabet, not just from a display of the resulting automaton. -/
def checkSpan (generators : List (Weight n)) (weight : Weight n) : Bool :=
  checkSpanRaw (SemilinearNormalization.periods generators) weight

theorem checkSpan_exact (generators : List (Weight n)) (weight : Weight n) :
    checkSpan generators weight = true ↔ Span generators weight :=
  (checkSpanRaw_exact _ weight).trans (SemilinearNormalization.span_exact generators weight)

theorem checkSpan_preserves_result (generators : List (Weight n)) (weight : Weight n) :
    checkSpan generators weight = checkSpanRaw generators weight := by
  have same := (checkSpan_exact generators weight).trans (checkSpanRaw_exact generators weight).symm
  cases left : checkSpan generators weight <;> cases right : checkSpanRaw generators weight <;> simp_all

def subtract (weight base : Weight n) : Weight n := fun coordinate => weight coordinate - base coordinate

theorem linear_iff_span (line : Linear n) (weight : Weight n) :
    line.Holds weight ↔ Span line.periods (subtract weight line.base) := by
  constructor
  · rintro ⟨offset, member, total⟩
    have equal : subtract weight line.base = offset := by
      funext coordinate
      have point := congrFun total coordinate
      simp only [add, subtract] at *
      omega
    rw [equal]
    exact member
  · intro member
    refine ⟨subtract weight line.base, member, ?_⟩
    funext coordinate
    simp only [subtract, add]
    omega

def checkLinear (line : Linear n) (weight : Weight n) : Bool :=
  checkSpan line.periods (subtract weight line.base)

theorem checkLinear_exact (line : Linear n) (weight : Weight n) :
    checkLinear line weight = true ↔ line.Holds weight :=
  (checkSpan_exact line.periods _).trans (linear_iff_span line weight).symm

def check (semi : Semi n) (weight : Weight n) : Bool :=
  (SemilinearNormalization.normalize semi).any fun line => checkLinear line weight

/-- Total executable membership for every finite semilinear integer set. -/
theorem check_exact (semi : Semi n) (weight : Weight n) :
    check semi weight = true ↔ Meaning semi weight := by
  simp only [check, List.any_eq_true, checkLinear_exact]
  exact SemilinearNormalization.normalize_exact semi weight

theorem check_rejects (semi : Semi n) (weight : Weight n) :
    check semi weight = false ↔ ¬ Meaning semi weight := by
  rw [← check_exact]
  cases check semi weight <;> simp

end Yulang.SemilinearDecisions
