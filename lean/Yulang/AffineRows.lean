import Yulang.RecursiveRows

/-!
# Finite descriptions of unbounded signed occurrence rays

A ray stores one base occurrence and one integer vector. It denotes all
nonnegative repetitions of that vector, including negative and zero periods.
Membership is decided by at most one candidate per boundary coordinate plus
zero. Inclusion and equality of two rays are decided without enumerating their
possibly infinite support.

This module decides the sets defined by a base and one repeated vector. A
connection to a recursive problem's least solution is a separate theorem. It
does not claim that every guarded mutually recursive row problem is one ray or
that testing pairwise ray inclusion decides inclusion between unions of rays.
-/

namespace Yulang.AffineRows

open Directed

structure Ray (n : Nat) (Key : Type) where
  base : Occurrence n Key
  period : Fin n → Int

def Ray.point (ray : Ray n Key) (count : Nat) : Occurrence n Key :=
  ⟨ray.base.key, fun i => ray.base.weights i + (count : Int) * ray.period i⟩

def Ray.Holds (ray : Ray n Key) : RecursiveRows.SetRow n Key :=
  fun occurrence => ∃ count, ray.point count = occurrence

@[simp] theorem Ray.point_zero (ray : Ray n Key) : ray.point 0 = ray.base := by
  apply Occurrence.ext
  · rfl
  intro i
  simp [Ray.point]

def Ray.candidates (ray : Ray n Key) (occurrence : Occurrence n Key) : List Nat :=
  0 :: (List.finRange n).map
    (fun i => ((occurrence.weights i - ray.base.weights i) / ray.period i).toNat)

def Ray.check [DecidableEq Key] (ray : Ray n Key) (occurrence : Occurrence n Key) : Bool :=
  (ray.candidates occurrence).any (fun count => decide (ray.point count = occurrence))

theorem Ray.candidates_complete (ray : Ray n Key) (occurrence : Occurrence n Key)
    (member : ray.Holds occurrence) :
    ∃ count ∈ ray.candidates occurrence, ray.point count = occurrence := by
  obtain ⟨count, rfl⟩ := member
  by_cases zero : ∀ i, ray.period i = 0
  · refine ⟨0, by simp [Ray.candidates], ?_⟩
    apply Occurrence.ext
    · rfl
    intro i
    simp [Ray.point, zero i]
  · obtain ⟨i, nonzero⟩ := Classical.not_forall.mp zero
    refine ⟨count, List.mem_cons.mpr (Or.inr ?_), rfl⟩
    apply List.mem_map.mpr
    refine ⟨i, by simp, ?_⟩
    simp only [Ray.point]
    rw [show ray.base.weights i + (count : Int) * ray.period i - ray.base.weights i =
      (count : Int) * ray.period i by omega, Int.mul_ediv_cancel _ nonzero]
    simp

theorem Ray.check_exact [DecidableEq Key] (ray : Ray n Key) (occurrence : Occurrence n Key) :
    ray.check occurrence = true ↔ ray.Holds occurrence := by
  simp only [Ray.check, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨count, _, equality⟩ => ⟨count, equality⟩, ray.candidates_complete occurrence⟩

/-- A finite candidate can always be chosen no later than a given witness.
This also covers a constant ray, for which the canonical candidate is zero. -/
theorem Ray.bounded_candidate (ray : Ray n Key) (count : Nat) :
    ∃ candidate ∈ ray.candidates (ray.point count),
      ray.point candidate = ray.point count ∧ candidate ≤ count := by
  obtain ⟨candidate, member, equal⟩ := ray.candidates_complete (ray.point count) ⟨count, rfl⟩
  by_cases zero : ∀ i, ray.period i = 0
  · refine ⟨0, by simp [Ray.candidates], ?_, Nat.zero_le _⟩
    apply Occurrence.ext
    · rfl
    intro i
    simp [Ray.point, zero i]
  · obtain ⟨i, nonzero⟩ := Classical.not_forall.mp zero
    have h := congrFun (congrArg Occurrence.weights equal) i
    change ray.base.weights i + (candidate : Int) * ray.period i =
      ray.base.weights i + (count : Int) * ray.period i at h
    have mult : (candidate : Int) * ray.period i = (count : Int) * ray.period i := by omega
    have cast := Int.eq_of_mul_eq_mul_right nonzero mult
    exact ⟨candidate, member, equal, by omega⟩

def Ray.Subset (source target : Ray n Key) : Prop :=
  ∀ occurrence, source.Holds occurrence → target.Holds occurrence

/-- Two endpoints and nondecreasing target indices characterize containment.
The zero-period case is included; no nonzero-coordinate input is required. -/
def Ray.checkSubset [DecidableEq Key] (source target : Ray n Key) : Bool :=
  (target.candidates source.base).any fun first =>
    (target.candidates (source.point 1)).any fun next =>
      decide (target.point first = source.base ∧
        target.point next = source.point 1 ∧ first ≤ next)

theorem Ray.endpoints_period (source target : Ray n Key) (first next : Nat)
    (atZero : target.point first = source.base)
    (atOne : target.point next = source.point 1) (i : Fin n) :
    source.period i = ((next : Int) - (first : Int)) * target.period i := by
  have h0 := congrFun (congrArg Occurrence.weights atZero) i
  have h1 := congrFun (congrArg Occurrence.weights atOne) i
  simp only [Ray.point, Int.ofNat_one, Int.one_mul] at h0 h1
  rw [Int.sub_mul]
  omega

theorem Ray.endpoint_point (source target : Ray n Key) (first next count : Nat)
    (atZero : target.point first = source.base)
    (atOne : target.point next = source.point 1) :
    (source.point count).weights i = target.base.weights i +
      ((first : Int) + (count : Int) * ((next : Int) - (first : Int))) * target.period i := by
  have h0 := congrFun (congrArg Occurrence.weights atZero) i
  change target.base.weights i + (first : Int) * target.period i = source.base.weights i at h0
  simp only [Ray.point, source.endpoints_period target first next atZero atOne i,
    Int.mul_assoc, Int.add_mul]
  omega

theorem Ray.endpoints_sufficient (source target : Ray n Key) (first next : Nat)
    (atZero : target.point first = source.base)
    (atOne : target.point next = source.point 1) (ordered : first ≤ next) :
    source.Subset target := by
  rintro occurrence ⟨count, rfl⟩
  refine ⟨first + count * (next - first), ?_⟩
  apply Occurrence.ext
  · change target.base.key = source.base.key
    have keys := congrArg Occurrence.key atZero
    exact keys
  intro i
  rw [source.endpoint_point target first next count atZero atOne]
  simp only [Ray.point, Int.natCast_add, Int.natCast_mul, Int.ofNat_sub ordered]

theorem Ray.point_injective (ray : Ray n Key) (i : Fin n) (nonzero : ray.period i ≠ 0)
    {first next : Nat} (equal : ray.point first = ray.point next) : first = next := by
  have h := congrFun (congrArg Occurrence.weights equal) i
  change ray.base.weights i + (first : Int) * ray.period i =
    ray.base.weights i + (next : Int) * ray.period i at h
  have mult : (first : Int) * ray.period i = (next : Int) * ray.period i := by omega
  have cast := Int.eq_of_mul_eq_mul_right nonzero mult
  omega

theorem Ray.endpoints_necessary (source target : Ray n Key) (subset : source.Subset target) :
    ∃ first next, target.point first = source.base ∧
      target.point next = source.point 1 ∧ first ≤ next := by
  obtain ⟨first, atZero⟩ := subset source.base ⟨0, source.point_zero⟩
  obtain ⟨next, atOne⟩ := subset (source.point 1) ⟨1, rfl⟩
  by_cases zero : ∀ i, target.period i = 0
  · have same (count : Nat) : target.point count = target.point 0 := by
      apply Occurrence.ext
      · rfl
      intro i
      simp [Ray.point, zero i]
    exact ⟨0, 0, (same first).symm.trans atZero, (same next).symm.trans atOne, Nat.le_refl _⟩
  · obtain ⟨i, nonzero⟩ := Classical.not_forall.mp zero
    refine ⟨first, next, atZero, atOne, ?_⟩
    apply Classical.byContradiction
    intro notOrdered
    have negative : (next : Int) - (first : Int) ≤ -1 := by omega
    obtain ⟨far, atFar⟩ := subset (source.point (first + 1)) ⟨first + 1, rfl⟩
    have h := congrFun (congrArg Occurrence.weights atFar) i
    rw [source.endpoint_point target first next (first + 1) atZero atOne] at h
    change target.base.weights i + (far : Int) * target.period i = _ at h
    have mult : (far : Int) * target.period i =
        ((first : Int) + ((first + 1 : Nat) : Int) * ((next : Int) - (first : Int))) *
          target.period i := by omega
    have coeff := Int.eq_of_mul_eq_mul_right nonzero mult
    have bound := Int.mul_le_mul_of_nonneg_left negative
      (show (0 : Int) ≤ ((first + 1 : Nat) : Int) by omega)
    simp only [Int.mul_neg, Int.mul_one, Int.natCast_add, Int.ofNat_one] at bound coeff
    omega

theorem Ray.checkSubset_exact [DecidableEq Key] (source target : Ray n Key) :
    source.checkSubset target = true ↔ source.Subset target := by
  simp only [Ray.checkSubset, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨first, _, next, _, atZero, atOne, ordered⟩
    exact source.endpoints_sufficient target first next atZero atOne ordered
  · intro subset
    obtain ⟨first, next, atZero, atOne, ordered⟩ := source.endpoints_necessary target subset
    by_cases zero : ∀ i, target.period i = 0
    · have same (count : Nat) : target.point count = target.point 0 := by
        apply Occurrence.ext
        · rfl
        intro i
        simp [Ray.point, zero i]
      exact ⟨0, by simp [Ray.candidates], 0, by simp [Ray.candidates],
        (same first).symm.trans atZero, (same next).symm.trans atOne, Nat.le_refl _⟩
    · obtain ⟨i, nonzero⟩ := Classical.not_forall.mp zero
      obtain ⟨a, amem, aeq⟩ := target.candidates_complete source.base ⟨first, atZero⟩
      obtain ⟨b, bmem, beq⟩ := target.candidates_complete (source.point 1) ⟨next, atOne⟩
      have ha : a = first := target.point_injective i nonzero (aeq.trans atZero.symm)
      have hb : b = next := target.point_injective i nonzero (beq.trans atOne.symm)
      exact ⟨a, amem, b, bmem, aeq, beq, by omega⟩

def Ray.checkEqual [DecidableEq Key] (left right : Ray n Key) : Bool :=
  left.checkSubset right && right.checkSubset left

theorem Ray.checkEqual_exact [DecidableEq Key] (left right : Ray n Key) :
    left.checkEqual right = true ↔ ∀ occurrence, left.Holds occurrence ↔ right.Holds occurrence := by
  simp only [Ray.checkEqual, Bool.and_eq_true, Ray.checkSubset_exact]
  exact ⟨fun ⟨lr, rl⟩ occurrence => ⟨lr occurrence, rl occurrence⟩,
    fun same => ⟨fun occurrence => (same occurrence).mp, fun occurrence => (same occurrence).mpr⟩⟩

namespace Examples

def scalar (base period : Int) : Ray 1 Nat :=
  ⟨⟨0, fun _ => base⟩, fun _ => period⟩

theorem even_below_nonnegative : (scalar 0 2).checkSubset (scalar 0 1) = true := by decide
theorem nonnegative_not_below_even : (scalar 0 1).checkSubset (scalar 0 2) = false := by decide
theorem negative_period_accepted : (scalar 0 (-2)).check ⟨0, fun _ => -100000⟩ = true := by decide
theorem wrong_direction_rejected : (scalar 0 1).check ⟨0, fun _ => -1⟩ = false := by decide
theorem fractional_index_rejected : (scalar 0 2).check ⟨0, fun _ => 3⟩ = false := by decide
theorem zero_period_singleton :
    (scalar 7 0).check ⟨0, fun _ => 7⟩ = true ∧
    (scalar 7 0).check ⟨0, fun _ => 8⟩ = false := by decide
theorem descending_not_below_ascending : (scalar 0 (-1)).checkSubset (scalar 0 1) = false := by decide
theorem shifted_ray_below_origin : (scalar 3 1).checkSubset (scalar 0 1) = true := by decide
theorem distinct_bases_are_not_equal : (scalar 3 1).checkEqual (scalar 0 1) = false := by decide
theorem no_boundary_key_check :
    (Ray.check (n := 0) ⟨raw (0 : Nat), Fin.elim0⟩ (raw 0) = true) ∧
    (Ray.check (n := 0) ⟨raw (0 : Nat), Fin.elim0⟩ (raw 1) = false) := by decide

def secondCoordinate : Ray 2 Nat := ⟨raw 0, fun i => if i.val = 0 then 0 else 2⟩

theorem zero_first_coordinate_uses_later_candidate :
    secondCoordinate.check ⟨0, fun i => if i.val = 0 then 0 else 1000⟩ = true := by decide

end Examples

end Yulang.AffineRows
