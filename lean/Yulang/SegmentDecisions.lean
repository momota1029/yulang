import Yulang.SymbolicRows

/-!
# Exact containment and equality of affine row segments

The input is an existing `SymbolicRows.Segment`: its optional endpoint is the
actual represented endpoint, not an unfolding limit for an unknown solution.
For a bounded source, containment checks every index through that endpoint.
This is a terminating decision procedure; its work grows with the endpoint,
and no endpoint-independent efficiency bound is asserted.

Two unbounded index ranges use the existing affine-ray containment procedure.
An unbounded source can be contained in a bounded target only when every source
period coordinate is zero. Such a source denotes one occurrence, which is
checked directly. The proofs allow zero dimensions, negative periods and zero
coordinates; an unbounded index range need not denote an infinite set.

This module compares two already supplied segments. It does not assert that
every recursive row graph has a segment representation, or decide containment
between arbitrary unions of segments or general recursive row systems.
-/

namespace Yulang.SegmentDecisions

open Directed
open AffineRows (Ray)
open SymbolicRows (Segment Allows)

variable {n : Nat} {Key : Type}

def Subset (source target : Segment n Key) : Prop :=
  ∀ occurrence, source.Holds occurrence → target.Holds occurrence

def checkZeroPeriod (ray : Ray n Key) : Bool :=
  (List.finRange n).all (fun coordinate => decide (ray.period coordinate = 0))

theorem checkZeroPeriod_exact (ray : Ray n Key) :
    checkZeroPeriod ray = true ↔ ∀ coordinate, ray.period coordinate = 0 := by
  simp [checkZeroPeriod]

theorem point_of_zero_period (ray : Ray n Key)
    (zero : ∀ coordinate, ray.period coordinate = 0) (count : Nat) :
    ray.point count = ray.base := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  simp [Ray.point, zero coordinate]

theorem bounded_subset_iff (source : Ray n Key) (stop : Nat) (target : Segment n Key) :
    Subset ⟨source, some stop⟩ target ↔
      ∀ count, count < stop + 1 → target.Holds (source.point count) := by
  constructor
  · intro included count bound
    exact included _ ⟨count, show count ≤ stop by omega, rfl⟩
  · intro contains occurrence member
    obtain ⟨count, allowed, rfl⟩ := member
    change count ≤ stop at allowed
    exact contains count (by omega)

theorem unbounded_subset_iff (source target : Ray n Key) :
    Subset ⟨source, none⟩ ⟨target, none⟩ ↔ source.Subset target := by
  unfold Subset Ray.Subset
  simp only [Segment.unbounded]

/-- A nonconstant source ray cannot fit into a bounded target segment. Target
indices have a strictly positive slope and eventually exceed the endpoint. -/
theorem unbounded_bounded_zero (source target : Ray n Key) (stop : Nat)
    (included : Subset ⟨source, none⟩ ⟨target, some stop⟩) :
    ∀ coordinate, source.period coordinate = 0 := by
  have rays : source.Subset target := by
    rintro occurrence ⟨count, rfl⟩
    obtain ⟨index, _, equality⟩ := included _ ⟨count, trivial, rfl⟩
    exact ⟨index, equality⟩
  obtain ⟨first, next, atZero, atOne, ordered⟩ := source.endpoints_necessary target rays
  intro coordinate
  apply Classical.byContradiction
  intro nonzero
  have period := source.endpoints_period target first next atZero atOne coordinate
  have targetNonzero : target.period coordinate ≠ 0 := by
    intro zero
    rw [zero, Int.mul_zero] at period
    exact nonzero period
  have strict : first < next := by
    apply Classical.byContradiction
    intro unordered
    have same : first = next := by omega
    rw [same, Int.sub_self, Int.zero_mul] at period
    exact nonzero period
  obtain ⟨far, allowed, atFar⟩ := included (source.point (stop + 1)) ⟨stop + 1, trivial, rfl⟩
  change far ≤ stop at allowed
  have coordinates := congrFun (congrArg Occurrence.weights atFar) coordinate
  rw [source.endpoint_point target first next (stop + 1) atZero atOne] at coordinates
  change target.base.weights coordinate + (far : Int) * target.period coordinate = _ at coordinates
  have mult : (far : Int) * target.period coordinate =
      ((first : Int) + ((stop + 1 : Nat) : Int) * ((next : Int) - (first : Int))) *
        target.period coordinate := by omega
  have coefficient := Int.eq_of_mul_eq_mul_right targetNonzero mult
  have positive : (1 : Int) ≤ (next : Int) - (first : Int) := by omega
  have growth := Int.mul_le_mul_of_nonneg_left positive
    (show (0 : Int) ≤ ((stop + 1 : Nat) : Int) by omega)
  simp only [Int.mul_one, Int.natCast_add, Int.ofNat_one] at growth coefficient
  omega

theorem unbounded_bounded_iff (source target : Ray n Key) (stop : Nat) :
    Subset ⟨source, none⟩ ⟨target, some stop⟩ ↔
      (∀ coordinate, source.period coordinate = 0) ∧
        (Segment.mk target (some stop)).Holds source.base := by
  constructor
  · intro included
    exact ⟨unbounded_bounded_zero source target stop included,
      included _ ⟨0, trivial, source.point_zero⟩⟩
  · rintro ⟨zero, base⟩ occurrence ⟨count, _, rfl⟩
    rw [point_of_zero_period source zero count]
    exact base

/-- A bounded source is enumerated through its exact endpoint. Unbounded
sources use either ray containment or the singleton test for a zero period. -/
def checkSubset [DecidableEq Key] (source target : Segment n Key) : Bool :=
  match source.upper, target.upper with
  | some stop, _ =>
      (List.range (stop + 1)).all (fun count => target.check (source.ray.point count))
  | none, none => source.ray.checkSubset target.ray
  | none, some _ => checkZeroPeriod source.ray && target.check source.ray.base

theorem checkSubset_exact [DecidableEq Key] (source target : Segment n Key) :
    checkSubset source target = true ↔ Subset source target := by
  rcases source with ⟨source, sourceUpper⟩
  rcases target with ⟨target, targetUpper⟩
  cases sourceUpper with
  | some stop =>
      simp only [checkSubset, List.all_eq_true, List.mem_range, Segment.check_exact]
      exact (bounded_subset_iff source stop ⟨target, targetUpper⟩).symm
  | none =>
      cases targetUpper with
      | none =>
          simp only [checkSubset, Ray.checkSubset_exact]
          exact (unbounded_subset_iff source target).symm
      | some stop =>
          simp only [checkSubset, Bool.and_eq_true, checkZeroPeriod_exact, Segment.check_exact]
          exact (unbounded_bounded_iff source target stop).symm

theorem checkSubset_rejects [DecidableEq Key] (source target : Segment n Key) :
    checkSubset source target = false ↔ ¬ Subset source target := by
  constructor
  · intro rejected included
    have accepted := (checkSubset_exact source target).mpr included
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases answer : checkSubset source target with
    | false => rfl
    | true => exact False.elim (missing ((checkSubset_exact source target).mp answer))

def checkEqual [DecidableEq Key] (left right : Segment n Key) : Bool :=
  checkSubset left right && checkSubset right left

theorem checkEqual_exact [DecidableEq Key] (left right : Segment n Key) :
    checkEqual left right = true ↔ ∀ occurrence, left.Holds occurrence ↔ right.Holds occurrence := by
  simp only [checkEqual, Bool.and_eq_true, checkSubset_exact]
  exact ⟨fun ⟨lr, rl⟩ occurrence => ⟨lr occurrence, rl occurrence⟩,
    fun same => ⟨fun occurrence => (same occurrence).mp, fun occurrence => (same occurrence).mpr⟩⟩

theorem checkEqual_set_exact [DecidableEq Key] (left right : Segment n Key) :
    checkEqual left right = true ↔ left.Holds = right.Holds := by
  rw [checkEqual_exact]
  exact ⟨fun same => funext (fun occurrence => propext (same occurrence)),
    fun same occurrence => by rw [same]⟩

namespace Examples

def scalar (base period : Int) (upper : Option Nat) : Segment 1 Nat :=
  ⟨⟨⟨0, fun _ => base⟩, fun _ => period⟩, upper⟩

theorem finite_prefix_contained :
    checkSubset (scalar 0 2 (some 3)) (scalar 0 1 (some 6)) = true := by decide

theorem true_endpoint_is_checked :
    checkSubset (scalar 0 2 (some 3)) (scalar 0 1 (some 5)) = false := by decide

theorem finite_negative_period :
    checkSubset (scalar 0 (-2) (some 3)) (scalar 0 (-1) (some 6)) = true := by decide

theorem reversed_finite_prefix_equal :
    checkEqual (scalar 0 1 (some 3)) (scalar 3 (-1) (some 3)) = true := by decide

theorem singleton_prefix_ignores_direction :
    checkEqual (scalar 3 2 (some 0)) (scalar 3 (-5) (some 0)) = true := by decide

theorem finite_prefix_below_unbounded :
    checkSubset (scalar 2 2 (some 5)) (scalar 0 1 none) = true := by decide

theorem unbounded_ray_below_ray :
    checkSubset (scalar 0 2 none) (scalar 0 1 none) = true := by decide

theorem unbounded_opposite_directions :
    checkSubset (scalar 0 (-1) none) (scalar 0 1 none) = false := by decide

theorem unbounded_nonzero_not_below_prefix :
    checkSubset (scalar 0 1 none) (scalar 0 1 (some 1000000)) = false := by decide

theorem unbounded_constant_inside_prefix :
    checkSubset (scalar 2 0 none) (scalar 0 1 (some 3)) = true := by decide

theorem unbounded_constant_outside_prefix :
    checkSubset (scalar 4 0 none) (scalar 0 1 (some 3)) = false := by decide

theorem constant_bounded_unbounded_equal :
    checkEqual (scalar 3 0 (some 2)) (scalar 3 0 none) = true := by decide

def secondCoordinate (upper : Option Nat) : Segment 2 Nat :=
  ⟨⟨raw 0, fun coordinate => if coordinate.val = 0 then 0 else 1⟩, upper⟩

theorem zero_first_coordinate_does_not_make_constant :
    checkSubset (secondCoordinate none) (secondCoordinate (some 5)) = false := by decide

def zeroDim (key : Nat) (upper : Option Nat) : Segment 0 Nat :=
  ⟨⟨raw key, fun _ => 0⟩, upper⟩

theorem zero_dimensions_is_singleton :
    checkEqual (zeroDim 0 none) (zeroDim 0 (some 0)) = true := by decide

theorem zero_dimensions_keep_keys_distinct :
    checkSubset (zeroDim 0 none) (zeroDim 1 (some 0)) = false := by decide

end Examples

end Yulang.SegmentDecisions
