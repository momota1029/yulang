import Yulang.AffineRows

/-!
# Finite descriptions of affine row segments

An absent upper endpoint denotes an unbounded ray. A present endpoint is part
of the exact represented set, not a truncation of an unknown least solution.
Membership is decided using the finite candidates of `AffineRows`.
-/

namespace Yulang.SymbolicRows

open Directed
open AffineRows (Ray)

def Allows (upper : Option Nat) (count : Nat) : Prop :=
  match upper with
  | none => True
  | some stop => count ≤ stop

instance (upper : Option Nat) (count : Nat) : Decidable (Allows upper count) := by
  cases upper <;> unfold Allows <;> infer_instance

theorem allows_mono (upper : Option Nat) (first next : Nat) (le : first ≤ next)
    (allowed : Allows upper next) : Allows upper first := by
  cases upper with
  | none => trivial
  | some stop => exact Nat.le_trans le allowed

structure Segment (n : Nat) (Key : Type) where
  ray : Ray n Key
  upper : Option Nat

def Segment.Holds (segment : Segment n Key) : RecursiveRows.SetRow n Key :=
  fun occurrence => ∃ count, Allows segment.upper count ∧ segment.ray.point count = occurrence

def Segment.check [DecidableEq Key] (segment : Segment n Key) (occurrence : Occurrence n Key) : Bool :=
  (segment.ray.candidates occurrence).any fun count =>
    decide (Allows segment.upper count ∧ segment.ray.point count = occurrence)

theorem Segment.check_exact [DecidableEq Key] (segment : Segment n Key) (occurrence : Occurrence n Key) :
    segment.check occurrence = true ↔ segment.Holds occurrence := by
  simp only [Segment.check, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨count, _, allowed, equality⟩
    exact ⟨count, allowed, equality⟩
  · rintro ⟨count, allowed, rfl⟩
    obtain ⟨candidate, member, equal, earlier⟩ := segment.ray.bounded_candidate count
    exact ⟨candidate, member, allows_mono segment.upper candidate count earlier allowed, equal⟩

theorem Segment.unbounded (ray : Ray n Key) (occurrence : Occurrence n Key) :
    (Segment.mk ray none).Holds occurrence ↔ ray.Holds occurrence := by
  simp [Segment.Holds, Allows, Ray.Holds]

end Yulang.SymbolicRows
