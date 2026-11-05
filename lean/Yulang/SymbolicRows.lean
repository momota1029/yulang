import Yulang.AffineRows

/-!
# Finite descriptions of affine row segments and their row operations

An absent upper endpoint denotes an unbounded ray. A present endpoint is part
of the exact represented set, not a truncation of an unknown least solution.
Membership is decided using the finite candidates of `AffineRows`.

Finite expressions built from segments, union and difference are closed under
every existing row-expression operation. Shift operations update the stored
base; their bijectivity makes difference exact. A residual removes only the
finite set of handled raw occurrences. Neither operation enumerates an infinite
support. This is closure of the supplied representation, not a claim that every
recursive problem has a solution in this representation or an inclusion
algorithm for arbitrary expressions.
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

def Segment.shift (scope : Fin n) (permission : Permission Key) (amount : Int)
    (segment : Segment n Key) : Segment n Key :=
  ⟨⟨Directed.shift scope permission amount segment.ray.base, segment.ray.period⟩, segment.upper⟩

theorem Segment.point_shift (scope : Fin n) (permission : Permission Key) (amount : Int)
    (segment : Segment n Key) (count : Nat) :
    (segment.shift scope permission amount).ray.point count =
      Directed.shift scope permission amount (segment.ray.point count) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  by_cases moved : coordinate = scope ∧ permission segment.ray.base.key = false
  · simp [Segment.shift, Ray.point, Directed.shift, moved]
    omega
  · simp [Segment.shift, Ray.point, Directed.shift, moved]

private theorem shift_injective (scope : Fin n) (permission : Permission Key) (amount : Int)
    {left right : Occurrence n Key}
    (equal : Directed.shift scope permission amount left = Directed.shift scope permission amount right) :
    left = right := by
  have inverse := congrArg (Directed.shift scope permission (-amount)) equal
  simpa only [Directed.shift_add, show amount + -amount = 0 by omega,
    Directed.shift_zero] using inverse

theorem Segment.shift_pullback (scope : Fin n) (permission : Permission Key) (amount : Int)
    (segment : Segment n Key) (occurrence : Occurrence n Key) :
    (segment.shift scope permission amount).Holds (Directed.shift scope permission amount occurrence) ↔
      segment.Holds occurrence := by
  constructor
  · rintro ⟨count, allowed, equal⟩
    rw [Segment.point_shift] at equal
    exact ⟨count, allowed, shift_injective scope permission amount equal⟩
  · rintro ⟨count, allowed, rfl⟩
    exact ⟨count, allowed, Segment.point_shift scope permission amount segment count⟩

/-- A finite symbolic syntax. Difference is a set operation, not a negative
dependency in the recursive lower-bound constraint language. -/
inductive Expr (n : Nat) (Key : Type) where
  | empty
  | segment (value : Segment n Key)
  | union (left right : Expr n Key)
  | difference (left right : Expr n Key)

def Expr.Holds : Expr n Key → RecursiveRows.SetRow n Key
  | .empty => fun _ => False
  | .segment value => value.Holds
  | .union left right => fun occurrence => left.Holds occurrence ∨ right.Holds occurrence
  | .difference left right => fun occurrence => left.Holds occurrence ∧ ¬ right.Holds occurrence

def Expr.check [DecidableEq Key] : Expr n Key → Occurrence n Key → Bool
  | .empty, _ => false
  | .segment value, occurrence => value.check occurrence
  | .union left right, occurrence => left.check occurrence || right.check occurrence
  | .difference left right, occurrence => left.check occurrence && !right.check occurrence

theorem Expr.check_exact [DecidableEq Key] (expression : Expr n Key) (occurrence : Occurrence n Key) :
    expression.check occurrence = true ↔ expression.Holds occurrence := by
  induction expression with
  | empty => simp [Expr.check, Expr.Holds]
  | segment value => exact value.check_exact occurrence
  | union left right ihl ihr => simp [Expr.check, Expr.Holds, ihl, ihr]
  | difference left right ihl ihr =>
      cases hl : left.check occurrence <;> cases hr : right.check occurrence <;>
        simp_all [Expr.check, Expr.Holds]

def Expr.singleton (occurrence : Occurrence n Key) : Expr n Key :=
  .segment ⟨⟨occurrence, fun _ => 0⟩, some 0⟩

theorem Expr.singleton_exact (point occurrence : Occurrence n Key) :
    (Expr.singleton point).Holds occurrence ↔ occurrence = point := by
  constructor
  · rintro ⟨count, allowed, equal⟩
    have zero : count = 0 := by exact Nat.eq_zero_of_le_zero allowed
    subst count
    simpa only [Ray.point_zero] using equal.symm
  · intro equal
    subst occurrence
    exact ⟨0, Nat.le_refl _, Ray.point_zero _⟩

def Expr.ofList : List (Occurrence n Key) → Expr n Key
  | [] => .empty
  | head :: tail => .union (.singleton head) (Expr.ofList tail)

theorem Expr.ofList_exact (points : List (Occurrence n Key)) (occurrence : Occurrence n Key) :
    (Expr.ofList points).Holds occurrence ↔ occurrence ∈ points := by
  induction points with
  | nil => simp [Expr.ofList, Expr.Holds]
  | cons head tail ih =>
      simp only [Expr.ofList, Expr.Holds, Expr.singleton_exact, ih, List.mem_cons]

def Expr.shift (scope : Fin n) (permission : Permission Key) (amount : Int) : Expr n Key → Expr n Key
  | .empty => .empty
  | .segment value => .segment (value.shift scope permission amount)
  | .union left right => .union (left.shift scope permission amount) (right.shift scope permission amount)
  | .difference left right =>
      .difference (left.shift scope permission amount) (right.shift scope permission amount)

theorem Expr.shift_pullback (scope : Fin n) (permission : Permission Key) (amount : Int)
    (expression : Expr n Key) (occurrence : Occurrence n Key) :
    (expression.shift scope permission amount).Holds (Directed.shift scope permission amount occurrence) ↔
      expression.Holds occurrence := by
  induction expression with
  | empty => exact Iff.rfl
  | segment value => exact value.shift_pullback scope permission amount occurrence
  | union left right ihl ihr => exact or_congr ihl ihr
  | difference left right ihl ihr => exact and_congr ihl (not_congr ihr)

theorem Expr.shift_exact (scope : Fin n) (permission : Permission Key) (amount : Int)
    (expression : Expr n Key) (occurrence : Occurrence n Key) :
    (expression.shift scope permission amount).Holds occurrence ↔
      ∃ original, expression.Holds original ∧ Directed.shift scope permission amount original = occurrence := by
  constructor
  · intro member
    let original := Directed.shift scope permission (-amount) occurrence
    have inverse : Directed.shift scope permission amount original = occurrence := by
      simp only [original, Directed.shift_add, show -amount + amount = 0 by omega,
        Directed.shift_zero]
    refine ⟨original, ?_, inverse⟩
    apply (expression.shift_pullback scope permission amount original).mp
    exact inverse.symm ▸ member
  · rintro ⟨original, member, rfl⟩
    exact (expression.shift_pullback scope permission amount original).mpr member

def Expr.protect (scope : Fin n) (permission : Permission Key) (expression : Expr n Key) : Expr n Key :=
  expression.shift scope permission 1

def Expr.release (scope : Fin n) (permission : Permission Key) (expression : Expr n Key) : Expr n Key :=
  expression.shift scope permission (-1)

def Expr.residual (handled : List Key) (expression : Expr n Key) : Expr n Key :=
  .difference expression (Expr.ofList (handled.map raw))

theorem capturable_iff_mem_raw (handled : List Key) (occurrence : Occurrence n Key) :
    Capturable handled occurrence ↔ occurrence ∈ handled.map raw := by
  constructor
  · rintro ⟨member, zero⟩
    refine List.mem_map.mpr ⟨occurrence.key, member, ?_⟩
    apply Occurrence.ext
    · rfl
    intro coordinate
    exact (zero coordinate).symm
  · intro member
    obtain ⟨key, handledKey, equal⟩ := List.mem_map.mp member
    cases equal
    exact ⟨handledKey, fun _ => rfl⟩

theorem Expr.residual_exact (handled : List Key) (expression : Expr n Key)
    (occurrence : Occurrence n Key) :
    (expression.residual handled).Holds occurrence ↔
      expression.Holds occurrence ∧ ¬ Capturable handled occurrence := by
  simp only [Expr.residual, Expr.Holds, Expr.ofList_exact, capturable_iff_mem_raw]

/-- Compile any row expression whose environment is already represented by
finite expressions. This does not solve a recursive fixed-point equation. -/
def compile (environment : Slot → Expr n Key) : RowInference.RowExpr Key (Fin n) Slot → Expr n Key
  | .empty => .empty
  | .var slot => environment slot
  | .head key => .singleton (raw key)
  | .union left right => .union (compile environment left) (compile environment right)
  | .protect scope permission row => (compile environment row).protect scope permission
  | .release scope permission row => (compile environment row).release scope permission
  | .residual handled row => (compile environment row).residual handled

theorem compile_exact (environment : Slot → Expr n Key)
    (row : RowInference.RowExpr Key (Fin n) Slot) (occurrence : Occurrence n Key) :
    (compile environment row).Holds occurrence ↔
      row.eval (RecursiveRows.algebra n Key) (fun slot => (environment slot).Holds) occurrence := by
  induction row generalizing occurrence with
  | empty => exact Iff.rfl
  | var slot => exact Iff.rfl
  | head key => exact Expr.singleton_exact (raw key) occurrence
  | union left right ihl ihr => exact or_congr (ihl occurrence) (ihr occurrence)
  | protect scope permission row ih =>
      change ((compile environment row).shift scope permission 1).Holds occurrence ↔ _
      rw [Expr.shift_exact]
      exact exists_congr (fun original => and_congr (ih original) Iff.rfl)
  | release scope permission row ih =>
      change ((compile environment row).shift scope permission (-1)).Holds occurrence ↔ _
      rw [Expr.shift_exact]
      exact exists_congr (fun original => and_congr (ih original) Iff.rfl)
  | residual handled row ih =>
      change ((compile environment row).residual handled).Holds occurrence ↔ _
      rw [Expr.residual_exact]
      exact and_congr (ih occurrence) Iff.rfl

theorem check_compiled_exact [DecidableEq Key] (environment : Slot → Expr n Key)
    (row : RowInference.RowExpr Key (Fin n) Slot) (occurrence : Occurrence n Key) :
    (compile environment row).check occurrence = true ↔
      row.eval (RecursiveRows.algebra n Key) (fun slot => (environment slot).Holds) occurrence :=
  ((compile environment row).check_exact occurrence).trans (compile_exact environment row occurrence)

namespace Examples

def positive : Expr 1 Unit := .segment ⟨⟨raw (), fun _ => 1⟩, none⟩
def even : Expr 1 Unit := .segment ⟨⟨raw (), fun _ => 2⟩, none⟩
def odd : Expr 1 Unit := .difference positive even
def weighted (weight : Int) : Occurrence 1 Unit := ⟨(), fun _ => weight⟩

example : odd.check (weighted 100001) = true := by decide
example : odd.check (weighted 100000) = false := by decide
example : odd.check (weighted (-1)) = false := by decide
example : (odd.protect 0 allowNone).check (weighted 100002) = true := by decide
example : (odd.protect 0 allowAll).check (weighted 100002) = false := by decide
example : (positive.residual [()]).check (weighted 0) = false := by decide
example : (positive.residual [()]).check (weighted 100000) = true := by decide
example : ((positive.protect 0 allowNone).residual [()]).check (weighted 1) = true := by decide
example : ((positive.release 0 allowNone).residual [()]).check (weighted (-1)) = true := by decide

end Examples

end Yulang.SymbolicRows
