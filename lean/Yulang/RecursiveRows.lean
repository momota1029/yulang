import Yulang.RowInference

/-!
# Least solutions of recursive signed-row inclusions

This module closes the semantic recursive row subsystem without assuming that
its solution has finite support. A finite family of lower-bound rules uses the
existing `RowExpr` operations, including signed protection, release, and handler
residuals. The least solution is described by finite derivations, even when it
contains infinitely many distinct signed occurrences.

This is a least-solution theorem, not a decision procedure for general row
constraints or structural subtyping. It neither rejects recursive source
programs nor replaces their rows by a bounded enumeration. Finite list rows
embed into the same algebra without losing negative weights or protected tails.
-/

namespace Yulang.RecursiveRows

open Directed
open RowInference (RowAlgebra RowExpr)

abbrev SetRow (n : Nat) (Key : Type) := Occurrence n Key → Prop

/-- The same occurrence operations, interpreted as possibly infinite sets. -/
def algebra (n : Nat) (Key : Type) : RowAlgebra Key (Fin n) where
  Row := SetRow n Key
  empty := fun _ => False
  join := fun left right occurrence => left occurrence ∨ right occurrence
  head := fun key occurrence => occurrence = raw key
  protect := fun scope permission row occurrence =>
    ∃ original, row original ∧ protect scope permission original = occurrence
  release := fun scope permission row occurrence =>
    ∃ original, row original ∧ release scope permission original = occurrence
  residual := fun handled row occurrence => row occurrence ∧ ¬ Capturable handled occurrence
  le := fun left right => ∀ occurrence, left occurrence → right occurrence

abbrev Environment (n : Nat) (Key Slot : Type) := Slot → SetRow n Key

structure Rule (n : Nat) (Key Slot : Type) where
  target : Slot
  lower : RowExpr Key (Fin n) Slot

abbrev Problem (n : Nat) (Key Slot : Type) := List (Rule n Key Slot)

/-- Every rule requires its evaluated lower bound to be included at the target. -/
def Models (problem : Problem n Key Slot) (rows : Environment n Key Slot) : Prop :=
  ∀ rule ∈ problem, ∀ occurrence,
    rule.lower.eval (algebra n Key) rows occurrence → rows rule.target occurrence

def Below (left right : Environment n Key Slot) : Prop :=
  ∀ slot occurrence, left slot occurrence → right slot occurrence

def IsLeastModel (problem : Problem n Key Slot) (rows : Environment n Key Slot) : Prop :=
  Models problem rows ∧ ∀ other, Models problem other → Below rows other

mutual
  /-- A row fact has a finite derivation from one of the declared rules. -/
  inductive Derives (problem : Problem n Key Slot) : Slot → Occurrence n Key → Prop where
    | rule {rule : Rule n Key Slot} : rule ∈ problem →
        ExprDerives problem rule.lower occurrence → Derives problem rule.target occurrence

  /-- Finitary membership rules for the already established row syntax. -/
  inductive ExprDerives (problem : Problem n Key Slot) :
      RowExpr Key (Fin n) Slot → Occurrence n Key → Prop where
    | head (key : Key) : ExprDerives problem (.head key) (raw key)
    | var : Derives problem slot occurrence → ExprDerives problem (.var slot) occurrence
    | left : ExprDerives problem left occurrence →
        ExprDerives problem (.union left right) occurrence
    | right : ExprDerives problem right occurrence →
        ExprDerives problem (.union left right) occurrence
    | protect : ExprDerives problem row occurrence →
        ExprDerives problem (.protect scope permission row) (Directed.protect scope permission occurrence)
    | release : ExprDerives problem row occurrence →
        ExprDerives problem (.release scope permission row) (Directed.release scope permission occurrence)
    | residual : ExprDerives problem row occurrence → ¬ Capturable handled occurrence →
        ExprDerives problem (.residual handled row) occurrence
end

theorem expr_exact (problem : Problem n Key Slot) (row : RowExpr Key (Fin n) Slot)
    (occurrence : Occurrence n Key) :
    ExprDerives problem row occurrence ↔ row.eval (algebra n Key) (Derives problem) occurrence := by
  induction row generalizing occurrence with
  | empty =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; exact False.elim impossible
  | head key =>
      constructor
      · intro derivation; cases derivation; rfl
      · intro equality; cases equality; exact .head key
  | var slot =>
      constructor
      · intro derivation; cases derivation with | var h => exact h
      · exact .var
  | union left right ihLeft ihRight =>
      constructor
      · intro derivation
        cases derivation with
        | left h => exact Or.inl ((ihLeft occurrence).mp h)
        | right h => exact Or.inr ((ihRight occurrence).mp h)
      · intro fact
        cases fact with
        | inl h => exact .left ((ihLeft occurrence).mpr h)
        | inr h => exact .right ((ihRight occurrence).mpr h)
  | protect scope permission row ih =>
      constructor
      · intro derivation
        cases derivation with
        | protect h => exact ⟨_, (ih _).mp h, rfl⟩
      · rintro ⟨original, fact, rfl⟩
        exact .protect ((ih original).mpr fact)
  | release scope permission row ih =>
      constructor
      · intro derivation
        cases derivation with
        | release h => exact ⟨_, (ih _).mp h, rfl⟩
      · rintro ⟨original, fact, rfl⟩
        exact .release ((ih original).mpr fact)
  | residual handled row ih =>
      constructor
      · intro derivation
        cases derivation with
        | residual h blocked => exact ⟨(ih _).mp h, blocked⟩
      · rintro ⟨fact, blocked⟩
        exact .residual ((ih occurrence).mpr fact) blocked

theorem least_models (problem : Problem n Key Slot) : Models problem (Derives problem) := by
  intro rule member occurrence fact
  exact .rule member ((expr_exact problem rule.lower occurrence).mpr fact)

theorem least_below (problem : Problem n Key Slot) (rows : Environment n Key Slot)
    (model : Models problem rows) : Below (Derives problem) rows := by
  intro slot occurrence derivation
  exact Derives.rec
    (motive_1 := fun slot occurrence _ => rows slot occurrence)
    (motive_2 := fun row occurrence _ => row.eval (algebra n Key) rows occurrence)
    (fun member _ ih => model _ member _ ih)
    (fun _ => rfl)
    (fun _ ih => ih)
    (fun _ ih => Or.inl ih)
    (fun _ ih => Or.inr ih)
    (fun _ ih => ⟨_, ih, rfl⟩)
    (fun _ ih => ⟨_, ih, rfl⟩)
    (fun _ blocked ih => ⟨ih, blocked⟩)
    derivation

theorem least_principal (problem : Problem n Key Slot) :
    IsLeastModel problem (Derives problem) :=
  ⟨least_models problem, fun rows model => least_below problem rows model⟩

/-- A derived occurrence is forced by all solutions, including infinite ones. -/
theorem derives_iff_forced (problem : Problem n Key Slot) (slot : Slot)
    (occurrence : Occurrence n Key) :
    Derives problem slot occurrence ↔ ∀ rows, Models problem rows → rows slot occurrence :=
  ⟨fun derived rows model => least_below problem rows model slot occurrence derived,
    fun forced => forced (Derives problem) (least_models problem)⟩

theorem least_unique (problem : Problem n Key Slot) (rows : Environment n Key Slot)
    (least : IsLeastModel problem rows) :
    ∀ slot occurrence, rows slot occurrence ↔ Derives problem slot occurrence := by
  intro slot occurrence
  exact ⟨least.2 _ (least_models problem) slot occurrence,
    least_below problem rows least.1 slot occurrence⟩

theorem models_membership (first second : Problem n Key Slot)
    (same : ∀ rule, rule ∈ first ↔ rule ∈ second) (rows : Environment n Key Slot) :
    Models first rows ↔ Models second rows := by
  constructor
  · intro model rule member; exact model rule ((same rule).mpr member)
  · intro model rule member; exact model rule ((same rule).mp member)

theorem derives_membership (first second : Problem n Key Slot)
    (same : ∀ rule, rule ∈ first ↔ rule ∈ second) (slot : Slot)
    (occurrence : Occurrence n Key) :
    Derives first slot occurrence ↔ Derives second slot occurrence := by
  rw [derives_iff_forced, derives_iff_forced]
  constructor
  · intro forced rows model
    exact forced rows ((models_membership first second same rows).mpr model)
  · intro forced rows model
    exact forced rows ((models_membership first second same rows).mp model)

theorem eval_mono (row : RowExpr Key (Fin n) Slot)
    (left right : Environment n Key Slot) (below : Below left right)
    (occurrence : Occurrence n Key)
    (member : row.eval (algebra n Key) left occurrence) :
    row.eval (algebra n Key) right occurrence := by
  induction row generalizing occurrence with
  | empty => exact False.elim member
  | head _ => exact member
  | var slot => exact below slot occurrence member
  | union _ _ ihLeft ihRight =>
      exact member.elim (fun h => Or.inl (ihLeft occurrence h))
        (fun h => Or.inr (ihRight occurrence h))
  | protect _ _ _ ih =>
      obtain ⟨original, fact, equal⟩ := member
      exact ⟨original, ih original fact, equal⟩
  | release _ _ _ ih =>
      obtain ⟨original, fact, equal⟩ := member
      exact ⟨original, ih original fact, equal⟩
  | residual _ _ ih => exact ⟨ih occurrence member.1, member.2⟩

/-- A fixed upper requirement can be a finite row or an occurrence predicate.
It cannot depend negatively on the unknown row assignment. -/
structure Upper (n : Nat) (Key Slot : Type) where
  row : RowExpr Key (Fin n) Slot
  allowed : SetRow n Key

def Meets (limits : List (Upper n Key Slot)) (rows : Environment n Key Slot) : Prop :=
  ∀ limit ∈ limits, ∀ occurrence,
    limit.row.eval (algebra n Key) rows occurrence → limit.allowed occurrence

theorem meets_below (limits : List (Upper n Key Slot))
    (left right : Environment n Key Slot) (below : Below left right)
    (satisfied : Meets limits right) : Meets limits left := by
  intro limit member occurrence fact
  exact satisfied limit member occurrence (eval_mono limit.row left right below occurrence fact)

/-- Fixed upper requirements have a solution exactly when the constructed
least solution satisfies them. This is a semantic equivalence, not a checker. -/
theorem upper_constraints_exact (problem : Problem n Key Slot)
    (limits : List (Upper n Key Slot)) :
    (∃ rows, Models problem rows ∧ Meets limits rows) ↔ Meets limits (Derives problem) := by
  constructor
  · rintro ⟨rows, model, satisfied⟩
    exact meets_below limits _ rows (least_below problem rows model) satisfied
  · intro satisfied
    exact ⟨Derives problem, least_models problem, satisfied⟩

/-- Finite list rows keep all their occurrences in the extended interpretation. -/
def ofList (row : Directed.Row n Key) : SetRow n Key := fun occurrence => occurrence ∈ row

theorem finite_eval [DecidableEq Key] (row : RowExpr Key (Fin n) Slot)
    (rows : Slot → Directed.Row n Key) (occurrence : Occurrence n Key) :
    row.eval (algebra n Key) (fun slot => ofList (rows slot)) occurrence ↔
      ofList (row.eval (RowInference.signedAlgebra n Key) rows) occurrence := by
  induction row generalizing occurrence with
  | empty => simp [RowExpr.eval, algebra, RowInference.signedAlgebra, ofList]
  | head key => simp [RowExpr.eval, algebra, RowInference.signedAlgebra, ofList]
  | var slot => rfl
  | union left right ihLeft ihRight =>
      exact (or_congr (ihLeft occurrence) (ihRight occurrence)).trans List.mem_append.symm
  | protect scope permission row ih =>
      simp only [RowExpr.eval, algebra, RowInference.signedAlgebra, ofList, List.mem_map]
      exact exists_congr (fun original => and_congr (ih original) Iff.rfl)
  | release scope permission row ih =>
      simp only [RowExpr.eval, algebra, RowInference.signedAlgebra, ofList, List.mem_map]
      exact exists_congr (fun original => and_congr (ih original) Iff.rfl)
  | residual handled row ih =>
      simp only [RowExpr.eval, algebra, RowInference.signedAlgebra, ofList, Directed.residual,
        List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
      exact and_congr (ih occurrence) Iff.rfl

/-- Ordinary finite-row lower-bound problems are included faithfully; there
is no premise asserting that every recursive problem has a finite solution. -/
theorem finite_models_exact [DecidableEq Key] (problem : Problem n Key Slot)
    (rows : Slot → Directed.Row n Key) :
    Models problem (fun slot => ofList (rows slot)) ↔
      ∀ rule ∈ problem, ∀ occurrence,
        ofList (rule.lower.eval (RowInference.signedAlgebra n Key) rows) occurrence →
          occurrence ∈ rows rule.target := by
  unfold Models
  simp only [finite_eval, ofList]

namespace Examples

def scope : Fin 1 := 0

/-- The same finite problem can have an infinite least signed support. -/
def growing : Problem 1 Nat Unit :=
  [⟨(), .head 0⟩, ⟨(), .protect scope allowNone (.var ())⟩]

def raised (count : Nat) : Occurrence 1 Nat := ⟨0, fun _ => (count : Int)⟩

theorem protect_raised (count : Nat) : protect scope allowNone (raised count) = raised (count + 1) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  have equal : coordinate = scope := by
    apply Fin.ext
    have bound := coordinate.isLt
    change coordinate.val = 0
    omega
  subst coordinate
  simp [protect, shift, allowNone, raised, Int.natCast_add]

theorem every_weight_derived (count : Nat) : Derives growing () (raised count) := by
  induction count with
  | zero => exact .rule (rule := ⟨(), .head 0⟩) (by simp [growing]) (.head 0)
  | succ count ih =>
      rw [← protect_raised]
      exact .rule (rule := ⟨(), .protect scope allowNone (.var ())⟩)
        (by simp [growing]) (.protect (.var ih))

/-- A numerical bound for every member of any proposed finite support. -/
def weightBound : Directed.Row 1 Nat → Nat
  | [] => 0
  | first :: rest => (first.weights scope).natAbs + weightBound rest

theorem member_weight_le (row : Directed.Row 1 Nat) (occurrence : Occurrence 1 Nat)
    (member : occurrence ∈ row) : (occurrence.weights scope).natAbs ≤ weightBound row := by
  induction row with
  | nil => cases member
  | cons first rest ih =>
      cases List.mem_cons.mp member with
      | inl equal => subst occurrence; simp [weightBound]
      | inr member =>
          have smaller := ih member
          simp only [weightBound]
          omega

/-- A finite fact universe cannot solve even this two-rule recursive problem. -/
theorem growing_has_no_finite_model (row : Directed.Row 1 Nat) :
    ¬ Models growing (fun _ => ofList row) := by
  intro model
  have member : raised (weightBound row + 1) ∈ row :=
    least_below growing (fun _ => ofList row) model () _
      (every_weight_derived (weightBound row + 1))
  have bound := member_weight_le row _ member
  change weightBound row + 1 ≤ weightBound row at bound
  omega

/-- The problem is consistent in the extended algebra; its finite rejection
is not evidence that a corresponding source program is ill-typed. -/
theorem growing_has_least_model : IsLeastModel growing (Derives growing) := least_principal growing

def balanced : Problem 1 Nat Unit :=
  [⟨(), .head 0⟩, ⟨(), .release scope allowNone (.protect scope allowNone (.var ()))⟩]

/-- Cyclic dependence itself does not force infinite support: matched signed
transport permits the singleton solution, in the same recursive subsystem. -/
theorem balanced_has_finite_model : Models balanced (fun _ => ofList [raw 0]) := by
  intro rule member occurrence fact
  simp [balanced] at member
  rcases member with rfl | rfl
  · change occurrence = raw 0 at fact
    simp [ofList, fact]
  · change (∃ released, (∃ original, ofList [raw 0] original ∧
        protect scope allowNone original = released) ∧
        release scope allowNone released = occurrence) at fact
    rcases fact with ⟨released, ⟨original, originalMember, rfl⟩, equal⟩
    rw [release_protect] at equal
    exact equal ▸ originalMember

end Examples

end Yulang.RecursiveRows
