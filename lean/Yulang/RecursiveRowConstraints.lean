import Yulang.RecursiveRowQueries
import Yulang.SolvedRecursiveRows

/-!
# Deciding fixed upper requirements on recursive row constraints

Each upper requirement has an arbitrary existing row expression on the left
and a fixed finite-key semilinear row on the right. Fresh output slots evaluate
all those expressions in the original least model. Automatic summaries and
exact semilinear inclusion then decide whether that least model meets them.
The least-model theorem turns the result into existence of an original model
satisfying every lower and upper requirement.

The returned Boolean is exact. `none` reports an extension outside the current
checked guard-erasure boundary, and is never a proof of inconsistency. Empty
upper lists succeed because every positive lower problem has a least model.
This does not constrain an open row in every future scheme instantiation:
satisfiability is existential, and the least row witnesses it when accepted.
-/

namespace Yulang.RecursiveRowConstraints

open RowInference (RowExpr)
open RecursiveRows (Problem Environment Models Derives algebra)
open SemilinearRowAlgebra (Row decode)

variable {n : Nat} {Key Slot : Type}

structure Upper (n : Nat) (Key Slot : Type) where
  row : RowExpr Key (Fin n) Slot
  allowed : Row n Key

def Upper.meaning [DecidableEq Key] (limit : Upper n Key Slot) :
    RecursiveRows.Upper n Key Slot :=
  ⟨limit.row, decode limit.allowed⟩

theorem meets_exact [DecidableEq Key] (limits : List (Upper n Key Slot))
    (rows : Environment n Key Slot) :
    RecursiveRows.Meets (limits.map Upper.meaning) rows ↔
      ∀ limit ∈ limits, ∀ occurrence,
        limit.row.eval (algebra n Key) rows occurrence → decode limit.allowed occurrence := by
  constructor
  · intro satisfied limit declared occurrence fact
    exact satisfied limit.meaning (List.mem_map.mpr ⟨limit, declared, rfl⟩) occurrence fact
  · intro satisfied limit declared occurrence fact
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp declared
    exact satisfied original member occurrence fact

def extended (problem : Problem n Key Slot) (limits : List (Upper n Key Slot)) :
    Problem n Key (Slot ⊕ Fin limits.length) :=
  RecursiveRowQueries.extend problem (fun index => (limits.get index).row)

def summarize [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (index : Fin limits.length) : Option (Row n Key) :=
  SolvedRecursiveRows.summarize (extended problem limits) (.inr index)

theorem summarize_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (index : Fin limits.length) (row : Row n Key)
    (returned : summarize problem limits index = some row)
    (occurrence : Directed.Occurrence n Key) :
    decode row occurrence ↔
      (limits.get index).row.eval (algebra n Key) (Derives problem) occurrence :=
  (SolvedRecursiveRows.summarize_exact _ _ _ returned occurrence.key occurrence.weights).trans
    (RecursiveRowQueries.query_exact problem _ index occurrence)

theorem summarize_decode [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (index : Fin limits.length) (row : Row n Key)
    (returned : summarize problem limits index = some row) :
    decode row = (limits.get index).row.eval (algebra n Key) (Derives problem) := by
  funext occurrence
  exact propext (summarize_exact problem limits index row returned occurrence)

def checkLimit [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (index : Fin limits.length) : Option Bool := do
  let source ← summarize problem limits index
  pure (SemilinearRowAlgebra.checkSubset source (limits.get index).allowed)

theorem checkLimit_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (index : Fin limits.length) (answer : Bool)
    (returned : checkLimit problem limits index = some answer) :
    answer = true ↔ ∀ occurrence,
      (limits.get index).row.eval (algebra n Key) (Derives problem) occurrence →
        decode (limits.get index).allowed occurrence := by
  cases selected : summarize problem limits index with
  | none => simp [checkLimit, selected] at returned
  | some source =>
      have same : SemilinearRowAlgebra.checkSubset source (limits.get index).allowed = answer := by
        simpa [checkLimit, selected] using returned
      rw [← same, SemilinearRowAlgebra.checkSubset_sets,
        summarize_decode problem limits index source selected]
      rfl

/-- Keep unsupported answers separate from both Boolean outcomes. -/
def allAnswers {α : Type} (choose : α → Option Bool) : List α → Option Bool
  | [] => some true
  | name :: rest =>
      match choose name, allAnswers choose rest with
      | some first, some later => some (first && later)
      | _, _ => none

theorem allAnswers_exact {α : Type} (choose : α → Option Bool)
    (property : α → Prop)
    (correct : ∀ name answer, choose name = some answer → (answer = true ↔ property name))
    (names : List α) (answer : Bool) (returned : allAnswers choose names = some answer) :
    answer = true ↔ ∀ name ∈ names, property name := by
  induction names generalizing answer with
  | nil =>
      have same : true = answer := Option.some.inj returned
      simp [← same]
  | cons name rest ih =>
      cases first : choose name <;> cases tail : allAnswers choose rest <;>
        simp only [allAnswers, first, tail] at returned <;> try contradiction
      case some.some head later =>
        have same : (head && later) = answer := Option.some.inj returned
        rw [← same, Bool.and_eq_true, correct name head first, ih later tail]
        simp

theorem allAnswers_supported {α : Type} (choose : α → Option Bool) (names : List α) :
    (∃ answer, allAnswers choose names = some answer) ↔
      ∀ name ∈ names, ∃ answer, choose name = some answer := by
  induction names with
  | nil => simp [allAnswers]
  | cons name rest ih =>
      constructor
      · rintro ⟨answer, returned⟩
        cases first : choose name <;> cases tail : allAnswers choose rest <;>
          simp only [allAnswers, first, tail] at returned <;> try contradiction
        case some.some head later =>
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨head, first⟩
          · exact ih.mp ⟨later, tail⟩ item member
      · intro total
        obtain ⟨first, selected⟩ := total name (by simp)
        obtain ⟨later, tail⟩ := ih.mpr (fun item member =>
          total item (List.mem_cons_of_mem _ member))
        exact ⟨first && later, by simp [allAnswers, selected, tail]⟩

def check [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot)) : Option Bool :=
  allAnswers (checkLimit problem limits) (List.finRange limits.length)

theorem check_least [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (answer : Bool) (returned : check problem limits = some answer) :
    answer = true ↔ RecursiveRows.Meets (limits.map Upper.meaning) (Derives problem) := by
  rw [meets_exact]
  have pointwise := allAnswers_exact (checkLimit problem limits)
    (fun index => ∀ occurrence,
      (limits.get index).row.eval (algebra n Key) (Derives problem) occurrence →
        decode (limits.get index).allowed occurrence)
    (checkLimit_exact problem limits) _ answer returned
  constructor
  · intro accepted limit member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact pointwise.mp accepted index (List.mem_finRange index)
  · intro satisfied
    apply pointwise.mpr
    intro index _
    exact satisfied (limits.get index) (List.get_mem _ index)

/-- A returned result decides existence of a model of the original lower
problem and every fixed upper expression, including infinite row solutions. -/
theorem check_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (answer : Bool) (returned : check problem limits = some answer) :
    answer = true ↔ ∃ rows, Models problem rows ∧
      ∀ limit ∈ limits, ∀ occurrence,
        limit.row.eval (algebra n Key) rows occurrence → decode limit.allowed occurrence := by
  rw [check_least problem limits answer returned, ← RecursiveRows.upper_constraints_exact]
  exact exists_congr (fun rows => and_congr Iff.rfl (meets_exact limits rows))

theorem check_rejects [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (answer : Bool) (returned : check problem limits = some answer) :
    answer = false ↔ ¬ ∃ rows, Models problem rows ∧
      ∀ limit ∈ limits, ∀ occurrence,
        limit.row.eval (algebra n Key) rows occurrence → decode limit.allowed occurrence := by
  simpa only [Bool.not_eq_true] using not_congr (check_exact problem limits answer returned)

theorem checkLimit_supported_iff [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot))
    (index : Fin limits.length) :
    (∃ answer, checkLimit problem limits index = some answer) ↔
      ∀ key ∈ SolvedRecursiveRows.keys (extended problem limits),
        GuardedRowErasure.Harmless
          (CertifiedRowSummaries.normalizedProblem key (extended problem limits)) key := by
  rw [← SolvedRecursiveRows.summarize_supported_iff (extended problem limits) (.inr index)]
  change (∃ answer, checkLimit problem limits index = some answer) ↔
    ∃ row, summarize problem limits index = some row
  cases selected : summarize problem limits index <;> simp [checkLimit, selected]

/-- The support condition is checked, not a supplied oracle. An empty list of
upper requirements needs no query and makes this condition vacuous. -/
theorem check_supported_iff [DecidableEq Key] [DecidableEq Slot]
    (problem : Problem n Key Slot) (limits : List (Upper n Key Slot)) :
    (∃ answer, check problem limits = some answer) ↔
      ∀ (_ : Fin limits.length), ∀ key ∈ SolvedRecursiveRows.keys (extended problem limits),
        GuardedRowErasure.Harmless
          (CertifiedRowSummaries.normalizedProblem key (extended problem limits)) key := by
  simp only [check, allAnswers_supported, List.mem_finRange, forall_const,
    checkLimit_supported_iff]

end Yulang.RecursiveRowConstraints
