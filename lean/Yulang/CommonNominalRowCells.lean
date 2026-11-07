import Yulang.CommonNominalFieldTemplates
import Yulang.Horn

/-!
# Finite Boolean cells for unrestricted Common row parameters

A cell stores a nonempty finite table of Boolean row-membership vectors.
Instantiation uses parameter rows to select the first marked table entry, with
the first entry as the fallback. It uses finite conjunction/disjunction and
complement masks; it never tests whether parameter rows model constraints.
The table is finite syntax, and every parameter product is admissible.
-/

namespace Yulang.CommonNominalRowCells

open CommonNominalCarrier

abbrev Pattern (slots : Nat) := Fin slots → Bool

structure Cell (slots : Nat) where
  first : Pattern slots
  rest : List (Pattern slots)

def Cell.patterns (cell : Cell slots) : List (Pattern slots) := cell.first :: cell.rest

abbrev Parameters (slots : Nat) := Pattern slots → Row

def choose (fallback : Pattern slots) (parameters : Parameters slots) :
    List (Pattern slots) → Fin slots → Row
  | [], index => fun _ => fallback index = true
  | pattern :: rest, index => fun occurrence =>
      (parameters pattern occurrence ∧ pattern index = true) ∨
        (¬ parameters pattern occurrence ∧ choose fallback parameters rest index occurrence)

def Cell.instantiate (cell : Cell slots) (parameters : Parameters slots) : Fin slots → Row :=
  choose cell.first parameters cell.rest

/-- Instantiation always selects an actual entry of the finite table,
regardless of the arbitrary (possibly infinite) parameter rows. -/
theorem choose_selects (fallback : Pattern slots) (parameters : Parameters slots)
    (patterns : List (Pattern slots)) (occurrence : Common.Occurrence) :
    ∃ pattern ∈ fallback :: patterns,
      ∀ index, choose fallback parameters patterns index occurrence ↔ pattern index = true := by
  induction patterns with
  | nil => exact ⟨fallback, by simp, fun _ => Iff.rfl⟩
  | cons pattern rest ih =>
      by_cases selected : parameters pattern occurrence
      · exact ⟨pattern, by simp, by intro index; simp only [choose, selected, true_and, not_true_eq_false,
          false_and, or_false]⟩
      · obtain ⟨chosen, present, same⟩ := ih
        refine ⟨chosen, ?_, ?_⟩
        · simp only [List.mem_cons] at present ⊢
          exact present.elim Or.inl (fun member => Or.inr (Or.inr member))
        · intro index
          simpa only [choose, selected, false_and, not_false_eq_true, true_and, false_or] using same index

theorem Cell.selects (cell : Cell slots) (parameters : Parameters slots) (occurrence : Common.Occurrence) :
    ∃ pattern ∈ cell.patterns, ∀ index, cell.instantiate parameters index occurrence ↔ pattern index = true :=
  choose_selects cell.first parameters cell.rest occurrence

def recoveryParameters (rows : Fin slots → Row) : Parameters slots :=
  fun pattern occurrence => ∀ index, rows index occurrence ↔ pattern index = true

private theorem choose_recovers (fallback : Pattern slots) (rows : Fin slots → Row)
    (patterns : List (Pattern slots)) (occurrence : Common.Occurrence)
    (represented : ∃ pattern ∈ fallback :: patterns,
      ∀ index, rows index occurrence ↔ pattern index = true) :
    ∀ index, choose fallback (recoveryParameters rows) patterns index occurrence ↔ rows index occurrence := by
  induction patterns with
  | nil =>
      obtain ⟨pattern, member, same⟩ := represented
      have eq : pattern = fallback := List.mem_singleton.mp member
      subst pattern
      exact fun index => (same index).symm
  | cons pattern rest ih =>
      by_cases selected : recoveryParameters rows pattern occurrence
      · intro index
        simpa only [choose, selected, true_and, not_true_eq_false, false_and, or_false] using
          (selected index).symm
      · have representedRest : ∃ value ∈ fallback :: rest,
            ∀ index, rows index occurrence ↔ value index = true := by
          obtain ⟨value, member, same⟩ := represented
          simp only [List.mem_cons] at member
          rcases member with initial | second | present
          · exact ⟨value, List.mem_cons.mpr (Or.inl initial), same⟩
          · subst value
            exact False.elim (selected same)
          · exact ⟨value, List.mem_cons.mpr (Or.inr present), same⟩
        intro index
        simpa only [choose, selected, false_and, not_false_eq_true, true_and, false_or] using
          ih representedRest index

/-- The same original row assignment supplies unrestricted parameters at
all occurrences; different table cells can use this one parameter vector. -/
theorem Cell.recovers (cell : Cell slots) (rows : Fin slots → Row) (occurrence : Common.Occurrence)
    (represented : ∃ pattern ∈ cell.patterns, ∀ index, rows index occurrence ↔ pattern index = true) :
    ∀ index, cell.instantiate (recoveryParameters rows) index occurrence ↔ rows index occurrence :=
  choose_recovers cell.first rows cell.rest occurrence represented

end Yulang.CommonNominalRowCells
