import Yulang.GeneralSourceRoleCstMissingAmbiguity294

/-! Maximality is relative to the ordered portable mark list and the
exact bridge relation already proved. It is not an equivalence proof for
Rust's full wall of structural diagnostics. -/
namespace Yulang.GeneralSourceRoleCstMaximalRuns294
open GeneralSourceRoleCstOriginalMarks294 (Origin)
open GeneralSourceRoleCstErrorRuns294 (bridge Neighbors runs every_run bridge_exact)

def separated (a b : List Origin) : Prop :=
  ∃ x y, a.getLast? = some x ∧ b.head? = some y ∧ bridge x y = false

def MaximalBoundaries : List (List Origin) → Prop
  | [] | [_] => True
  | a::b::rest => separated a b ∧ MaximalBoundaries (b::rest)

theorem separation_cons (x a : Origin) (tail next : List Origin) :
    separated (x::a::tail) next ↔ separated (a::tail) next := by
  simp [separated]

theorem no_empty_run (input : List Origin) : [] ∉ runs input := by
  intro h
  have nonempty := every_run input [] h
  cases nonempty

theorem grouped_boundaries (input : List Origin) : MaximalBoundaries (runs input) := by
  induction input with
  | nil => trivial
  | cons a more ih =>
    cases h : runs more with
    | nil => simp [runs,h,MaximalBoundaries]
    | cons group rest =>
      cases group with
      | nil =>
        have present : [] ∈ runs more := by rw [h]; exact List.mem_cons_self
        exact False.elim (no_empty_run more present)
      | cons b tail =>
        cases decision : bridge a b with
        | false =>
          simp only [runs,h,decision,Bool.false_eq_true,ite_false,MaximalBoundaries]
          exact ⟨⟨a,b,rfl,rfl,decision⟩,h ▸ ih⟩
        | true =>
          cases rest with
          | nil => simp [runs,h,decision,MaximalBoundaries]
          | cons row rows =>
            have boundary : separated (b::tail) row ∧ MaximalBoundaries (row::rows) := by
              rw [h] at ih; exact ih
            simp only [runs,h,decision,ite_true,MaximalBoundaries]
            exact ⟨(separation_cons ..).mpr boundary.1,boundary.2⟩

theorem adjacent_boundary {groups : List (List Origin)} (h : MaximalBoundaries groups)
    (before after : List (List Origin)) (a b : List Origin)
    (shape : groups = before ++ a::b::after) : separated a b := by
  subst groups
  induction before with
  | nil => exact h.1
  | cons head before ih =>
    cases before with
    | nil => exact ih h.2
    | cons x xs => exact ih h.2

theorem no_bridge_across_runs (input : List Origin) (before after : List (List Origin))
    (a b : List Origin) (shape : runs input = before ++ a::b::after) :
    ∃ x y, a.getLast? = some x ∧ b.head? = some y ∧ ¬ Neighbors x y := by
  obtain ⟨x,y,aEnd,bStart,no⟩ :=
    adjacent_boundary (grouped_boundaries input) before after a b shape
  exact ⟨x,y,aEnd,bStart,fun bad => Bool.noConfusion ((bridge_exact ..).mpr bad ▸ no)⟩

end Yulang.GeneralSourceRoleCstMaximalRuns294
