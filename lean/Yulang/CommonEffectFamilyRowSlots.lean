import Yulang.CommonEffectRowIntervalConstraints

/-!
Finite collection of row-kind invariant arguments at resolved effect-family
slots. A slot includes the original row location as well as family identity
and argument position: occurrences of a family at unrelated row locations
are not globally unified. Every original occurrence contributes its bounds.

The collector generates constraints around the allocator's shared argument
term. It does not guess matching substitutions, choose a family key, lower
source names, or solve the resulting general quantified constraints.
-/
namespace Yulang.CommonEffectFamilyRowSlots
open Common (Row)
open CommonEffectRequestGeneration (Computation RowExpr)
open CommonEffectFormula (Formula)
open CommonEffectInvariantIntervals
open CommonEffectRowIntervalConstraints (Bounds check check_exact contains contains_exact)
open CommonEffectUniversalArms (andAll andAll_exact)

structure Slot where
  row : Nat
  family : Nat
  argument : Nat
  deriving DecidableEq

structure Occurrence (scopes : Nat) (α : Type) where
  slot : Slot
  origin : Nat
  bounds : Bounds scopes α

def collect (slot : Slot) : List (Occurrence scopes α) → Bounds scopes α
  | [] => ⟨[], []⟩
  | occurrence :: rest =>
      if occurrence.slot = slot then occurrence.bounds.merge (collect slot rest)
      else collect slot rest

/-- Membership of the merged interval is precisely membership in every
original occurrence at that same row/family/argument slot. -/
theorem collect_member_exact (slot : Slot) (occurrences : List (Occurrence scopes α))
    (assignment : α → Computation) (actual : Row) :
    EffectRow.Member ((collect slot occurrences).eval assignment) actual ↔
      ∀ occurrence ∈ occurrences, occurrence.slot = slot →
        EffectRow.Member (occurrence.bounds.eval assignment) actual := by
  induction occurrences with
  | nil => simp [collect, Bounds.eval, EffectRow.Member, Common.rowLe]
  | cons occurrence rest ih =>
    by_cases same : occurrence.slot = slot
    · simp only [collect, same, ↓reduceIte, Bounds.eval_merge, EffectRow.merge_member, ih,
        List.mem_cons, forall_eq_or_imp, true_implies]
    · simp only [collect, same, ↓reduceIte, ih, List.mem_cons, forall_eq_or_imp, false_implies,
        true_and]

theorem collect_contains_exact (slot : Slot) (occurrences : List (Occurrence scopes α))
    (assignment : α → Computation) (actual : RowExpr scopes α) :
    (contains (collect slot occurrences) actual).Holds assignment ↔
      ∀ occurrence ∈ occurrences, occurrence.slot = slot →
        EffectRow.Member (occurrence.bounds.eval assignment) (actual.eval assignment) :=
  (contains_exact _ _ _).trans (collect_member_exact _ _ _ _)

end Yulang.CommonEffectFamilyRowSlots
