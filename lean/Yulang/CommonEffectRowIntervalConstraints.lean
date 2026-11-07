import Yulang.CommonEffectInvariantIntervals
import Yulang.CommonEffectUniversalArms

/-!
Finite row-argument bounds for a centre-less interval. Lower endpoints are
joined and upper endpoints are met. The finite representation retains the
endpoint lists because the existing signed RowExpr has no intersection node.
The generated check contains every actual lower/upper comparison, rather than
an opaque consistency predicate or a condition on returned parameters.

No family key is chosen here and no universal quantifier is solved here. An
argument slot and its occurrence provenance are supplied by resolved syntax.
-/
namespace Yulang.CommonEffectRowIntervalConstraints
open Common (Row rowLe)
open CommonEffectRequestGeneration (Computation RowExpr)
open CommonEffectFormula (Formula)
open CommonEffectInvariantIntervals
open CommonEffectUniversalArms (andAll andAll_exact)

structure Bounds (scopes : Nat) (α : Type) where
  lower : List (RowExpr scopes α)
  upper : List (RowExpr scopes α)

def Bounds.eval (bounds : Bounds scopes α) (assignment : α → Computation) : EffectRow.Bounds :=
  ⟨(fun occurrence => ∃ endpoint ∈ bounds.lower, endpoint.eval assignment occurrence),
   (fun occurrence => ∀ endpoint ∈ bounds.upper, endpoint.eval assignment occurrence)⟩

def crossChecks (first last : Bounds scopes α) : Formula scopes α :=
  andAll (first.lower.flatMap (fun lower => last.upper.map (fun upper => .rowLe lower upper)))

/-- These are the actual finite endpoint comparisons injected into the
constraint language; no semantic atom is added to Formula. -/
theorem cross_checks_exact (first last : Bounds scopes α) (assignment : α → Computation) :
    (crossChecks first last).Holds assignment ↔
      rowLe (first.eval assignment).lower (last.eval assignment).upper := by
  simp only [crossChecks, andAll_exact, List.forall_mem_flatMap, List.forall_mem_map, Formula.Holds]
  constructor
  · intro checks occurrence present upper member
    obtain ⟨lower, included, holds⟩ := present
    exact checks lower included upper member occurrence holds
  · intro checked lower included upper member occurrence holds
    exact checked occurrence ⟨lower, included, holds⟩ upper member

def check (bounds : Bounds scopes α) : Formula scopes α := crossChecks bounds bounds

theorem check_exact (bounds : Bounds scopes α) (assignment : α → Computation) :
    (check bounds).Holds assignment ↔ EffectRow.Consistent (bounds.eval assignment) :=
  cross_checks_exact bounds bounds assignment

end Yulang.CommonEffectRowIntervalConstraints
