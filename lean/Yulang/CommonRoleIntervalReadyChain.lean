import Yulang.CommonRoleDeferredBounds
import Yulang.CommonRoleIntervalGeneration
import Yulang.CommonRoleStablePaterson

/-!
# Lower-head readiness alone is not a descent argument

Every snapshot below has ordinary finite, centre-less endpoint syntax and a
known pair lower head. A covariant pair wrapper produces the next bounds.
The corresponding growing declaration is rejected by the existing stable
Paterson check. This is a boundary for readiness alone, not a role resolver,
an accepted-program counterexample, or an E2 for the current language.
-/

namespace Yulang.CommonRoleIntervalReadyChain

open Core.PresenceGeneration (TyTerm)
open CommonRoleIntervals (Valid evaluate)
open CommonRoleIntervalGeneration (Argument eval)

def tower (last : TyTerm Empty) : Nat → TyTerm Empty
  | 0 => .pair (.base .int) last
  | count + 1 => .pair (.base .int) (tower last count)

def bounds (count : Nat) : Argument Empty :=
  (tower (.base .int) count, tower .top count)

/-- The projection reads a real syntax constructor, not an oracle for a
candidate or a putative solution of a matching equation. -/
def pairHead : TyTerm Empty → Option Unit
  | .pair _ _ => some ()
  | _ => none

def snapshot (count : Nat) : LayerBoundTemplates.Problem 1 (TyTerm Empty) :=
  [.lower (bounds count).1 0, .upper 0 (bounds count).2]

theorem always_known (count : Nat) :
    CommonRoleDeferredBounds.observe pairHead (snapshot count) 0 = .known () [] := by
  apply CommonRoleDeferredBounds.lower_arrives
  cases count <;> rfl

/-- These open bounds are consistent at every stage. No matching
substitution or successful candidate resolver is a premise. -/
theorem bounds_consistent (count : Nat) :
    Valid (evaluate (eval Empty.elim) (bounds count)) := by
  induction count with
  | zero =>
      exact (Common.common_pair_iff _ _ _ _).mpr
        ⟨Common.subtype_refl _, CommonBoundCoalescing.le_top _⟩
  | succ count ih =>
      exact (Common.common_pair_iff _ _ _ _).mpr ⟨Common.subtype_refl _, ih⟩

/-- No natural-valued measure decreases along this everywhere-ready,
everywhere-consistent sequence. Readiness therefore supplies no termination
argument on its own; an admissibility/descent condition remains necessary. -/
theorem no_readiness_rank :
    ¬ ∃ rank : Argument Empty → Nat,
      ∀ count, rank (bounds (count + 1)) < rank (bounds count) := by
  rintro ⟨rank, decreases⟩
  have bounded : ∀ count, rank (bounds count) + count ≤ rank (bounds 0) := by
    intro count
    induction count with
    | zero => omega
    | succ count ih =>
        have step := decreases count
        omega
  have impossible := bounded (rank (bounds 0) + 1)
  omega

def childTemplate : CommonRoleCaptureNormalization.Form := .pair .int (.var 0)

/-- The illustrative source template is `R a where R (int, a)`.
Its admissibility is checked separately below; readiness does not admit it. -/
def growingDeclaration : CommonRoleStablePaterson.Declaration :=
  ⟨0, 0, [.var 0], [(0, [childTemplate])]⟩

/-- The one fixed child template acts on the two endpoints separately.
No arbitrary point is captured between them to manufacture this sequence. -/
theorem declared_child_endpoints (count : Nat) :
    evaluate (eval Empty.elim) (bounds (count + 1)) =
      (childTemplate.eval (fun _ => eval Empty.elim (bounds count).1),
       childTemplate.eval (fun _ => eval Empty.elim (bounds count).2)) := rfl

end Yulang.CommonRoleIntervalReadyChain
