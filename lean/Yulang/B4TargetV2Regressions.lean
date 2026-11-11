import Yulang.B4SkeletonV2
import Yulang.CommonRoleScalarTargetObstruction

/-!
# I-17 regressions against both old-target obstructions

The first uses cycle118's same concrete scalar source boundary, real empty
ordinary state and empty registry. The second checks that an independently
resolved parent with a rejected child remains a diagnostic tree, never a
new root rejection or fabricated completed dictionary.
-/
namespace Yulang.B4TargetV2Regressions
open CommonRoleOutermostResolver
open B4TargetV2

/-- Same input as the old two-tag obstruction, now exactly pending. -/
theorem scalar_empty_classify (role : Nat) (out : Result) :
    B4TargetV2.Classify CommonRoleScalarTargetObstruction.boundary []
      CommonRoleSettledConstraints.State.empty role out ↔ out = .pending :=
  pending_only (CommonRoleScalarTargetObstruction.empty_pending role) out

/-- The tree judgment retains the actual scalar source run's pending result. -/
theorem scalar_empty_tree (role : Nat) (tree : Tree) :
    Resolves (Local CommonRoleScalarTargetObstruction.boundary []
      CommonRoleSettledConstraints.State.empty) role tree ↔ tree = .pending :=
  pending_tree_only (CommonRoleScalarTargetObstruction.empty_pending role) tree

theorem scalar_empty_not_rejected (role : Nat) :
    ¬ RejectReason CommonRoleScalarTargetObstruction.boundary []
      CommonRoleSettledConstraints.State.empty role := by
  intro reason
  exact reason.1 (CommonRoleScalarTargetObstruction.empty_pending role)

universe u
variable {v : B4Target.Vocabulary.{u}} {b : B4Target.SourceBoundary v}
  {r : v.Registry} {s : v.State} {d child : v.Demand}

/-- A single failed where-child is retained at its position. -/
theorem failed_child_tree (safe : B4Target.SafeKnown b r s d)
    (unique : B4Target.Unique b r s d key [child]) (reason : RejectReason b r s child) :
    Resolves (Local b r s) d (.selected key [.rejected]) :=
  .selected (.selected safe unique) (.cons (.rejected (.rejected reason)) .nil)

/-- Such a root cannot simultaneously be rejected in the new independent judgment. -/
theorem failed_child_not_root_rejected (safe : B4Target.SafeKnown b r s d)
    (unique : B4Target.Unique b r s d key [child]) : ¬ RejectReason b r s d :=
  safe_survivor_not_rejected safe unique.1

/-- There is deliberately no four-way readback of that incomplete parent. -/
theorem failed_child_not_completed (key : Nat) (out : Result) :
    ¬ Completed (.selected key [.rejected]) out :=
  B4Skeleton.rejected_child_has_no_completed_readback key [.rejected] (by simp) out

/-- All local source premises may hold and the exact tree is still allowed;
no hidden total Completed premise reintroduces the old obstruction. -/
theorem failed_child_no_classification (safe : B4Target.SafeKnown b r s d)
    (unique : B4Target.Unique b r s d key [child]) (reason : RejectReason b r s child)
    (out : Result) : ¬ B4TargetV2.Classify b r s d out := by
  intro derived
  obtain ⟨tree, resolved, done⟩ := classify_tree derived
  have same := resolves_functional b r s tree (.selected key [.rejected]) d resolved
    (failed_child_tree safe unique reason)
  rw [same] at done
  exact failed_child_not_completed key out done

end Yulang.B4TargetV2Regressions
