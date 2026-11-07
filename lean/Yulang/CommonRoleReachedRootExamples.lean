import Yulang.CommonRoleReachedRootObstruction

/-! A one-role, one-impl, one-variable illustration. It has a repeated goal,
so it alone is not an undecidability proof. The separate packed program
family proves the algorithmic obstruction, including algorithms with caches. -/

namespace Yulang.CommonRoleReachedRootExamples

open CommonRoleLinearClock (Pattern)
open CommonRoleReachedRoot

def headPattern : Pattern := .variant 8 (.variant 7 (.var 0))
def childPattern : Pattern := .variant 8 (.var 0)

def implementation : Roles.Impl :=
  ⟨0, [headPattern.encode], [⟨0, [childPattern.encode]⟩], 0⟩

def goal : Goal := ⟨0, .variant 8 .clock⟩

theorem declaration_sizes :
    Roles.argsSize implementation.head = 3 ∧
      Roles.argsSize [childPattern.encode] = 2 := by
  decide +kernel

theorem declaration_accepted : CheckedRoles.checkImpl implementation = true := by
  decide +kernel

theorem root_not_recursive : ¬ StructuralRecursive goal.argument := by
  simp [goal, StructuralRecursive, Description.clockOnly]

theorem root_matches : Matches implementation goal (fun _ => .clock) := by
  refine ⟨⟨0, .variant 8 (.variant 7 .clock)⟩, ?_, rfl, ?_⟩
  · simp [interpretGoal, implementation, headPattern, instantiate]
  · exact (CommonCanonicalShapes.variant_equivalent_iff 8 _ _).mpr
      (Common.equivalent_symm CommonRoleLinearClock.clock_unfold)

theorem child_returns_to_goal :
    interpretGoal ⟨0, [childPattern.encode]⟩ (fun _ => .clock) = some goal := by
  simp [interpretGoal, childPattern, instantiate, goal]

theorem unique_head : Unique [implementation] implementation goal := by
  intro other member _
  exact List.mem_singleton.mp member

theorem no_rejection (path : List (Roles.Impl × Nat)) : ¬ Rejects [implementation] goal path := by
  intro rejected
  have allSafe {root : Goal} {trail} (failure : Rejects [implementation] root trail) :
      ∀ payload, root = ⟨0, .variant 8 payload⟩ → False := by
    induction failure with
    | here recursive =>
        intro payload equal
        rw [equal] at recursive
        simp [StructuralRecursive, Description.clockOnly] at recursive
    | descend safe selected assignment index member matched unique requirement present interpreted failure ih =>
        intro payload _
        have selectedSame := List.mem_singleton.mp member
        subst selected
        have required := List.mem_of_getElem? present
        have requiredSame : requirement = ⟨0, [childPattern.encode]⟩ := by
          simpa [implementation] using required
        subst requirement
        have read : interpretGoal ⟨0, [childPattern.encode]⟩ assignment =
            some ⟨0, .variant 8 (assignment 0)⟩ := by
          simp [interpretGoal, childPattern, instantiate]
        exact ih _ (Option.some.inj (read.symm.trans interpreted)).symm
  exact allSafe rejected .clock rfl

end Yulang.CommonRoleReachedRootExamples
