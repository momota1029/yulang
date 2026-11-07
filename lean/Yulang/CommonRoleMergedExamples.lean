import Yulang.CommonRoleMergedSemantic

/-! One repeated tag, one finite constant payload and one where child suffice
for a self-loop. A single variable additionally gives an unbounded sequence
of distinct finite goals. The stronger undecidability theorem is separate. -/
namespace Yulang.CommonRoleMergedExamples

open CommonRoleMergedPayload
open CommonRoleMergedRegistry (checkImpl)
open CommonRoleCanonicalMergedEvidence

def selfImpl : Roles.Impl := ⟨1, [headTerm 1 .int], [⟨1, [plainTerm .int]⟩], 1⟩
def selfGoal : Goal := ⟨1, .int⟩
def growingImpl : Roles.Impl := ⟨1, [headTerm 1 (.var 0)], [⟨1, [plainTerm (.variant 7 (.var 0))]⟩], 1⟩

theorem minimal_checked : checkImpl selfImpl = true := by decide +kernel
theorem growing_checked : checkImpl growingImpl = true := by decide +kernel

theorem minimal_sizes : Roles.argsSize selfImpl.head = 4 ∧
    Roles.argsSize (selfImpl.constraints[0]'(by decide)).args = 2 := by decide +kernel

theorem growing_sizes_occurrences : Roles.argsSize growingImpl.head = 4 ∧
    Roles.argsSize (growingImpl.constraints[0]'(by decide)).args = 3 ∧
    Roles.argsOccurrences 0 growingImpl.head = 2 ∧
    Roles.argsOccurrences 0 (growingImpl.constraints[0]'(by decide)).args = 1 := by decide +kernel

theorem minimal_normal : CommonRoleNormalizedDeclarations.normalizeImpl selfImpl = selfImpl := by
  simp [CommonRoleNormalizedDeclarations.normalizeImpl, CommonRoleNormalizedDeclarations.normalizeGoal,
    selfImpl, plainTerm, CommonRoleMergedRegistry.normalize_head]

theorem minimal_from_merge :
    CommonRoleMergedRegistry.headFromRow (mergedRow 1 .int) = some selfImpl.head :=
  CommonRoleMergedRegistry.merged_head _ _

theorem minimal_matches : headMatches selfImpl selfGoal = true := by decide +kernel
theorem minimal_child (substitution : Nat → CommonRoleLinearClock.Ground) :
    interpretGoal ⟨1, [plainTerm .int]⟩ substitution = some selfGoal := rfl

theorem no_finite_self_dictionary (goal : Goal) : ¬ Nonempty (Dictionary [selfImpl] goal) := by
  rintro ⟨dictionary⟩
  refine Dictionary.rec (motive_1 := fun _ _ => False)
    (motive_2 := fun _ requirements _ => requirements = []) ?_ ?_ ?_ dictionary
  · intro goal implementation substitution member matched unique children ih
    have same : implementation = selfImpl := by simpa using member
    subst implementation
    cases ih
  · intro substitution; rfl
  · intro substitution requirement child rest interpreted dictionary children ihChild ihRest
    exact False.elim ihChild

theorem no_self_descent_measure : ¬ ∃ measure : Goal → Nat, measure selfGoal < measure selfGoal := by
  rintro ⟨measure, impossible⟩
  omega

/-- Contracting the idempotent payload before Paterson measurement excludes
both small examples. This is a proposed checker change, not a settled rule. -/
def proposedContract (implementation : Roles.Impl) : Roles.Impl :=
  match decodeHead implementation.head with
  | none => implementation
  | some pattern => { implementation with head := [plainTerm pattern] }

theorem proposed_rejects_minimal : CheckedRoles.checkImpl (proposedContract selfImpl) = false := by decide +kernel
theorem proposed_rejects_growing : CheckedRoles.checkImpl (proposedContract growingImpl) = false := by decide +kernel

end Yulang.CommonRoleMergedExamples
