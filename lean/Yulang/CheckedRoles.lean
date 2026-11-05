import Yulang.RoleConstraints

/-!
# Checked role declarations before total resolution

The original resolver takes `WellFormed impls` as an input proof. This module
computes that condition from each finite resolved declaration, constructs the
proof only after success, and then invokes the same well-founded resolver.
An invalid database is rejected even when the queried goal would not use its
invalid declaration. There is no depth or fuel parameter.

The finite occurrence check is complete for *all* variable identifiers: above
the bound of a where-condition its occurrence count is zero. The reference
check scans that numerical range; it does not claim optimal sparse-variable
performance. Parsing, role-name resolution, and source diagnostics remain
separate from this resolved-declaration checker.
-/

namespace Yulang.CheckedRoles

open Roles

def checkOccurrences (head child : List Term) : Bool :=
  (List.range (argsBound child)).all fun name =>
    decide (argsOccurrences name child ≤ argsOccurrences name head)

theorem checkOccurrences_exact (head child : List Term) :
    checkOccurrences head child = true ↔
      ∀ name, argsOccurrences name child ≤ argsOccurrences name head := by
  simp only [checkOccurrences, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro bounded name
    by_cases inside : name < argsBound child
    · exact bounded name inside
    · rw [args_occurrences_above_bound child name (by omega)]
      exact Nat.zero_le _
  · intro allVariables name _
    exact allVariables name

def checkCondition (head : List Term) (child : Goal) : Bool :=
  decide (argsSize child.args < argsSize head) && checkOccurrences head child.args

theorem checkCondition_exact (head : List Term) (child : Goal) :
    checkCondition head child = true ↔ argsSize child.args < argsSize head ∧
      ∀ name, argsOccurrences name child.args ≤ argsOccurrences name head := by
  simp only [checkCondition, Bool.and_eq_true, decide_eq_true_eq, checkOccurrences_exact]

def checkImpl (declaration : Impl) : Bool :=
  declaration.constraints.all (checkCondition declaration.head)

theorem checkImpl_exact (declaration : Impl) :
    checkImpl declaration = true ↔ declaration.WellFormed := by
  simp only [checkImpl, List.all_eq_true, checkCondition_exact, Impl.WellFormed]

def checkDatabase (impls : List Impl) : Bool := impls.all checkImpl

theorem checkDatabase_exact (impls : List Impl) :
    checkDatabase impls = true ↔ WellFormed impls := by
  simp only [checkDatabase, List.all_eq_true, checkImpl_exact, WellFormed]

theorem checked_condition_strictly_decreases (declaration : Impl)
    (accepted : checkImpl declaration = true) (child : Goal)
    (present : child ∈ declaration.constraints) (substitution : Subst) :
    argsSize (substArgs substitution child.args) <
      argsSize (substArgs substitution declaration.head) :=
  size_decreases ((checkImpl_exact declaration).mp accepted) present substitution

inductive Result where
  | invalidDeclarations
  | answer : Roles.Result → Result
  deriving DecidableEq, Repr

/-- Callers no longer have to supply a termination certificate. -/
def resolve (impls : List Impl) (goal : Goal) : Result :=
  if accepted : checkDatabase impls = true then
    .answer (Roles.resolve impls ((checkDatabase_exact impls).mp accepted) goal)
  else .invalidDeclarations

theorem resolve_agrees (impls : List Impl) (wellFormed : WellFormed impls) (goal : Goal) :
    resolve impls goal = .answer (Roles.resolve impls wellFormed goal) := by
  simp only [resolve, dite_eq_left ((checkDatabase_exact impls).mpr wellFormed)]

theorem invalid_exact (impls : List Impl) (goal : Goal) :
    resolve impls goal = .invalidDeclarations ↔ ¬ WellFormed impls := by
  by_cases accepted : checkDatabase impls = true
  · have wellFormed := (checkDatabase_exact impls).mp accepted
    simp [resolve, accepted, wellFormed]
  · have invalid : ¬ WellFormed impls := fun wf => accepted ((checkDatabase_exact impls).mpr wf)
    simp [resolve, accepted, invalid]

/-- Success includes declaration validity, a derivation and absence of any
reachable head overlap. There is no well-formedness premise on this theorem. -/
theorem resolve_exact (impls : List Impl) (goal : Goal) :
    resolve impls goal = .answer .resolved ↔
      WellFormed impls ∧ RoleConstraints.Resolves impls goal := by
  by_cases accepted : checkDatabase impls = true
  · have wellFormed := (checkDatabase_exact impls).mp accepted
    rw [resolve_agrees impls wellFormed goal]
    simp only [Result.answer.injEq, wellFormed, true_and,
      RoleConstraints.resolve_exact impls wellFormed goal]
  · have invalid : ¬ WellFormed impls := fun wf => accepted ((checkDatabase_exact impls).mpr wf)
    simp [resolve, accepted, invalid]

theorem ambiguous_exact (impls : List Impl) (goal : Goal) :
    resolve impls goal = .answer .ambiguous ↔
      WellFormed impls ∧ ReachesOverlap impls goal := by
  by_cases accepted : checkDatabase impls = true
  · have wellFormed := (checkDatabase_exact impls).mp accepted
    rw [resolve_agrees impls wellFormed goal]
    simp only [Result.answer.injEq, wellFormed, true_and,
      Roles.resolve_ambiguous_iff impls wellFormed goal]
  · have invalid : ¬ WellFormed impls := fun wf => accepted ((checkDatabase_exact impls).mpr wf)
    simp [resolve, accepted, invalid]

theorem valid_answer_exists (impls : List Impl) (goal : Goal) :
    (∃ result, resolve impls goal = .answer result) ↔ WellFormed impls := by
  constructor
  · rintro ⟨result, answer⟩
    by_cases accepted : checkDatabase impls = true
    · exact (checkDatabase_exact impls).mp accepted
    · have rejected : resolve impls goal = .invalidDeclarations := by simp [resolve, accepted]
      rw [answer] at rejected
      cases rejected
  · intro wellFormed
    exact ⟨_, resolve_agrees impls wellFormed goal⟩

namespace Examples

theorem good_declarations_accepted : checkDatabase Roles.Examples.goodImpls = true := by
  decide

theorem growing_declaration_rejected (goal : Goal) :
    resolve [Roles.Examples.badImpl] goal = .invalidDeclarations := by
  apply (invalid_exact _ _).mpr
  intro wellFormed
  exact Roles.Examples.bad_not_wellFormed (wellFormed _ (by simp))

theorem duplicated_variable_rejected (goal : Goal) :
    resolve [Roles.Examples.duplicatingImpl] goal = .invalidDeclarations := by
  apply (invalid_exact _ _).mpr
  intro wellFormed
  exact Roles.Examples.duplicating_not_wellFormed (wellFormed _ (by simp))

/-- Unused invalid declarations are not allowed to hide behind a successful goal. -/
theorem invalid_database_rejected_before_lookup (goal : Goal) :
    resolve (Roles.Examples.intImpl :: [Roles.Examples.badImpl]) goal =
      .invalidDeclarations := by
  apply (invalid_exact _ _).mpr
  intro wellFormed
  exact Roles.Examples.bad_not_wellFormed (wellFormed _ (by simp))

end Examples
end Yulang.CheckedRoles
