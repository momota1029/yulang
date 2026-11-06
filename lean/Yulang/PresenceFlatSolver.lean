import Yulang.PresenceFiniteBounds
import Yulang.PresenceBoundCoalescing

/-!
# Total principal solving for flat Boolean presence constraints

An input is an arbitrary finite list of lower bounds, variable-flow edges,
upper bounds and fixed comparisons, whose bounds use `PresenceFiniteBounds`.
The input type itself declares the fragment. There is no support test, fuel,
supplied comparison oracle or successful-cache assumption in the complete
solver theorem.

The result is rejected or a finite shared-parameter scheme. Each output is a
union of fixed lower bounds and finitely many terms `parameter j ∩ upper j`.
All parameters remain arbitrary predicates on all runtime data values. The
solver's finite presence-profile enumeration is used only to decide fixed
bound comparisons; it never restricts parameters to those representatives.

This closes the flat fragment only. Recursive constructors, payload bounds,
open-tail dependencies, functions and rows do not occur in this input grammar.
-/

namespace Yulang.PresenceFlatSolver

open PresenceFiniteBounds (Bound denote checkLe)
open PresenceDataTypes (Ty Le)
open SourceDataRuntime (Value)

variable {n : Nat}

abbrev Constraint (n : Nat) := LayerBoundTemplates.Constraint n Bound
abbrev Problem (n : Nat) := LayerBoundTemplates.Problem n Bound

/-- Independent satisfaction by arbitrary predicates at the original slots. -/
abbrev Models (problem : Problem n) (value : Fin n → Ty) :=
  PresenceBoundCoalescing.Models denote problem value

/-- Finite output syntax with shared parameter identities. No source
constraints, semantic witnesses or parameter obligations are stored. -/
structure Scheme (n : Nat) where
  lower : Fin n → List Bound
  parts : Fin n → List (Fin n × List Bound)

def Scheme.instantiate (scheme : Scheme n) (parameters : Fin n → Ty) (target : Fin n) : Ty :=
  fun value =>
    (∃ bound ∈ scheme.lower target, denote bound value) ∨
      ∃ part ∈ scheme.parts target,
        parameters part.1 value ∧ ∀ bound ∈ part.2, denote bound value

def coalesce (problem : Problem n) : Scheme n where
  lower := LayerBoundTemplates.lowerBounds problem
  parts := fun target => (LayerBoundTemplates.ancestors problem target).map fun source =>
    (source, LayerBoundTemplates.upperBounds problem source)

/-- The computed finite scheme has exactly the shared-parameter expansion,
for every parameter predicate and every runtime value. -/
theorem coalesce_exact (problem : Problem n) (parameters : Fin n → Ty)
    (target : Fin n) (value : Value) :
    (coalesce problem).instantiate parameters target value ↔
      PresenceBoundCoalescing.expand denote problem parameters target value := by
  unfold Scheme.instantiate coalesce PresenceBoundCoalescing.expand PresenceBoundCoalescing.lower
    PresenceBoundCoalescing.upper
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨part, member, valid, upper⟩
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact ⟨source, (LayerBoundTemplates.mem_ancestors problem source target).mp present, valid, upper⟩
  · rintro ⟨source, path, valid, upper⟩
    exact ⟨_, List.mem_map.mpr ⟨source,
      (LayerBoundTemplates.mem_ancestors problem source target).mpr path, rfl⟩, valid, upper⟩

theorem coalesce_eq_expand (problem : Problem n) (parameters : Fin n → Ty) :
    (coalesce problem).instantiate parameters = PresenceBoundCoalescing.expand denote problem parameters := by
  funext target value
  exact propext (coalesce_exact problem parameters target value)

/-- No semantic inclusion checker is an argument: the fixed-bound checker
is the finite, fully proved profile algorithm. -/
def consistent (problem : Problem n) : Bool :=
  PresenceBoundCoalescing.consistent checkLe problem

theorem consistent_exact (problem : Problem n) :
    consistent problem = true ↔ ∃ value : Fin n → Ty, Models problem value :=
  PresenceBoundCoalescing.consistent_iff_satisfiable checkLe denote
    PresenceFiniteBounds.checkLe_exact problem

theorem coalesce_satisfies (problem : Problem n) (checked : consistent problem = true)
    (parameters : Fin n → Ty) : Models problem ((coalesce problem).instantiate parameters) := by
  rw [coalesce_eq_expand]
  exact PresenceBoundCoalescing.expand_satisfies
    ((PresenceBoundCoalescing.consistent_exact checkLe denote
      PresenceFiniteBounds.checkLe_exact problem).mp checked) parameters

theorem coalesce_retraction (problem : Problem n) (value : Fin n → Ty)
    (model : Models problem value) : (coalesce problem).instantiate value = value := by
  rw [coalesce_eq_expand]
  exact PresenceBoundCoalescing.expand_retraction_eq model

inductive Result (n : Nat) where
  | rejected
  | solved : Scheme n → Result n

/-- A total algorithm. Every inhabitant of `Problem n` is in the fragment. -/
def solve (problem : Problem n) : Result n :=
  if consistent problem then .solved (coalesce problem) else .rejected

theorem solve_solved_iff (problem : Problem n) (scheme : Scheme n) :
    solve problem = .solved scheme ↔ consistent problem = true ∧ scheme = coalesce problem := by
  cases checked : consistent problem <;> simp [solve, checked, eq_comm]

theorem solve_rejected_iff (problem : Problem n) :
    solve problem = .rejected ↔ ¬ ∃ value : Fin n → Ty, Models problem value := by
  have exact := consistent_exact problem
  cases checked : consistent problem <;> simp_all [solve]

theorem solved_satisfies (problem : Problem n) (scheme : Scheme n)
    (returned : solve problem = .solved scheme) (parameters : Fin n → Ty) :
    Models problem (scheme.instantiate parameters) := by
  obtain ⟨checked, rfl⟩ := (solve_solved_iff problem scheme).mp returned
  exact coalesce_satisfies problem checked parameters

theorem solved_retraction (problem : Problem n) (scheme : Scheme n)
    (returned : solve problem = .solved scheme) (value : Fin n → Ty)
    (model : Models problem value) : scheme.instantiate value = value := by
  obtain ⟨_, rfl⟩ := (solve_solved_iff problem scheme).mp returned
  exact coalesce_retraction problem value model

/-- Complete solution-space equality, with no success or satisfiability
premise. All independent slot assignments and all unrestricted parameters
are quantified; the output has no residual constraints. -/
theorem solve_models_exact (problem : Problem n) (value : Fin n → Ty) :
    Models problem value ↔
      ∃ scheme, solve problem = .solved scheme ∧
        ∃ parameters : Fin n → Ty, scheme.instantiate parameters = value := by
  constructor
  · intro model
    have checked := (consistent_exact problem).mpr ⟨value, model⟩
    exact ⟨coalesce problem, by simp [solve, checked], value, coalesce_retraction problem value model⟩
  · rintro ⟨scheme, returned, parameters, rfl⟩
    exact solved_satisfies problem scheme returned parameters

/-- Both outcomes of the total solver are characterized for every input.
In the successful case *every* parameter choice is valid, and every
independent solution is recovered by using that solution as parameters. -/
theorem solve_complete (problem : Problem n) :
    match solve problem with
    | .rejected => ¬ ∃ value : Fin n → Ty, Models problem value
    | .solved scheme =>
        (∀ parameters : Fin n → Ty, Models problem (scheme.instantiate parameters)) ∧
        (∀ value : Fin n → Ty, Models problem value → scheme.instantiate value = value) := by
  cases returned : solve problem with
  | rejected => exact (solve_rejected_iff problem).mp returned
  | solved scheme =>
      exact ⟨solved_satisfies problem scheme returned, solved_retraction problem scheme returned⟩

/-- Subsumed output instances also agree with all independent solutions,
for every result slot and arbitrary target predicate. -/
theorem solve_instances_exact (problem : Problem n) (output : Fin n) (target : Ty) :
    (∃ value : Fin n → Ty, Models problem value ∧ Le (value output) target) ↔
      ∃ scheme, solve problem = .solved scheme ∧ ∃ parameters : Fin n → Ty,
        Le (scheme.instantiate parameters output) target := by
  constructor
  · rintro ⟨value, model, below⟩
    obtain ⟨scheme, returned, parameters, same⟩ := (solve_models_exact problem value).mp model
    exact ⟨scheme, returned, parameters, same ▸ below⟩
  · rintro ⟨scheme, returned, parameters, below⟩
    exact ⟨scheme.instantiate parameters, solved_satisfies problem scheme returned parameters, below⟩

/-- Isolated unconstrained variables retain every predicate exactly. In
particular they are not defaulted to a record or a finite profile value. -/
theorem unconstrained_parameters (parameters : Fin n → Ty) :
    (coalesce ([] : Problem n)).instantiate parameters = parameters := by
  apply coalesce_retraction
  intro constraint impossible
  cases impossible

namespace Examples

def conflicting : Problem 1 := [.lower (.present 7) 0, .upper 0 (.absent 7)]

theorem conflicting_rejected : solve conflicting = .rejected := by
  have checked : consistent conflicting = false := by decide +kernel
  simp [solve, checked]

def indirectConflict : Problem 2 :=
  [.lower (.present 7) 0, .flow 0 1, .upper 1 (.absent 7)]

theorem indirect_conflict_rejected : solve indirectConflict = .rejected := by
  have checked : consistent indirectConflict = false := by decide +kernel
  simp [solve, checked]

/-- This bound retains a relation between two fields; it is not projected
to two independent optional-field flags. -/
def correlated : Bound :=
  .union (.inter (.present 0) (.absent 1)) (.inter (.absent 0) (.present 1))

def correlatedProblem : Problem 1 := [.lower correlated 0, .upper 0 .records]

theorem correlated_solved : solve correlatedProblem = .solved (coalesce correlatedProblem) := by
  have checked : consistent correlatedProblem = true := by decide +kernel
  simp [solve, checked]

end Examples

end Yulang.PresenceFlatSolver
