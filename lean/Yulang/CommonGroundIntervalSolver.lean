import Yulang.CommonInvariantIntervals
import Yulang.CommonGroundScalarCasts

/-!
# Executable interval-bound solving with closed scalar endpoints

The finite bounds machine and expansion are reused unchanged. Its actual
fixed comparisons are decided by the existing computed scalar canonicalizer.
Every returned parameter ranges over arbitrary existing Common types; neither
an interval model predicate nor an endpoint oracle is a parameter condition.
This covers the displayed endpoint grammar, not arbitrary nominal source
construction or correlated open endpoint expressions.
-/

namespace Yulang.CommonGroundIntervalSolver

open Common (Ty Equivalent)
open CommonGroundScalarCasts (Scalar meaning)

abbrev Problem (slots : Nat) := LayerBoundTemplates.Problem slots Scalar

def check (problem : Problem slots) : Bool :=
  (CommonBoundCoalescing.rigidComparisons problem).all fun comparison =>
    CommonGroundScalarCasts.check comparison.1 comparison.2

theorem check_exact (problem : Problem slots) :
    check problem = true ↔ CommonBoundCoalescing.Consistent meaning problem := by
  simp only [check, List.all_eq_true, CommonGroundScalarCasts.check_exact,
    CommonBoundCoalescing.Consistent]

structure Scheme (slots : Nat) where
  problem : Problem slots

abbrev Scheme.Parameters (_scheme : Scheme slots) := Fin slots → Ty

def Scheme.instantiate (scheme : Scheme slots) (parameters : scheme.Parameters) : Fin slots → Ty :=
  CommonBoundCoalescing.expand meaning scheme.problem parameters

def solve (problem : Problem slots) : List (Scheme slots) :=
  if check problem then [⟨problem⟩] else []

theorem mem_solve (problem : Problem slots) (scheme : Scheme slots) :
    scheme ∈ solve problem ↔ check problem = true ∧ scheme.problem = problem := by
  cases accepted : check problem <;> simp [solve, accepted]
  case true =>
    constructor
    · intro same; cases same; rfl
    · intro same; cases scheme; cases same; rfl

/-- All arbitrary existing Common type parameters, after the actual finite
checker succeeds through membership of the returned scheme. -/
theorem all_parameters_models (problem : Problem slots) (scheme : Scheme slots)
    (returned : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    CommonBoundCoalescing.Models meaning problem (scheme.instantiate parameters) := by
  obtain ⟨checked, same⟩ := (mem_solve problem scheme).mp returned
  change CommonBoundCoalescing.Models meaning problem
    (CommonBoundCoalescing.expand meaning scheme.problem parameters)
  rw [same]
  exact CommonBoundCoalescing.expand_satisfies ((check_exact problem).mp checked) parameters

/-- Every original actual argument slot is recovered simultaneously. No
substitution is existentially guessed by the implementation: instantiate is
exactly the existing expand and the original model is its retraction tuple. -/
theorem solve_all_instances_exact (problem : Problem slots) (actual : Fin slots → Ty) :
    CommonBoundCoalescing.Models meaning problem actual ↔
      ∃ scheme ∈ solve problem, ∃ parameters : scheme.Parameters,
        ∀ index, Equivalent (scheme.instantiate parameters index) (actual index) := by
  constructor
  · intro model
    have consistent := (CommonBoundCoalescing.consistent_iff_satisfiable meaning problem).mpr
      ⟨actual, model⟩
    let scheme : Scheme slots := ⟨problem⟩
    exact ⟨scheme, (mem_solve problem scheme).mpr ⟨(check_exact problem).mpr consistent, rfl⟩,
      actual, CommonBoundCoalescing.expand_retraction model⟩
  · rintro ⟨scheme, returned, parameters, same⟩
    exact (CommonBoundCoalescing.models_congr meaning problem same).mp
      (all_parameters_models problem scheme returned parameters)

theorem rejected_iff (problem : Problem slots) :
    solve problem = [] ↔ ¬ ∃ actual, CommonBoundCoalescing.Models meaning problem actual := by
  rw [← CommonBoundCoalescing.consistent_iff_satisfiable, ← check_exact]
  cases accepted : check problem <;> simp [solve, accepted]

/-- The pair stores syntax for two bounds, with no distinguished centre. -/
abbrev Occurrence (slots : Nat) := Fin slots × (Scalar × Scalar)

private def intervalConstraints (occurrence : Occurrence slots) : Problem slots :=
  [.lower occurrence.2.1 occurrence.1, .upper occurrence.1 occurrence.2.2]

def compile (occurrences : List (Occurrence slots))
    (flows : List (CommonInvariantIntervals.Flow slots)) : Problem slots :=
  occurrences.flatMap intervalConstraints ++ flows.map (fun edge => .flow edge.1 edge.2)

def intervals (occurrences : List (Occurrence slots)) : List (CommonInvariantIntervals.Occurrence slots) :=
  occurrences.map fun occurrence =>
    (occurrence.1, (meaning occurrence.2.1, meaning occurrence.2.2))

theorem compile_models_exact (occurrences : List (Occurrence slots))
    (flows : List (CommonInvariantIntervals.Flow slots)) (actual : Fin slots → Ty) :
    CommonBoundCoalescing.Models meaning (compile occurrences flows) actual ↔
      CommonInvariantIntervals.Models (intervals occurrences) flows actual := by
  simp only [CommonBoundCoalescing.Models, compile, List.mem_append, or_imp, forall_and,
    List.mem_flatMap, forall_exists_index, and_imp, List.mem_map,
    CommonInvariantIntervals.Models, intervals]
  constructor
  · rintro ⟨bounds, edges⟩
    refine ⟨?_, ?_⟩
    · intro interpreted occurrence member same
      subst interpreted
      exact ⟨bounds (.lower occurrence.2.1 occurrence.1) occurrence member
          (by simp [intervalConstraints]),
        bounds (.upper occurrence.1 occurrence.2.2) occurrence member
          (by simp [intervalConstraints])⟩
    · intro edge member
      exact edges _ edge member rfl
  · rintro ⟨bounds, edges⟩
    refine ⟨?_, ?_⟩
    · intro constraint occurrence member included
      have original := bounds _ occurrence member rfl
      simp only [intervalConstraints, List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl
      · exact original.1
      · exact original.2
    · intro constraint edge member same
      subst constraint
      exact edges edge member

theorem interval_all_parameters_models (occurrences : List (Occurrence slots))
    (flows : List (CommonInvariantIntervals.Flow slots)) (scheme : Scheme slots)
    (returned : scheme ∈ solve (compile occurrences flows)) (parameters : scheme.Parameters) :
    CommonInvariantIntervals.Models (intervals occurrences) flows (scheme.instantiate parameters) :=
  (compile_models_exact occurrences flows _).mp
    (all_parameters_models (compile occurrences flows) scheme returned parameters)

theorem interval_solve_all_instances_exact (occurrences : List (Occurrence slots))
    (flows : List (CommonInvariantIntervals.Flow slots)) (actual : Fin slots → Ty) :
    CommonInvariantIntervals.Models (intervals occurrences) flows actual ↔
      ∃ scheme ∈ solve (compile occurrences flows), ∃ parameters : scheme.Parameters,
        ∀ index, Equivalent (scheme.instantiate parameters index) (actual index) := by
  rw [← compile_models_exact]
  exact solve_all_instances_exact (compile occurrences flows) actual

end Yulang.CommonGroundIntervalSolver
