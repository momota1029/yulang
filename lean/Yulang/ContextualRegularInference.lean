import Yulang.ContextualCoalescing
import Yulang.RegularInferenceModel

/-!
# Complete contextual instances in the actual inference carrier

Closing the actual coalesced graph into `RegularInferenceModel.solution`
preserves and reflects contextual demand comparison. The executable block
syntax and scheme evaluator are unchanged. The model below is the independent
contextual regular graph model, with arbitrary values for all unknowns.

Every independent contextual solution is represented by the actual solution
block with unrestricted shared type parameters. This closes the gap between
an external-graph retraction and the concrete carrier used by source inference.
-/

namespace Yulang.ContextualRegularInference

open RegularInferenceModel (Ty State graph solution solutionRef)

universe u
variable {n : Nat} {Row : Type u}

abbrev Models (source : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (leRow : Row → Row → Prop) (value : Fin n → Ty Row) : Prop :=
  ContextualNestedModels.Models leRow source constraints (graph Row) (fun index => State.node (value index))

abbrev Equivalent (leRow : Row → Row → Prop) :=
  ProducerContextualRegular.ProducerEq (graph Row) leRow

abbrev Le (leRow : Row → Row → Prop) :=
  ProducerContextualRegular.ProducerLe (graph Row) leRow

theorem solution_nodeLe (source : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (parameter : Fin n → Ty Row)
    (leRow : Row → Row → Prop) (left right : Fin n ⊕ State Row) :
    ContextualNestedModels.NodeLe (graph Row) leRow
        (solutionRef source cache parameter left) (solutionRef source cache parameter right) ↔
      ContextualNestedModels.NodeLe
        (RegularValueCoalescing.coalesceGraph source cache (graph Row) parameter) leRow left right :=
  ContextualCoalescing.nodeLe_morphism _ _ leRow (solutionRef source cache parameter)
    (RegularInferenceModel.solution_morphism source cache parameter) left right

/-- All solutions in the common carrier are represented by the unchanged
regular block evaluator, with no restrictions on the shared parameters. -/
theorem solve_models_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (value : Fin n → Ty Row) :
    Models source constraints leRow value ↔
      ∃ parameter : Fin n → Ty Row,
        ∀ index, Equivalent leRow (solution source cache parameter index) (value index) := by
  rw [Models, ContextualCoalescing.solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
    source constraints cache solved (graph Row) (fun index => State.node (value index))]
  constructor
  · rintro ⟨parameter, equivalent⟩
    refine ⟨parameter, fun index => ?_⟩
    exact ⟨(solution_nodeLe source cache parameter leRow (.inl index) (.inr (.node (value index)))).mpr
        (equivalent index).1,
      (solution_nodeLe source cache parameter leRow (.inr (.node (value index))) (.inl index)).mpr
        (equivalent index).2⟩
  · rintro ⟨parameter, equivalent⟩
    refine ⟨parameter, fun index => ?_⟩
    exact ⟨(solution_nodeLe source cache parameter leRow (.inl index) (.inr (.node (value index)))).mp
        (equivalent index).1,
      (solution_nodeLe source cache parameter leRow (.inr (.node (value index))) (.inl index)).mp
        (equivalent index).2⟩

/-- Every arbitrary parameter instance is independently a solution. -/
theorem solve_solution (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (parameter : Fin n → Ty Row) :
    Models source constraints leRow (solution source cache parameter) :=
  (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact source constraints cache solved _).mpr
    ⟨parameter, fun _ => ProducerContextualRegular.producerEq_refl _⟩

/-- The principal family equality covers every input without assuming that
the solver succeeds. The only right-side predicate after the computed result
is observational equality of the instantiated values. -/
theorem models_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (value : Fin n → Ty Row) :
    Models source constraints leRow value ↔
      ∃ cache, NestedValueSolver.solve rowCheck source constraints = some cache ∧
        ∃ parameter : Fin n → Ty Row,
          ∀ index, Equivalent leRow (solution source cache parameter index) (value index) := by
  constructor
  · intro model
    obtain ⟨cache, solved, _⟩ :=
      (ContextualCoalescing.models_exact rowCheck leRow rowRefl rowTrans rowExact
        source constraints (graph Row) (fun index => State.node (value index))).mp model
    exact ⟨cache, solved, (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
      source constraints cache solved value).mp model⟩
  · rintro ⟨cache, solved, parameter, equivalent⟩
    exact (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
      source constraints cache solved value).mpr ⟨parameter, equivalent⟩

def ConstrainedInstance (source : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (root : Fin n)
    (leRow : Row → Row → Prop) (target : Ty Row) : Prop :=
  ∃ value : Fin n → Ty Row, Models source constraints leRow value ∧ Le leRow (value root) target

def SchemeInstance (source : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (root : Fin n)
    (leRow : Row → Row → Prop) (target : Ty Row) : Prop :=
  ∃ parameter : Fin n → Ty Row, Le leRow (solution source cache parameter root) target

theorem solve_instances_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (root : Fin n) (target : Ty Row) :
    ConstrainedInstance source constraints root leRow target ↔
      SchemeInstance source cache root leRow target := by
  constructor
  · rintro ⟨value, model, below⟩
    obtain ⟨parameter, equivalent⟩ := (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
      source constraints cache solved value).mp model
    exact ⟨parameter, ProducerContextualRegular.producerLe_trans (equivalent root).1 below⟩
  · rintro ⟨parameter, below⟩
    exact ⟨solution source cache parameter,
      solve_solution rowCheck leRow rowRefl rowTrans rowExact source constraints cache solved parameter, below⟩

theorem instances_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (root : Fin n) (target : Ty Row) :
    ConstrainedInstance source constraints root leRow target ↔
      ∃ cache, NestedValueSolver.solve rowCheck source constraints = some cache ∧
        SchemeInstance source cache root leRow target := by
  constructor
  · rintro ⟨value, model, below⟩
    obtain ⟨cache, solved, parameter, equivalent⟩ :=
      (models_exact rowCheck leRow rowRefl rowTrans rowExact source constraints value).mp model
    exact ⟨cache, solved, parameter,
      ProducerContextualRegular.producerLe_trans (equivalent root).1 below⟩
  · rintro ⟨cache, solved, accepted⟩
    exact (solve_instances_exact rowCheck leRow rowRefl rowTrans rowExact
      source constraints cache solved root target).mpr accepted

end Yulang.ContextualRegularInference
