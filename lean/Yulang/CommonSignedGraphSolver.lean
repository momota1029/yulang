import Yulang.CommonSignedSafetyDecision

/-!
# All instances of finite signed/residual row graphs with constants and purity

The returned scheme is the finite input graph and head list. Its interpretation
uses the proved Boolean safety algorithm and recursive finite-path closure.
All parameter rows are arbitrary. The solver performs the head checks itself;
no residual model condition or universally quantified path test is a parameter
condition. Value nodes, universal type binders and source compilation are not
handled by this row-only module.
-/
namespace Yulang.CommonSignedGraphSolver
open Common (Occurrence Row)
abbrev Scheme := CommonSignedSeedFamily.Scheme
abbrev Models {n : Nat} (problem : Scheme n) (rows : Fin n → Row) :=
  CommonSignedSeedFamily.Models problem rows

/-- The finite input and finite returned scheme have the same representation. -/
def checkHeads (problem : Scheme n) : Bool :=
  problem.heads.all (fun head => CommonSignedSafetyDecision.check problem.graph head.1 head.2)

theorem checkHeads_exact (problem : Scheme n) :
    checkHeads problem = true ↔ CommonSignedSeedFamily.HeadsSafe problem := by
  simp only [checkHeads, List.all_eq_true, CommonSignedSafetyDecision.check_exact,
    CommonSignedSeedFamily.HeadsSafe]

/-- Empty exactly when a checked constant can reach a pure sink. -/
def solve (problem : Scheme n) : List (Scheme n) :=
  if checkHeads problem then [problem] else []

/-- Safety is computed, including for arbitrary infinite parameter rows. The
remaining path closure is the meaning of finite recursive row graph syntax. -/
def instantiate (scheme : Scheme n) (parameters : Fin n → Row) : Fin n → Row :=
  fun target occurrence => CommonSignedSeedFamily.forced scheme target occurrence ∨
    ∃ source seed, parameters source seed ∧
      CommonSignedSafetyDecision.check scheme.graph source seed = true ∧
      CommonSignedFlowFamily.Path scheme.graph source seed target occurrence

theorem instantiate_exact (scheme : Scheme n) (parameters : Fin n → Row) :
    instantiate scheme parameters = scheme.instantiate parameters := by
  funext slot occurrence
  apply propext
  simp only [instantiate, CommonSignedSeedFamily.Scheme.instantiate,
    CommonSignedFlowFamily.Scheme.instantiate, Common.rowJoin, CommonSignedSafetyDecision.check_exact]

theorem mem_solve (problem scheme : Scheme n) :
    scheme ∈ solve problem ↔ checkHeads problem = true ∧ scheme = problem := by
  cases checked : checkHeads problem <;> simp [solve, checked]

/-- Every returned scheme, every unrestricted row parameter assignment. -/
theorem all_parameters_models (problem scheme : Scheme n) (returned : scheme ∈ solve problem)
    (parameters : Fin n → Row) : Models problem (instantiate scheme parameters) := by
  obtain ⟨checked, same⟩ := (mem_solve problem scheme).mp returned
  subst scheme
  rw [instantiate_exact]
  exact CommonSignedSeedFamily.all_parameters_models problem ((checkHeads_exact problem).mp checked) parameters

/-- Every independent original row assignment is recovered literally. -/
theorem model_retraction (problem : Scheme n) (rows : Fin n → Row) (model : Models problem rows) :
    problem ∈ solve problem ∧ instantiate problem rows = rows := by
  refine ⟨(mem_solve problem problem).mpr ⟨?_, rfl⟩, ?_⟩
  · exact (checkHeads_exact problem).mpr (CommonSignedSeedFamily.models_heads_safe problem rows model)
  · rw [instantiate_exact]
    exact CommonSignedSeedFamily.model_retraction problem rows model

/-- All finite signed graphs and heads, all independent rows, no support,
success, residual, finite-row or bounded-weight premise. -/
theorem solve_all_instances_exact (problem : Scheme n) (rows : Fin n → Row) :
    Models problem rows ↔ ∃ scheme ∈ solve problem, ∃ parameters : Fin n → Row,
      instantiate scheme parameters = rows := by
  constructor
  · intro model
    have recovered := model_retraction problem rows model
    exact ⟨problem, recovered.1, rows, recovered.2⟩
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact all_parameters_models problem scheme returned parameters

theorem rejected_iff (problem : Scheme n) :
    solve problem = [] ↔ ¬ ∃ rows, Models problem rows := by
  constructor
  · intro rejected ⟨rows, model⟩
    have returned := (model_retraction problem rows model).1
    rw [rejected] at returned
    cases returned
  · intro absent
    cases checked : checkHeads problem with
    | false => simp [solve, checked]
    | true =>
      exact False.elim (absent ⟨instantiate problem (fun _ => Common.rowEmpty),
        all_parameters_models problem problem ((mem_solve _ _).mpr ⟨checked, rfl⟩) _⟩)

theorem rejected_iff_head_path (problem : Scheme n) :
    solve problem = [] ↔ ∃ head ∈ problem.heads, ∃ sink ∈ problem.graph.pure, ∃ occurrence,
      CommonSignedFlowFamily.Path problem.graph head.1 head.2 sink occurrence :=
  (rejected_iff problem).trans (CommonSignedSeedFamily.inconsistent_iff_head_path problem)

namespace Examples

def captured : Scheme 2 :=
  ⟨⟨[⟨0, 1, .residual [7]⟩], [1]⟩, [(0, (7, [0]))]⟩

def negativeDebt : Scheme 2 :=
  ⟨⟨[⟨0, 1, .residual [7]⟩], [1]⟩, [(0, (7, [-1]))]⟩

def escapingCycle : Scheme 2 :=
  ⟨⟨[⟨0, 0, .shift 0 (.only []) 1⟩, ⟨0, 1, .residual [7]⟩], [1]⟩,
    [(0, (7, [0]))]⟩

theorem captured_checked : checkHeads captured = true := by decide +kernel

theorem negative_debt_checked : checkHeads negativeDebt = false := by decide +kernel

/-- A raw head blocked by the residual still escapes after one loop. -/
theorem cycle_checked : checkHeads escapingCycle = false := by decide +kernel

theorem growing_checked :
    checkHeads (CommonSignedSeedFamily.coalesce CommonSignedSeedFamily.Examples.growing) = true := by decide +kernel

end Examples
end Yulang.CommonSignedGraphSolver
