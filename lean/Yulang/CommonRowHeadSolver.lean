import Yulang.CommonRowHeadFlow

/-!
# Complete finite row-head solution families

The solver returns either no scheme, for a required occurrence that reaches
an empty upper bound, or one finite scheme. Every unrestricted Common row
parameter assignment instantiates a returned scheme to a model. Every model
is recovered by substituting its original rows, with literal equality.

No support predicate, caller fuel, solver-success premise, or residual model
condition appears in the principal or rejection theorem. The soundness theorem
uses only membership in the actual returned finite list. This remains a row
foundation; it does not add request syntax to `Core.infer`.
-/

namespace Yulang.CommonRowHeadSolver

open Common (Row Occurrence)
open CommonRowHeadFlow

variable {n : Nat}

def solve (problem : Problem n) : List (Scheme n) :=
  if check problem then [coalesce problem] else []

theorem mem_solve (problem : Problem n) (scheme : Scheme n) :
    scheme ∈ solve problem ↔ check problem = true ∧ scheme = coalesce problem := by
  cases checked : check problem <;> simp [solve, checked]

/-- Every finite problem, every returned scheme, and every unrestricted
assignment of possibly infinite Common rows. Membership is the only premise. -/
theorem all_parameters_models (problem : Problem n) (scheme : Scheme n)
    (returned : scheme ∈ solve problem) (parameters : Fin n → Row) :
    Models problem (scheme.instantiate parameters) := by
  obtain ⟨checked, rfl⟩ := (mem_solve problem scheme).mp returned
  exact coalesce_models problem checked parameters

theorem model_retraction (problem : Problem n) (rows : Fin n → Row)
    (model : Models problem rows) :
    coalesce problem ∈ solve problem ∧ (coalesce problem).instantiate rows = rows :=
  ⟨(mem_solve problem _).mpr ⟨models_check model, rfl⟩,
    coalesce_retraction problem rows model⟩

/-- All original rows are independent and are recovered literally. The
existential parameter assignment has no additional predicate. -/
theorem solve_all_instances_exact (problem : Problem n) (rows : Fin n → Row) :
    Models problem rows ↔
      ∃ scheme ∈ solve problem, ∃ parameters : Fin n → Row,
        scheme.instantiate parameters = rows := by
  constructor
  · intro model
    have recovered := model_retraction problem rows model
    exact ⟨coalesce problem, recovered.1, rows, recovered.2⟩
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact all_parameters_models problem scheme returned parameters

theorem check_iff_satisfiable (problem : Problem n) :
    check problem = true ↔ ∃ rows, Models problem rows :=
  ⟨fun checked => ⟨(coalesce problem).instantiate (fun _ => Common.rowEmpty),
      coalesce_models problem checked _⟩,
    fun ⟨_, model⟩ => models_check model⟩

/-- Finite rejection is exactly absence of any row model, with no grammar
or successful-solver premise and no defaulting of the surviving parameters. -/
theorem rejected_iff (problem : Problem n) :
    solve problem = [] ↔ ¬ ∃ rows, Models problem rows := by
  constructor
  · intro rejected ⟨rows, model⟩
    have returned := (model_retraction problem rows model).1
    rw [rejected] at returned
    cases returned
  · intro absent
    have unchecked : check problem ≠ true := fun checked =>
      absent ((check_iff_satisfiable problem).mp checked)
    simp [solve, unchecked]

/-- A precise explanation of rejection: some asserted occurrence flows to
a declared pure sink. No sign is erased when checking that occurrence. -/
theorem rejected_iff_head_reaches_pure (problem : Problem n) :
    solve problem = [] ↔
      ∃ source occurrence target, (source, occurrence) ∈ problem.heads ∧
        .pure target ∈ problem.flow ∧ RowFlowSchemes.Reaches problem.flow source target := by
  have empty_iff : solve problem = [] ↔ check problem = false := by
    cases checked : check problem <;> simp [solve, checked]
  rw [empty_iff]
  have false_iff : check problem = false ↔
      ∃ head ∈ problem.heads, RowFlowSchemes.forcedPure problem.flow head.1 = true := by
    simp [check, List.all_eq_false]
  rw [false_iff]
  constructor
  · rintro ⟨⟨source, occurrence⟩, member, forced⟩
    obtain ⟨target, pure, path⟩ := (RowFlowSchemes.forcedPure_exact problem.flow source).mp forced
    exact ⟨source, occurrence, target, member, pure, path⟩
  · rintro ⟨source, occurrence, target, member, pure, path⟩
    exact ⟨(source, occurrence), member,
      (RowFlowSchemes.forcedPure_exact problem.flow source).mpr ⟨target, pure, path⟩⟩

theorem no_heads_solved (flow : RowFlowSchemes.FlatProblem n) :
    solve ⟨flow, []⟩ = [coalesce ⟨flow, []⟩] := rfl

namespace Examples

def signedCycle : Problem 3 :=
  ⟨[.flow 0 1, .flow 1 0], [(0, (7, [1, -2]))]⟩

/-- Positive protection and negative debt coordinates both survive ordinary
flow propagation. This theorem makes no assumption about row parameters. -/
theorem signed_head_propagates (parameters : Fin 3 → Row) :
    ((coalesce signedCycle).instantiate parameters 1) (7, [1, -2]) := by
  apply Or.inl
  decide +kernel

def impureCycle : Problem 3 :=
  ⟨[.flow 0 1, .flow 1 0, .pure 1], [(0, (7, [1, -2]))]⟩

/-- A head is inconsistent even when the empty upper bound occurs only at a
different, transitively reachable slot; signed debt is not mistaken for empty. -/
theorem transitive_head_conflict_rejected : solve impureCycle = [] := by
  have checked : check impureCycle = false := by decide +kernel
  simp only [solve, checked, Bool.false_eq_true, ↓reduceIte]

end Examples

end Yulang.CommonRowHeadSolver
