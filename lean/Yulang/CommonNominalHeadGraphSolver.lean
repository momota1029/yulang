import Yulang.CommonNominalTemplateGraphSolver

/-!
# Actual nominal comparison compilation into mixed graph solved families

All finite nominal-head comparisons are compiled together, preserving shared
value and row slots. Mismatched IDs/arities/argument kinds are rejected by the
actual comparison compiler. Value invariance becomes representative equality;
row invariance becomes two actual template-row inequalities. These are solved
together with arbitrary literal/join row bounds and guarded mixed equations.

Known-head arguments reference free shared slots of the full regular carrier.
General subtype edges and equality constraints on constructed graph nodes are
still separate obligations; they are not stored as parameter predicates.
-/

namespace Yulang.CommonNominalHeadGraphSolver

open CommonNominalCarrier
open CommonNominalFieldTemplates (TemplateRow rowsLayer)
open CommonNominalSlotSolver (Head Edge)

structure Problem (nodes slots : Nat) where
  body : Fin nodes → CommonNominalSyntax.Layer (TemplateRow slots) (Fin nodes ⊕ Fin slots)
  rows : CommonNominalTemplateRowPatterns.Problem slots
  comparisons : List (Head slots × Head slots)

def Problem.Models (problem : Problem nodes slots) (rows : Fin slots → Row)
    (types : Fin slots → Ty) (values : Fin nodes → Ty) : Prop :=
  (CommonNominalTemplateRowPatterns.Models problem.rows rows ∧
    CommonNominalGuardedClosure.Models (fun index => rowsLayer rows (problem.body index)) types values) ∧
    ∀ pair ∈ problem.comparisons, CommonNominalCarrier.Subtype
      (pair.1.meaning (fun index => (types index, rows index)))
      (pair.2.meaning (fun index => (types index, rows index)))

def rowEdges (edges : List (Edge slots)) : CommonNominalTemplateRowPatterns.Problem slots :=
  edges.flatMap fun edge => [(.var edge.1, .var edge.2), (.var edge.2, .var edge.1)]

theorem row_edges_exact (edges : List (Edge slots)) (rows : Fin slots → Row) :
    CommonNominalTemplateRowPatterns.Models (rowEdges edges) rows ↔
      ∀ edge ∈ edges, rows edge.1 = rows edge.2 := by
  constructor
  · intro models edge present
    exact Common.rowLe_antisymm
      (models (.var edge.1, .var edge.2) (List.mem_flatMap.mpr ⟨edge, present, by simp⟩))
      (models (.var edge.2, .var edge.1) (List.mem_flatMap.mpr ⟨edge, present, by simp⟩))
  · intro equalities constraint present
    obtain ⟨edge, member, edgeConstraint⟩ := List.mem_flatMap.mp present
    have same := equalities edge member
    rcases List.mem_cons.mp edgeConstraint with before | after
    · subst constraint
      change Common.rowLe (rows edge.1) (rows edge.2)
      rw [same]
      exact Common.rowLe_refl _
    · have after := List.mem_singleton.mp after
      subst constraint
      change Common.rowLe (rows edge.2) (rows edge.1)
      rw [same]
      exact Common.rowLe_refl _

def ofEqualities (problem : Problem nodes slots) (equalities : CommonNominalSlotSolver.Problem slots) :
    CommonNominalTemplateGraphSolver.Problem nodes slots slots :=
  ⟨problem.body, problem.rows ++ rowEdges equalities.rowEdges, equalities.valueEdges⟩

private theorem of_equalities_models (problem : Problem nodes slots)
    (equalities : CommonNominalSlotSolver.Problem slots) (rows : Fin slots → Row)
    (types : Fin slots → Ty) (values : Fin nodes → Ty) :
    (ofEqualities problem equalities).Models rows types values ↔
      (CommonNominalTemplateRowPatterns.Models problem.rows rows ∧
        CommonNominalGuardedClosure.Models (fun index => rowsLayer rows (problem.body index)) types values) ∧
        equalities.Models (fun index => (types index, rows index)) := by
  simp only [ofEqualities, CommonNominalTemplateGraphSolver.Problem.Models,
    CommonNominalTemplateRowPatterns.Models, List.forall_mem_append, CommonNominalSlotSolver.Problem.Models]
  have rowsExact := row_edges_exact equalities.rowEdges rows
  change (((_ ∧ CommonNominalTemplateRowPatterns.Models (rowEdges equalities.rowEdges) rows) ∧ _) ∧ _) ↔ _
  rw [rowsExact]
  exact ⟨fun model => ⟨⟨model.1.1.1, model.1.2⟩, model.2, model.1.1.2⟩,
    fun model => ⟨⟨⟨model.1.1, model.2.2⟩, model.1.2⟩, model.2.1⟩⟩

def compile (problem : Problem nodes slots) : Option (CommonNominalTemplateGraphSolver.Problem nodes slots slots) :=
  (CommonNominalSlotSolver.compileAll problem.comparisons).map (ofEqualities problem)

theorem compile_exact (problem : Problem nodes slots) (rows : Fin slots → Row)
    (types : Fin slots → Ty) (values : Fin nodes → Ty) :
    (∃ graph, compile problem = some graph ∧ graph.Models rows types values) ↔ problem.Models rows types values := by
  have comparisonExact := CommonNominalSlotSolver.compile_all_exact problem.comparisons
    (fun index => (types index, rows index))
  cases compiled : CommonNominalSlotSolver.compileAll problem.comparisons with
  | none =>
      constructor
      · rintro ⟨graph, found, _⟩
        simp [compile, compiled] at found
      · intro model
        obtain ⟨equalities, found, _⟩ := comparisonExact.mpr model.2
        simp [compiled] at found
  | some equalities =>
      simp only [compiled, Option.some.injEq, exists_eq_left'] at comparisonExact
      simp only [compile, compiled, Option.map_some, Option.some.injEq, exists_eq_left']
      exact (of_equalities_models problem equalities rows types values).trans (and_congr Iff.rfl comparisonExact)

abbrev Scheme (nodes slots : Nat) := CommonNominalTemplateGraphSolver.Scheme nodes slots slots

def solve (problem : Problem nodes slots) : List (Scheme nodes slots) :=
  match compile problem with
  | none => []
  | some graph => CommonNominalTemplateGraphSolver.solve graph

private theorem returned (problem : Problem nodes slots) (scheme : Scheme nodes slots) :
    scheme ∈ solve problem ↔ ∃ graph, compile problem = some graph ∧ scheme ∈ CommonNominalTemplateGraphSolver.solve graph := by
  cases compiled : compile problem <;> simp [solve, compiled]

theorem all_parameters_models (problem : Problem nodes slots) (scheme : Scheme nodes slots)
    (member : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    problem.Models (scheme.instantiateRows parameters) (scheme.instantiateTypes parameters)
      (scheme.instantiateValues parameters) := by
  obtain ⟨graph, compiled, returned⟩ := (returned problem scheme).mp member
  exact (compile_exact problem _ _ _).mp
    ⟨graph, compiled, CommonNominalTemplateGraphSolver.all_parameters_models graph scheme returned parameters⟩

theorem solve_all_instances_exact (problem : Problem nodes slots) (rows : Fin slots → Row)
    (types : Fin slots → Ty) (values : Fin nodes → Ty) :
    problem.Models rows types values ↔ ∃ scheme ∈ solve problem, ∃ parameters : scheme.Parameters,
      scheme.instantiateRows parameters = rows ∧
      (∀ index, Equivalent (scheme.instantiateTypes parameters index) (types index)) ∧
      ∀ index, Equivalent (scheme.instantiateValues parameters index) (values index) := by
  constructor
  · intro model
    obtain ⟨graph, compiled, models⟩ := (compile_exact problem rows types values).mpr model
    obtain ⟨scheme, member, parameters, same⟩ :=
      (CommonNominalTemplateGraphSolver.solve_all_instances_exact graph rows types values).mp models
    exact ⟨scheme, (returned problem scheme).mpr ⟨graph, compiled, member⟩, parameters, same⟩
  · rintro ⟨scheme, member, parameters, same⟩
    obtain ⟨graph, compiled, returned⟩ := (returned problem scheme).mp member
    exact (compile_exact problem rows types values).mp
      ⟨graph, compiled, (CommonNominalTemplateGraphSolver.solve_all_instances_exact graph rows types values).mpr
        ⟨scheme, returned, parameters, same⟩⟩

end Yulang.CommonNominalHeadGraphSolver
