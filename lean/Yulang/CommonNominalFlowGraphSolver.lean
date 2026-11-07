import Yulang.CommonNominalTemplateRowSolver
import Yulang.CommonNominalTypeFlow

/-!
# Directed type flows with full mixed graphs and solved literal row constraints

Directed shared free-type inequalities are solved by finite predecessor joins,
then substituted into the full mixed guarded closure. The row part is the
actual finite literal/join truth-table solver. Every row/type parameter is
unrestricted; all original rows, free types and nodes are recovered together.

This still excludes inequalities whose endpoints are constructed graph nodes
and arbitrary equality constraints tying a free type to such a node. The
actual source-generated full type graph is not declared solved.
-/

namespace Yulang.CommonNominalFlowGraphSolver

open CommonNominalCarrier
open Core.PresenceGeneration (RowTerm)
open CommonNominalTypeFlow (Edge)
open CommonNominalFieldTemplates (rowsLayer TemplateRow)

structure Problem (nodes types rows : Nat) where
  body : Fin nodes → CommonNominalSyntax.Layer (TemplateRow rows) (Fin nodes ⊕ Fin types)
  rowConstraints : CommonNominalTemplateRowPatterns.Problem rows
  typeEdges : List (Edge types)

def Problem.Models (problem : Problem nodes types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) : Prop :=
  (CommonNominalTemplateRowPatterns.Models problem.rowConstraints rowValues ∧
    CommonNominalGuardedClosure.Models (fun index => rowsLayer rowValues (problem.body index)) typeValues nodeValues) ∧
    CommonNominalTypeFlow.Models problem.typeEdges typeValues

structure Scheme (nodes types rows : Nat) where
  body : Fin nodes → CommonNominalSyntax.Layer (TemplateRow rows) (Fin nodes ⊕ Fin types)
  rowSolution : CommonNominalTemplateRowSolver.Scheme rows
  typeEdges : List (Edge types)

abbrev Scheme.Parameters (_scheme : Scheme nodes types rows) := (CommonNominalRowCells.Parameters rows) × (Fin types → Ty)

def Scheme.instantiateRows (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin rows → Row :=
  scheme.rowSolution.instantiate parameters.1

def Scheme.instantiateTypes (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin types → Ty :=
  CommonNominalTypeFlow.instantiate scheme.typeEdges parameters.2

def Scheme.instantiateValues (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin nodes → Ty :=
  CommonNominalGuardedClosure.instantiate
    (fun index => rowsLayer (scheme.instantiateRows parameters) (scheme.body index))
    (scheme.instantiateTypes parameters)

def solve (problem : Problem nodes types rows) : List (Scheme nodes types rows) :=
  (CommonNominalTemplateRowSolver.solve problem.rowConstraints).map fun rowScheme =>
    ⟨problem.body, rowScheme, problem.typeEdges⟩

private theorem type_sound (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) :
    CommonNominalTypeFlow.Models scheme.typeEdges (scheme.instantiateTypes parameters) :=
  CommonNominalTypeFlow.all_parameters_models scheme.typeEdges parameters.2

/-- Every row/type parameter product is a model of the original combined
problem, including directed shared type bounds and designated pure rows. -/
theorem all_parameters_models (problem : Problem nodes types rows) (scheme : Scheme nodes types rows)
    (returned : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    problem.Models (scheme.instantiateRows parameters) (scheme.instantiateTypes parameters)
      (scheme.instantiateValues parameters) := by
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp returned
  exact ⟨⟨CommonNominalTemplateRowSolver.all_parameters_models problem.rowConstraints rowScheme rowReturned parameters.1,
    CommonNominalGuardedClosure.all_parameter_sound _ _⟩, type_sound _ parameters⟩

private theorem equivalent_symm {first last : Ty} (same : Equivalent first last) : Equivalent last first :=
  ⟨same.2, same.1⟩
private theorem equivalent_trans {first middle last : Ty}
    (before : Equivalent first middle) (after : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩

/-- Every original row, shared free type and constructor node is recovered
simultaneously. No pure/flow/closure hypothesis remains on parameters. -/
theorem solve_all_instances_exact (problem : Problem nodes types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) :
    problem.Models rowValues typeValues nodeValues ↔
      ∃ scheme ∈ solve problem, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows parameters = rowValues ∧
        (∀ index, Equivalent (scheme.instantiateTypes parameters index) (typeValues index)) ∧
        ∀ index, Equivalent (scheme.instantiateValues parameters index) (nodeValues index) := by
  constructor
  · rintro ⟨⟨rowModel, nodeModel⟩, typeModel⟩
    obtain ⟨rowScheme, rowReturned, rowParameters, rowsSame⟩ :=
      (CommonNominalTemplateRowSolver.solve_all_instances_exact problem.rowConstraints rowValues).mp rowModel
    let scheme : Scheme nodes types rows := ⟨problem.body, rowScheme, problem.typeEdges⟩
    have freeSame := CommonNominalTypeFlow.model_retraction problem.typeEdges typeValues typeModel
    refine ⟨scheme, List.mem_map.mpr ⟨rowScheme, rowReturned, rfl⟩,
      ⟨rowParameters, typeValues⟩, rowsSame, freeSame, ?_⟩
    intro index
    change Equivalent
      (CommonNominalGuardedClosure.instantiate
        (fun index => rowsLayer (rowScheme.instantiate rowParameters) (problem.body index))
        (CommonNominalTypeFlow.instantiate problem.typeEdges typeValues) index) (nodeValues index)
    rw [rowsSame]
    exact equivalent_trans (CommonNominalGuardedClosure.parameter_congr _ _ _ freeSame index)
      (CommonNominalGuardedClosure.all_models_recovered _ typeValues nodeValues nodeModel index)
  · rintro ⟨scheme, returned, parameters, rowsSame, typesSame, nodesSame⟩
    obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp returned
    have rowModel := CommonNominalTemplateRowSolver.all_parameters_models problem.rowConstraints rowScheme rowReturned parameters.1
    have actualRows : rowScheme.instantiate parameters.1 = rowValues := rowsSame
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [actualRows] using rowModel
    · apply (CommonNominalGuardedClosure.models_exact _ typeValues nodeValues).mpr
      intro index
      have freeCongr := CommonNominalGuardedClosure.parameter_congr
        (fun index => rowsLayer rowValues (problem.body index)) _ typeValues typesSame index
      have nodes := nodesSame index
      simp only [Scheme.instantiateValues, Scheme.instantiateRows, actualRows] at nodes
      exact equivalent_trans (equivalent_symm freeCongr) nodes
    · exact CommonNominalTypeFlow.models_of_recovered problem.typeEdges parameters.2 typeValues typesSame

end Yulang.CommonNominalFlowGraphSolver
