import Yulang.CommonNominalGuardedRowSolver
import Yulang.CommonNominalSlotSolver

/-!
# Shared invariant parameters, mixed guarded constructors and pure rows

The solver composes value-equivalence components, actual signed row/head/pure
solving, and mixed nominal regular closure. All parameters remain unrestricted.
Original free type slots and every node are recovered modulo demand equivalence;
original rows are recovered literally. No model condition is hidden in a scheme.

Only equality edges on shared free type slots are handled here. General type
inequalities and equality edges on arbitrary constructed nodes are not claimed.
-/

namespace Yulang.CommonNominalInvariantGraphSolver

open CommonNominalCarrier
open Core.PresenceGeneration (RowTerm)
open CommonNominalSlotSolver (Edge representative)
open CommonNominalGuardedRowSolver (rowsLayer)

structure Problem (nodes types rows : Nat) where
  graph : CommonNominalGuardedRowSolver.Problem nodes types rows
  equalities : List (Edge types)

def typeProblem (edges : List (Edge types)) : CommonNominalSlotSolver.Problem types := ⟨edges, []⟩

def Problem.Models (problem : Problem nodes types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) : Prop :=
  problem.graph.Models rowValues typeValues nodeValues ∧
    ∀ edge ∈ problem.equalities, Equivalent (typeValues edge.1) (typeValues edge.2)

structure Scheme (nodes types rows : Nat) where
  body : Fin nodes → CommonNominalSyntax.Layer (RowTerm (Fin rows)) (Fin nodes ⊕ Fin types)
  rowSolution : CommonRowHeadFlow.Scheme rows
  equalities : List (Edge types)

abbrev Scheme.Parameters (_scheme : Scheme nodes types rows) := (Fin rows → Row) × (Fin types → Ty)

def Scheme.instantiateRows (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin rows → Row :=
  scheme.rowSolution.instantiate parameters.1

def Scheme.instantiateTypes (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin types → Ty :=
  fun index => parameters.2 (representative scheme.equalities index)

def Scheme.instantiateValues (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin nodes → Ty :=
  CommonNominalGuardedClosure.instantiate
    (fun index => rowsLayer (scheme.instantiateRows parameters) (scheme.body index))
    (scheme.instantiateTypes parameters)

def solve (problem : Problem nodes types rows) : List (Scheme nodes types rows) :=
  (CommonRowHeadSolver.solve problem.graph.rowConstraints).map fun rowScheme =>
    ⟨problem.graph.body, rowScheme, problem.equalities⟩

private theorem type_sound (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) :
    ∀ edge ∈ scheme.equalities, Equivalent
      (scheme.instantiateTypes parameters edge.1) (scheme.instantiateTypes parameters edge.2) :=
  (CommonNominalSlotSolver.all_parameter_sound (typeProblem scheme.equalities)
    ⟨parameters.2, fun _ => Common.rowEmpty⟩).1

/-- Every row/type parameter product is a model of the original combined
problem, including shared nominal invariance and designated pure rows. -/
theorem all_parameters_models (problem : Problem nodes types rows) (scheme : Scheme nodes types rows)
    (returned : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    problem.Models (scheme.instantiateRows parameters) (scheme.instantiateTypes parameters)
      (scheme.instantiateValues parameters) := by
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp returned
  exact ⟨⟨CommonRowHeadSolver.all_parameters_models problem.graph.rowConstraints rowScheme rowReturned parameters.1,
    CommonNominalGuardedClosure.all_parameter_sound _ _⟩, type_sound _ parameters⟩

private theorem equivalent_symm {first last : Ty} (same : Equivalent first last) : Equivalent last first :=
  ⟨same.2, same.1⟩
private theorem equivalent_trans {first middle last : Ty}
    (before : Equivalent first middle) (after : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩

/-- Every original row, shared free type and constructor node is recovered
simultaneously. No pure/equality/closure hypothesis remains on parameters. -/
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
      (CommonRowHeadSolver.solve_all_instances_exact problem.graph.rowConstraints rowValues).mp rowModel
    let scheme : Scheme nodes types rows := ⟨problem.graph.body, rowScheme, problem.equalities⟩
    have typeModels : (typeProblem problem.equalities).Models
        (fun index => (typeValues index, Common.rowEmpty)) := ⟨typeModel, by simp [typeProblem]⟩
    have freeSame (index : Fin types) :
        Equivalent (typeValues (representative problem.equalities index)) (typeValues index) := by
      exact (CommonNominalSlotSolver.direct_retraction
        (typeProblem problem.equalities) (fun index => (typeValues index, Common.rowEmpty)) typeModels index).1
    refine ⟨scheme, List.mem_map.mpr ⟨rowScheme, rowReturned, rfl⟩,
      ⟨rowParameters, typeValues⟩, rowsSame, freeSame, ?_⟩
    intro index
    change Equivalent
      (CommonNominalGuardedClosure.instantiate
        (fun index => rowsLayer (rowScheme.instantiate rowParameters) (problem.graph.body index))
        (fun index => typeValues (representative problem.equalities index)) index) (nodeValues index)
    rw [rowsSame]
    exact equivalent_trans (CommonNominalGuardedClosure.parameter_congr _ _ _ freeSame index)
      (CommonNominalGuardedClosure.all_models_recovered _ typeValues nodeValues nodeModel index)
  · rintro ⟨scheme, returned, parameters, rowsSame, typesSame, nodesSame⟩
    obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp returned
    have rowModel := CommonRowHeadSolver.all_parameters_models problem.graph.rowConstraints rowScheme rowReturned parameters.1
    have actualRows : rowScheme.instantiate parameters.1 = rowValues := rowsSame
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [actualRows] using rowModel
    · apply (CommonNominalGuardedClosure.models_exact _ typeValues nodeValues).mpr
      intro index
      have freeCongr := CommonNominalGuardedClosure.parameter_congr
        (fun index => rowsLayer rowValues (problem.graph.body index)) _ typeValues typesSame index
      have nodes := nodesSame index
      simp only [Scheme.instantiateValues, Scheme.instantiateRows, actualRows] at nodes
      exact equivalent_trans (equivalent_symm freeCongr) nodes
    · have typeRecovered : ∀ index, Equivalent
          ((typeProblem problem.equalities).instantiate ⟨parameters.2, fun _ => Common.rowEmpty⟩ index).1
          (typeValues index) ∧
          ((typeProblem problem.equalities).instantiate ⟨parameters.2, fun _ => Common.rowEmpty⟩ index).2 = Common.rowEmpty := by
        intro index
        exact ⟨typesSame index, rfl⟩
      exact (CommonNominalSlotSolver.models_of_recovered (typeProblem problem.equalities)
        ⟨parameters.2, fun _ => Common.rowEmpty⟩ (fun index => (typeValues index, Common.rowEmpty)) typeRecovered).1

end Yulang.CommonNominalInvariantGraphSolver
