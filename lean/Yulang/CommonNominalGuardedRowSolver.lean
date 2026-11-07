import Yulang.CommonNominalGuardedClosure
import Yulang.CommonRowHeadSolver

/-!
# Finite mixed nominal constructor graphs with pure row constraints

The input is finite row syntax, a finite mixed constructor body, and the actual
row-flow/head/pure problem. All row and free type parameters are unrestricted.
Solving uses the existing exact row family and the new mixed guarded closure.
Every original row and every original node value is recovered simultaneously.

This does not solve additional type-subtyping edges or generate a source
construction problem. Those are not silently stored as parameter conditions.
-/

namespace Yulang.CommonNominalGuardedRowSolver

open CommonNominalCarrier
open Core.PresenceGeneration (RowTerm)

def rowMeaning (rows : Fin count → Row) (term : RowTerm (Fin count)) : Row :=
  term.eval model (fun index => (.bottom, rows index))

def rowsLayer (rows : Fin count → Row) :
    CommonNominalSyntax.Layer (RowTerm (Fin count)) Index → CommonNominalSyntax.Layer Row Index
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (rowsLayer rows first) (rowsLayer rows last)
  | .inter first last => .inter (rowsLayer rows first) (rowsLayer rows last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload rest => .record label payload (rowsLayer rows rest)
  | .recordDefault label source fallback => .recordDefault label (rowsLayer rows source) fallback
  | .variant label payload => .variant label payload
  | .arrow input incoming output outgoing => .arrow input (rowMeaning rows incoming) output (rowMeaning rows outgoing)
  | .mask hidden source => .mask hidden (rowsLayer rows source)
  | .nominal name arguments => .nominal name (arguments.map (Sum.map id (rowMeaning rows)))

structure Problem (nodes types rows : Nat) where
  body : Fin nodes → CommonNominalSyntax.Layer (RowTerm (Fin rows)) (Fin nodes ⊕ Fin types)
  rowConstraints : CommonRowHeadFlow.Problem rows

def Problem.Models (problem : Problem nodes types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) : Prop :=
  CommonRowHeadFlow.Models problem.rowConstraints rowValues ∧
    CommonNominalGuardedClosure.Models (fun index => rowsLayer rowValues (problem.body index)) typeValues nodeValues

structure Scheme (nodes types rows : Nat) where
  body : Fin nodes → CommonNominalSyntax.Layer (RowTerm (Fin rows)) (Fin nodes ⊕ Fin types)
  rowSolution : CommonRowHeadFlow.Scheme rows

abbrev Scheme.Parameters (_scheme : Scheme nodes types rows) := (Fin rows → Row) × (Fin types → Ty)

def Scheme.instantiateRows (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin rows → Row :=
  scheme.rowSolution.instantiate parameters.1

def Scheme.instantiateValues (scheme : Scheme nodes types rows) (parameters : scheme.Parameters) : Fin nodes → Ty :=
  CommonNominalGuardedClosure.instantiate
    (fun index => rowsLayer (scheme.instantiateRows parameters) (scheme.body index)) parameters.2

def solve (problem : Problem nodes types rows) : List (Scheme nodes types rows) :=
  (CommonRowHeadSolver.solve problem.rowConstraints).map (fun rows => ⟨problem.body, rows⟩)

/-- Arbitrary original signed rows, mixed recursive nominal constructors and
unrestricted free type parameters. Membership is the only solver premise. -/
theorem all_parameters_models (problem : Problem nodes types rows) (scheme : Scheme nodes types rows)
    (returned : scheme ∈ solve problem) (parameters : scheme.Parameters) :
    problem.Models (scheme.instantiateRows parameters) parameters.2 (scheme.instantiateValues parameters) := by
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp returned
  exact ⟨CommonRowHeadSolver.all_parameters_models problem.rowConstraints rowScheme rowReturned parameters.1,
    CommonNominalGuardedClosure.all_parameter_sound _ parameters.2⟩

/-- Pure immediate-row constraints are solved, not left as a predicate on the
row parameters. Every returned scheme has literally empty designated rows. -/
theorem pure_row_empty (problem : Problem nodes types rows) (scheme : Scheme nodes types rows)
    (returned : scheme ∈ solve problem) (parameters : scheme.Parameters) (index : Fin rows)
    (pure : RowFlowSchemes.FlatConstraint.pure index ∈ problem.rowConstraints.flow) :
    scheme.instantiateRows parameters index = Common.rowEmpty := by
  have rowModel := (all_parameters_models problem scheme returned parameters).1.1
  exact Common.rowLe_antisymm (rowModel (.pure index) pure) (Common.rowEmpty_le _)

/-- Every original row is recovered with literal equality, and every original
node value with demand equivalence. The same free type parameters are retained.
No residual model/purity/closure condition is placed on the parameters. -/
theorem solve_all_instances_exact (problem : Problem nodes types rows) (rowValues : Fin rows → Row)
    (typeValues : Fin types → Ty) (nodeValues : Fin nodes → Ty) :
    problem.Models rowValues typeValues nodeValues ↔
      ∃ scheme ∈ solve problem, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows parameters = rowValues ∧ parameters.2 = typeValues ∧
          ∀ index, Equivalent (scheme.instantiateValues parameters index) (nodeValues index) := by
  constructor
  · rintro ⟨rowModel, valueModel⟩
    obtain ⟨rowScheme, returned, rowParameters, rowsSame⟩ :=
      (CommonRowHeadSolver.solve_all_instances_exact problem.rowConstraints rowValues).mp rowModel
    let scheme : Scheme nodes types rows := ⟨problem.body, rowScheme⟩
    refine ⟨scheme, List.mem_map.mpr ⟨rowScheme, returned, rfl⟩, ⟨rowParameters, typeValues⟩, rowsSame, rfl, ?_⟩
    intro index
    change Equivalent
      (CommonNominalGuardedClosure.instantiate
        (fun index => rowsLayer (rowScheme.instantiate rowParameters) (problem.body index)) typeValues index)
      (nodeValues index)
    rw [rowsSame]
    exact CommonNominalGuardedClosure.all_models_recovered _ typeValues nodeValues valueModel index
  · rintro ⟨scheme, returned, parameters, rowsSame, typesSame, recovered⟩
    obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp returned
    have rowModel := CommonRowHeadSolver.all_parameters_models problem.rowConstraints rowScheme rowReturned parameters.1
    have sameRows : rowScheme.instantiate parameters.1 = rowValues := rowsSame
    refine ⟨?_, ?_⟩
    · simpa only [sameRows] using rowModel
    · apply (CommonNominalGuardedClosure.models_exact _ typeValues nodeValues).mpr
      intro index
      simpa only [Scheme.instantiateValues, Scheme.instantiateRows, sameRows, typesSame] using recovered index

end Yulang.CommonNominalGuardedRowSolver
