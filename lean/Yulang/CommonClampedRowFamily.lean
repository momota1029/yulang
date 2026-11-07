import Yulang.CommonPresenceClampedBounds
import Yulang.CommonRowTailInference

/-!
# A simultaneous row and clamped-value parameter family

A scheme stores only the finite shared source pool, its ordinary edge list,
and a finite row scheme. Its parameters are arbitrary type parameters and
arbitrary recursive-node parameters, with an independent row-parameter family.
The instantiated rows are passed unchanged to the clamped value solver.

Every parameter assignment satisfies the declared row constraints, original
constructor equations, propagated variable upper bounds and variable flows.
Every independent model of the original rows, constructors and full edge
list is recovered with literal row equality and demand-equivalent node values.
Full-edge soundness of every parameter assignment is a separate obligation;
no residual predicate, semantic law field or public inference entry is added.
-/

namespace Yulang.CommonClampedRowFamily

open Common (Ty Row Subtype Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Realizes EdgesHold restrict)
open CommonPresenceVariableBounds (template)
open CommonRowTailInference (RowConstraint RowsHold rowProblem rowScheme)

variable {m : Nat}

structure Scheme (inputs : Nat) where
  pool : Pool inputs
  edges : List (Fin pool.size × Fin pool.size)
  rows : RowFlowSchemes.Scheme inputs

abbrev Scheme.Parameters (scheme : Scheme m) :=
  (Fin m → Ty) × (Fin scheme.pool.size → Ty)

def build (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (constraints : List (RowConstraint m)) : Scheme m :=
  ⟨pool, edges, rowScheme constraints⟩

def Scheme.instantiateRows (scheme : Scheme m) (rowParameters : Fin m → Row) : Fin m → Row :=
  RowFlowSchemes.instantiate Common.rowAlgebra scheme.rows rowParameters

def Scheme.instantiateValues (scheme : Scheme m) (rowParameters : Fin m → Row)
    (parameters : scheme.Parameters) : Fin scheme.pool.size → Ty :=
  CommonPresenceClampedBounds.solve scheme.pool scheme.edges
    (scheme.instantiateRows rowParameters) parameters.1 parameters.2

theorem Scheme.instantiate_realizes (scheme : Scheme m) (rowParameters : Fin m → Row)
    (parameters : scheme.Parameters) :
    Realizes scheme.pool (scheme.instantiateRows rowParameters)
      (scheme.instantiateValues rowParameters parameters) :=
  CommonPresenceClampedBounds.solve_realizes scheme.pool scheme.edges
    (scheme.instantiateRows rowParameters) parameters.1 parameters.2

/-- The constructed equation model, available to an internal depth proof;
the scheme does not store this statement or any semantic evidence. -/
theorem Scheme.instantiate_clamped_model (scheme : Scheme m) (rowParameters : Fin m → Row)
    (parameters : scheme.Parameters) :
    CommonPresenceTailRegular.Models
      (CommonPresenceClampedBounds.graph scheme.pool scheme.edges
        (scheme.instantiateRows rowParameters) parameters.1)
      (scheme.instantiateValues rowParameters parameters) :=
  CommonPresenceTailRegular.solveBlock_models _ parameters.2

theorem Scheme.all_parameters_below_bound (scheme : Scheme m) (rowParameters : Fin m → Row)
    (parameters : scheme.Parameters) (source : Fin m) (bound : Fin scheme.pool.size)
    (member : bound ∈ LayerBoundTemplates.upperBounds (template scheme.pool scheme.edges) source) :
    Subtype (scheme.instantiateValues rowParameters parameters (scheme.pool.input source))
      (scheme.instantiateValues rowParameters parameters bound) :=
  CommonPresenceClampedBounds.all_parameters_below_bound scheme.pool scheme.edges
    (scheme.instantiateRows rowParameters) parameters.1 parameters.2 source bound member

theorem Scheme.all_parameters_along_path (scheme : Scheme m) (rowParameters : Fin m → Row)
    (parameters : scheme.Parameters) {source target : Fin m}
    (path : LayerBoundTemplates.Reaches (template scheme.pool scheme.edges) source target) :
    Subtype (scheme.instantiateValues rowParameters parameters (scheme.pool.input source))
      (scheme.instantiateValues rowParameters parameters (scheme.pool.input target)) :=
  CommonPresenceClampedBounds.all_parameters_along_path scheme.pool scheme.edges
    (scheme.instantiateRows rowParameters) parameters.1 parameters.2 path

theorem build_rows_hold (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (constraints : List (RowConstraint m)) (rowParameters : Fin m → Row) :
    RowsHold constraints ((build pool edges constraints).instantiateRows rowParameters) :=
  CommonRowTailInference.rowScheme_models constraints rowParameters

theorem build_row_models (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (constraints : List (RowConstraint m)) (rowParameters : Fin m → Row) :
    RowFlowSchemes.Models Common.rowAlgebra (rowProblem constraints)
      ((build pool edges constraints).instantiateRows rowParameters) :=
  (CommonRowTailInference.rows_hold_iff constraints _).mp (build_rows_hold pool edges constraints rowParameters)

theorem build_all_parameters (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (constraints : List (RowConstraint m)) (rowParameters : Fin m → Row)
    (parameters : (build pool edges constraints).Parameters) :
    let scheme := build pool edges constraints
    let rows := scheme.instantiateRows rowParameters
    let values := scheme.instantiateValues rowParameters parameters
    RowsHold constraints rows ∧ Realizes pool rows values ∧
      (∀ source bound, bound ∈ LayerBoundTemplates.upperBounds (template pool edges) source →
        Subtype (values (pool.input source)) (values bound)) ∧
      (∀ source target, LayerBoundTemplates.Reaches (template pool edges) source target →
        Subtype (values (pool.input source)) (values (pool.input target))) := by
  refine ⟨build_rows_hold pool edges constraints rowParameters,
    Scheme.instantiate_realizes _ rowParameters parameters, ?_, ?_⟩
  · exact Scheme.all_parameters_below_bound _ rowParameters parameters
  · intro source target path
    exact Scheme.all_parameters_along_path _ rowParameters parameters path

/-- Every independent original model is recovered by choosing its rows,
its original variable values, and all its shared node values as parameters. -/
theorem build_retract (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (constraints : List (RowConstraint m)) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (rowModel : RowsHold constraints rows) (realizes : Realizes pool rows values)
    (valid : EdgesHold edges values) :
    (build pool edges constraints).instantiateRows rows = rows ∧
      ∀ slot, Equivalent
        ((build pool edges constraints).instantiateValues rows (restrict pool values, values) slot)
        (values slot) := by
  have rowSame := CommonRowTailInference.rowScheme_retract constraints rows rowModel
  refine ⟨rowSame, ?_⟩
  intro slot
  change Equivalent (CommonPresenceClampedBounds.solve pool edges
    (RowFlowSchemes.instantiate Common.rowAlgebra (rowScheme constraints) rows)
    (restrict pool values) values slot) (values slot)
  rw [rowSame]
  exact CommonPresenceClampedBounds.solve_retract pool edges rows values realizes valid slot

end Yulang.CommonClampedRowFamily
