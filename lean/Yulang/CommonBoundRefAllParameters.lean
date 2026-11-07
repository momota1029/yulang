import Yulang.CommonBoundRefClosedSoundness
import Yulang.CommonBoundRefWorklistRows

/-!
# Closed saturation branches have unrestricted row and type parameters

The actual worklist supplies closure and the finite constructor inspection.
The actual row family supplies every row auxiliary and removes the remaining
literal-true checks. Consequently every row/type/recursive parameter choice
satisfies all final edges and the original constructor equations. No
residual predicate is imposed on any parameter.

The generated source/Core statements also retain the original row
constraints and restrict the values to the original shared node IDs.
-/

namespace Yulang.CommonBoundRefAllParameters

open Common (Ty Row)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Realizes EdgesHold splitAtoms compile)
open CommonOptionalPoolQueries (queries)
open CommonOptionalPool (restrictValues)
open CommonBoundRefWorklist (Edge State run originalEdges)
open CommonBoundRefClosedSoundness (Extended encodedEdges)
open CommonGeneratedPoolRows (AllSimpleRows)
open CommonRowTailInference (RowConstraint RowsHold)

variable {m : Nat}

/-- A fixed finite row scheme and clamped graph. Membership and row syntax
are used only to construct the finite row declaration, not as parameters. -/
def family (pool : Pool m) (good : AllSimpleRows pool) (edges : List (Edge pool))
    (state : State pool) (returned : state ∈ run pool edges)
    (original : List (RowConstraint m)) : CommonClampedRowFamily.Scheme m :=
  CommonBoundRefWorklistRows.family pool (Extended pool) (encodedEdges pool state)
    original state.aux (CommonBoundRefWorklistRows.run_all_rows pool good edges state returned)

theorem saturation_closed (pool : Pool m) (edges : List (Edge pool)) (state : State pool)
    (returned : state ∈ run pool edges) :
    FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
        (CommonBoundRefWorklist.inspect pool) state ∧
      FiniteBranchingWorklist.pending (CommonBoundRefWorklist.inventory pool)
        (CommonBoundRefWorklist.rigid pool) state = none ∧
      state.trace.length ≤ (5 * pool.size + 3) ^ 2 :=
  ⟨CommonBoundRefWorklist.run_closed pool edges state returned,
    CommonBoundRefWorklist.run_finished pool edges state returned,
    (CommonBoundRefWorklist.run_bound pool edges state returned).2.2⟩

/-- Arbitrary independent row parameters, original type parameters and
extended recursive-node parameters. All constraints hold simultaneously. -/
theorem all_parameters_models (pool : Pool m) (good : AllSimpleRows pool)
    (edges : List (Edge pool)) (state : State pool) (returned : state ∈ run pool edges)
    (original : List (RowConstraint m)) (rowParameters : Fin m → Row)
    (parameters : (family pool good edges state returned original).Parameters) :
    let scheme := family pool good edges state returned original
    let rows := scheme.instantiateRows rowParameters
    let values := scheme.instantiateValues rowParameters parameters
    Realizes (Extended pool) rows values ∧ EdgesHold (encodedEdges pool state) values ∧
      RowsHold original rows := by
  let scheme := family pool good edges state returned original
  let rows := scheme.instantiateRows rowParameters
  let values := scheme.instantiateValues rowParameters parameters
  have rowFacts := CommonBoundRefWorklistRows.run_family_all_rows pool (Extended pool) good
    (encodedEdges pool state) original edges state returned rowParameters
    (restrictValues pool (queries pool) values)
  exact ⟨scheme.instantiate_realizes rowParameters parameters,
    CommonBoundRefClosedSoundness.returned_solve_soundness pool edges state returned
      rows parameters.1 parameters.2 rowFacts.2,
    rowFacts.1⟩

theorem original_edges_retained (pool : Pool m)
    (edges : List (Fin pool.size × Fin pool.size)) (state : State pool)
    (returned : state ∈ run pool (originalEdges pool edges))
    (values : Fin (Extended pool).size → Ty) (valid : EdgesHold (encodedEdges pool state) values) :
    EdgesHold edges (restrictValues pool (queries pool) values) := by
  intro edge member
  have initial : (CommonBoundRefCoalescing.original pool (queries pool) edge.1,
      CommonBoundRefCoalescing.original pool (queries pool) edge.2) ∈ originalEdges pool edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have retained := CommonBoundRefWorklist.run_retains pool (originalEdges pool edges) state returned initial
  have final := valid _ (List.mem_map.mpr ⟨_, retained, rfl⟩)
  exact final

def compiledFamily (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (state : State (splitAtoms atoms).pool)
    (returned : state ∈ run (splitAtoms atoms).pool
      (originalEdges (splitAtoms atoms).pool (compile atoms).edges)) : CommonClampedRowFamily.Scheme m :=
  family (splitAtoms atoms).pool (CommonGeneratedPoolRows.compiled_pool_rows atoms good)
    (originalEdges (splitAtoms atoms).pool (compile atoms).edges) state returned
    (CommonPresenceClauseFamily.declareRows atoms good)

theorem compiled_all_parameters_models (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (good : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (state : State (splitAtoms atoms).pool)
    (returned : state ∈ run (splitAtoms atoms).pool
      (originalEdges (splitAtoms atoms).pool (compile atoms).edges))
    (rowParameters : Fin m → Row) (parameters : (compiledFamily atoms good state returned).Parameters) :
    let scheme := compiledFamily atoms good state returned
    (compile atoms).Models (scheme.instantiateRows rowParameters)
      (restrictValues (splitAtoms atoms).pool (queries (splitAtoms atoms).pool)
        (scheme.instantiateValues rowParameters parameters)) := by
  have solved := all_parameters_models (splitAtoms atoms).pool
    (CommonGeneratedPoolRows.compiled_pool_rows atoms good)
    (originalEdges (splitAtoms atoms).pool (compile atoms).edges) state returned
    (CommonPresenceClauseFamily.declareRows atoms good) rowParameters parameters
  exact ⟨CommonOptionalPool.restrict_realizes _ _ _ _ solved.1,
    original_edges_retained _ _ state returned _ solved.2.1,
    (CommonPresenceClauseFamily.declared_rows_models_exact atoms good _).mp solved.2.2⟩

/-- Every actual generated source clause; syntax, support, closure, model,
solver success and fuel are not premises on the free parameters. -/
theorem generated_all_parameters_models (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (state : State (splitAtoms clause.pack).pool)
    (returned : state ∈ run (splitAtoms clause.pack).pool
      (originalEdges (splitAtoms clause.pack).pool (compile clause.pack).edges))
    (rowParameters : Fin (clause.locals + 1) → Row)
    (parameters : (compiledFamily clause.pack
      (PresenceSourceConstraintSupport.generated_row_shapes expression clause member) state returned).Parameters) :
    let scheme := compiledFamily clause.pack
      (PresenceSourceConstraintSupport.generated_row_shapes expression clause member) state returned
    (compile clause.pack).Models (scheme.instantiateRows rowParameters)
      (restrictValues (splitAtoms clause.pack).pool (queries (splitAtoms clause.pack).pool)
        (scheme.instantiateValues rowParameters parameters)) :=
  compiled_all_parameters_models clause.pack
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause member) state returned rowParameters parameters

theorem generated_core_all_parameters_models (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.CoreRules.principalCore
        ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (state : State (splitAtoms clause.pack).pool)
    (returned : state ∈ run (splitAtoms clause.pack).pool
      (originalEdges (splitAtoms clause.pack).pool (compile clause.pack).edges))
    (rowParameters : Fin (clause.locals + 1) → Row)
    (parameters : (compiledFamily clause.pack
      (CommonPresenceSourceFamily.generated_core_row_shapes expression clause member) state returned).Parameters) :
    let scheme := compiledFamily clause.pack
      (CommonPresenceSourceFamily.generated_core_row_shapes expression clause member) state returned
    (compile clause.pack).Models (scheme.instantiateRows rowParameters)
      (restrictValues (splitAtoms clause.pack).pool (queries (splitAtoms clause.pack).pool)
        (scheme.instantiateValues rowParameters parameters)) :=
  compiled_all_parameters_models clause.pack
    (CommonPresenceSourceFamily.generated_core_row_shapes expression clause member) state returned rowParameters parameters

end Yulang.CommonBoundRefAllParameters
