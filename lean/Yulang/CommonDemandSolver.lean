import Yulang.DemandBoundPropagation
import Yulang.CoreCommonInference

/-!
# Pull-bound queries inside the actual common solver

`request` queries one bound at a fixed shared-pool snapshot. `rigid` uses the
same reverse worklist collector when a rigid upper check asks for its lower
contributions. `finishAll` runs every remaining rigid/row check with that
collector and returns exactly the reference solver's finite schemes.

This is a replacement of the bound-query computation, not a proof that an
unsaturated snapshot already describes a final solver instance. The full
completion operation still checks all components and all alternatives. In
particular, an inconsistent unrequested component can make that completed
scheme list empty. Partial bounds are not public schemes or permission to
execute a function that has not completed its required checks.
-/

namespace Yulang.CommonDemandSolver

open LayerBoundTemplates (Problem)
open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPoolQueries (queries)
open CommonBoundRefWorklist (Index Edge State)
open CommonPresenceConstraintGraph (Compiled)
open CommonBoundRefSolver (Scheme)

variable {m : Nat}

/-- A concrete bound request at the current constraint snapshot. The root
keeps the original shared input ID and asks only one polarity. -/
def request (pool : Pool m) (edges : List (Edge pool))
    (root : DemandBoundPropagation.Root m) : List (Index pool) :=
  DemandBoundPropagation.request
    (CommonBoundRefCoalescing.template pool (queries pool) edges) root

/-- This is the reference bound computation used by the eager solver's
coalescing/rigid-discovery stage, at the same snapshot. -/
theorem request_exact (pool : Pool m) (edges : List (Edge pool))
    (root : DemandBoundPropagation.Root m) :
    request pool edges root = DemandBoundPropagation.reference
      (CommonBoundRefCoalescing.template pool (queries pool) edges) root :=
  DemandBoundPropagation.request_exact _ root

/-- All upper checks are requested when full verification is required.
The lower collector for each request traverses predecessors of that root. -/
def rigidComparisons {Bound : Type} (problem : Problem m Bound) : List (Bound × Bound) :=
  problem.flatMap fun
    | .lower _ _ | .flow _ _ => []
    | .upper source bound =>
        (DemandBoundPropagation.lowerBounds problem source).map fun lowerBound => (lowerBound, bound)
    | .check source target => [(source, target)]

theorem rigidComparisons_exact {Bound : Type} (problem : Problem m Bound) :
    rigidComparisons problem = CommonBoundCoalescing.rigidComparisons problem := by
  simp only [rigidComparisons, CommonBoundCoalescing.rigidComparisons,
    DemandBoundPropagation.lowerBounds_exact]
  rfl

def rigid (pool : Pool m) (edges : List (Edge pool)) : List (Edge pool) :=
  rigidComparisons (CommonBoundRefCoalescing.template pool (queries pool) edges)

theorem rigid_exact (pool : Pool m) (edges : List (Edge pool)) :
    rigid pool edges = CommonBoundRefWorklist.rigid pool edges :=
  rigidComparisons_exact _

/-- Complete rigid inspection using the pull-bound collector, with the same
finite inventory, branch order and row checks as the reference worklist. -/
def finishWorklist (pool : Pool m) (edges : List (Edge pool)) : List (State pool) :=
  FiniteBranchingWorklist.run (CommonBoundRefWorklist.inventory pool) (rigid pool)
    (CommonBoundRefWorklist.inspect pool) edges []

theorem finishWorklist_exact (pool : Pool m) (edges : List (Edge pool)) :
    finishWorklist pool edges = CommonBoundRefWorklist.run pool edges := by
  have same : rigid pool = CommonBoundRefWorklist.rigid pool := funext (rigid_exact pool)
  simp only [finishWorklist, CommonBoundRefWorklist.run, same]

/-- At every state actually returned by completion, every requested bound
agrees with the reference at that state and no rigid comparison is pending.
This is still a statement about the same snapshot, not a global family
projection for a partially checked source. -/
theorem finished_request_exact (pool : Pool m) (edges : List (Edge pool))
    (state : State pool) (returned : state ∈ finishWorklist pool edges)
    (root : DemandBoundPropagation.Root m) :
    request pool state.edges root = DemandBoundPropagation.reference
        (CommonBoundRefCoalescing.template pool (queries pool) state.edges) root ∧
      FiniteBranchingWorklist.pending (CommonBoundRefWorklist.inventory pool)
        (CommonBoundRefWorklist.rigid pool) state = none := by
  rw [finishWorklist_exact] at returned
  exact ⟨request_exact pool state.edges root,
    CommonBoundRefWorklist.run_finished pool edges state returned⟩

def finishProblem (problem : CommonPresenceConstraintGraph.Problem m) :
    List (Scheme m problem.pool.size) :=
  match CommonRowDeclarations.declareRows problem.rows with
  | none => []
  | some originalRows =>
      (finishWorklist problem.pool (CommonBoundRefWorklist.originalEdges problem.pool problem.edges)).flatMap
        (CommonBoundRefSolver.solveState problem.pool originalRows)

theorem finishProblem_exact (problem : CommonPresenceConstraintGraph.Problem m) :
    finishProblem problem = CommonBoundRefSolver.solveProblem problem := by
  simp only [finishProblem, CommonBoundRefSolver.solveProblem, finishWorklist_exact]
  rfl

/-- Full completion. No call to the reference `solveAll` occurs here. -/
def finishAll (compiled : Compiled m) : List (Scheme m compiled.size) :=
  match compiled.origin with
  | none => []
  | some problem =>
      if same : problem.pool.size = compiled.size then
        (finishProblem problem).map (CommonBoundRefSolver.castScheme same)
      else []

/-- Every compiled input, including missing/inconsistent origin metadata:
the completed computation has exactly the reference finite scheme list. -/
theorem finishAll_exact (compiled : Compiled m) :
    finishAll compiled = CommonBoundRefSolver.solveAll compiled := by
  simp only [finishAll, CommonBoundRefSolver.solveAll, finishProblem_exact]
  rfl

theorem finishAll_rejected_iff (compiled : Compiled m) :
    finishAll compiled = [] ↔ CommonBoundRefSolver.solveAll compiled = [] := by
  rw [finishAll_exact]

/-- All free parameters remain unrestricted after replacing propagation. -/
theorem all_parameter_sound (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (scheme : Scheme m (CommonPresenceConstraintGraph.compile atoms).size)
    (returned : scheme ∈ finishAll (CommonPresenceConstraintGraph.compile atoms))
    (rowParameters : Fin m → Common.Row) (parameters : scheme.Parameters) :
    (CommonPresenceConstraintGraph.compile atoms).Models
      (scheme.instantiateRows rowParameters) (scheme.instantiateValues rowParameters parameters) := by
  rw [finishAll_exact] at returned
  exact CommonBoundRefSolver.all_parameter_sound atoms scheme returned rowParameters parameters

def finishClause (clause : PresenceNormalForm.Clause (Option Empty)) : List CommonSolvedSource.Scheme :=
  (finishAll (CommonPresenceConstraintGraph.compile clause.pack)).map (CommonSolvedSource.ofClause clause)

theorem finishClause_exact (clause : PresenceNormalForm.Clause (Option Empty)) :
    finishClause clause = CommonSolvedSource.solveClause clause := by
  simp only [finishClause, CommonSolvedSource.solveClause, finishAll_exact]

def finishSource (expression : Inference.Expr) : List CommonSolvedSource.Scheme :=
  (PresenceNormalForm.normalise
    (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)).flatMap
      finishClause

theorem finishSource_exact (expression : Inference.Expr) :
    finishSource expression = CommonSolvedSource.inferSource expression := by
  have same : finishClause = CommonSolvedSource.solveClause := funext finishClause_exact
  simp only [finishSource, CommonSolvedSource.inferSource, same]

def finishCoreSchemes (expression : Core.Required.Term) : List CommonSolvedSource.Scheme :=
  if Core.CommonSyntax.covered expression then finishSource (Core.CommonSyntax.lower expression) else []

theorem finishCoreSchemes_exact (expression : Core.Required.Term) :
    finishCoreSchemes expression = CommonSolvedCoreSyntax.infer expression := by
  simp only [finishCoreSchemes, CommonSolvedCoreSyntax.infer, finishSource_exact]

/-- Classification is exposed only after the full check has completed. -/
def finishCore (expression : Core.Required.Term) : Core.CommonInference.Result :=
  Core.CommonInference.finish (finishCoreSchemes expression)

theorem finishCore_exact (expression : Core.Required.Term) :
    finishCore expression = Core.infer expression := by
  simp only [finishCore, Core.infer, finishCoreSchemes_exact]

theorem finishCore_principal (expression : Core.Required.Term)
    (result : Core.PresenceGeneration.Comp Common.model) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression result ↔
      ∃ scheme ∈ finishCore expression, ∃ parameters : scheme.Parameters,
        Core.PresenceGeneration.Comp.le Common.model (scheme.instantiate parameters) result := by
  rw [finishCore_exact]
  exact Core.infer_principal expression result

theorem finishCore_instantiates (expression : Core.Required.Term) (scheme : CommonSolvedSource.Scheme)
    (returned : scheme ∈ finishCore expression) (parameters : scheme.Parameters) :
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression (scheme.instantiate parameters) := by
  rw [finishCore_exact] at returned
  exact Core.infer_instantiates expression scheme returned parameters

theorem finishCore_rejected_iff (expression : Core.Required.Term) :
    finishCore expression = .rejected ↔
      ¬ ∃ result, Core.Typing (Core.CommonSyntax.model Common.model) [] expression result := by
  rw [finishCore_exact]
  exact Core.infer_rejected_iff expression

end Yulang.CommonDemandSolver
