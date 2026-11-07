import Yulang.CommonPatternClosedSoundness
import Yulang.CommonBoundRefSolver

/-!
# Finite solved schemes with the pattern-target worklist

The finite Scheme and its ordinary unrestricted parameter product are the
existing ones. This computation changes the worklist to the proved pattern
dispatcher. Every returned scheme is sound without a source-grammar premise;
completeness and actual generation provenance are separate obligations.
-/

namespace Yulang.CommonPatternSolvedConstraints

open Common (Ty Row Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Problem Compiled compileProblem compile splitAtoms Realizes EdgesHold)
open CommonOptionalPoolQueries (queries)
open CommonOptionalPool (restrictValues)
open CommonBoundRefWorklist (State originalEdges)
open CommonPatternBoundWorklist (run)
open CommonPatternClosedSoundness (Extended encodedEdges)
open CommonRowTailInference (RowConstraint RowsHold)
open CommonRowDeclarations (declareRows declareChecks)
open CommonBoundRefSolver (Scheme ofState solveState mem_solveState)

variable {m originalSlots : Nat}

def solveProblem (problem : Problem m) : List (Scheme m problem.pool.size) :=
  match declareRows problem.rows with
  | none => []
  | some originalRows =>
      (run problem.pool (originalEdges problem.pool problem.edges)).flatMap
        (solveState problem.pool originalRows)

def castScheme {first last : Nat} (same : first = last) (scheme : Scheme m first) : Scheme m last :=
  same ▸ scheme

@[simp] theorem castScheme_refl (scheme : Scheme m originalSlots) : castScheme rfl scheme = scheme := rfl

/-- Recover the finite source problem from metadata and check its slot count.
The solver does not compare hand-built graph fields with that metadata.
Soundness below is for actual `compile atoms`, whose metadata and fields
are constructed together. Missing metadata or a size mismatch returns no schemes. -/
def solveAll (compiled : Compiled m) : List (Scheme m compiled.size) :=
  match compiled.origin with
  | none => []
  | some problem =>
      if same : problem.pool.size = compiled.size then
        (solveProblem problem).map (castScheme same)
      else []

@[simp] theorem solveAll_compileProblem (problem : Problem m) :
    solveAll (compileProblem problem) = solveProblem problem := by
  change (if same : problem.pool.size = problem.pool.size then
    (solveProblem problem).map (castScheme same) else []) = solveProblem problem
  rw [dite_eq_left rfl]
  exact List.map_id _

@[simp] theorem solveAll_compile (atoms : List (PresenceNormalForm.Atom (Fin m))) :
    solveAll (compile atoms) = solveProblem (splitAtoms atoms) :=
  solveAll_compileProblem _

theorem mem_solveState (pool : Pool m) (originalRows : List (RowConstraint m)) (state : State pool)
    (scheme : Scheme m pool.size) :
    scheme ∈ solveState pool originalRows state ↔
      ∃ auxRows, declareChecks state.aux = some auxRows ∧ scheme = ofState pool originalRows state auxRows := by
  cases found : declareChecks state.aux <;> simp [solveState, found]

theorem mem_solveProblem (problem : Problem m) (scheme : Scheme m problem.pool.size) :
    scheme ∈ solveProblem problem ↔
      ∃ originalRows, declareRows problem.rows = some originalRows ∧
        ∃ state ∈ run problem.pool (originalEdges problem.pool problem.edges),
          ∃ auxRows, declareChecks state.aux = some auxRows ∧
            scheme = ofState problem.pool originalRows state auxRows := by
  cases found : declareRows problem.rows <;>
    simp [solveProblem, found, List.mem_flatMap, mem_solveState]

/-- Initial ordinary edges are retained literally through the indexed
worklist and the pool extension. No constructor realizer is required. -/
theorem retained_original_edges (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (state : State pool) (returned : state ∈ run pool (originalEdges pool edges))
    (values : Fin (Extended pool).size → Ty) (valid : EdgesHold (encodedEdges pool state) values) :
    EdgesHold edges (restrictValues pool (queries pool) values) := by
  intro edge included
  let original : CommonBoundRefWorklist.Edge pool :=
    (CommonBoundRefCoalescing.original pool (queries pool) edge.1,
      CommonBoundRefCoalescing.original pool (queries pool) edge.2)
  have present : original ∈ state.edges :=
    CommonPatternBoundWorklist.run_retains pool (originalEdges pool edges) state returned
      (List.mem_map.mpr ⟨edge, included, rfl⟩)
  exact valid _ (List.mem_map.mpr ⟨original, present, rfl⟩)

/-- Every parameter assignment of a successfully declared returned state
models the original graph. Static return/declaration evidence appears only
in this theorem, not in the finite scheme or its parameter domain. -/
theorem ofState_sound (problem : Problem m) (originalRows : List (RowConstraint m))
    (declaredOriginal : declareRows problem.rows = some originalRows)
    (state : State problem.pool)
    (returned : state ∈ run problem.pool (originalEdges problem.pool problem.edges))
    (auxRows : List (RowConstraint m)) (declaredAux : declareChecks state.aux = some auxRows)
    (rowParameters : Fin m → Row) (parameters : (ofState problem.pool originalRows state auxRows).Parameters) :
    (compileProblem problem).Models
      ((ofState problem.pool originalRows state auxRows).instantiateRows rowParameters)
      ((ofState problem.pool originalRows state auxRows).instantiateValues rowParameters parameters) := by
  let scheme := ofState problem.pool originalRows state auxRows
  let rows := scheme.instantiateRows rowParameters
  let allValues := scheme.family.instantiateValues rowParameters parameters
  let values := scheme.instantiateValues rowParameters parameters
  have rowModel : RowsHold (originalRows ++ auxRows) rows :=
    CommonClampedRowFamily.build_rows_hold (Extended problem.pool) (encodedEdges problem.pool state)
      (originalRows ++ auxRows) rowParameters
  have bothRows := (CommonRowDeclarations.rows_hold_append originalRows auxRows rows).mp rowModel
  have originalValid :=
    (CommonRowDeclarations.declare_rows_exact problem.rows originalRows declaredOriginal rows).mp bothRows.1
  have auxValid : CommonPatternClosedSoundness.AuxHolds problem.pool state rows allValues :=
    (CommonRowDeclarations.declare_checks_exact state.aux auxRows declaredAux rows values
      (CommonSymbolicBoundInspection.BoundRef.eval values)).mp bothRows.2
  have allRealizes : Realizes (Extended problem.pool) rows allValues :=
    CommonClampedRowFamily.Scheme.instantiate_realizes scheme.family rowParameters parameters
  have allEdges : EdgesHold (encodedEdges problem.pool state) allValues :=
    CommonPatternClosedSoundness.returned_solve_soundness problem.pool
      (originalEdges problem.pool problem.edges) state returned rows parameters.1 parameters.2 auxValid
  exact ⟨CommonOptionalPool.restrict_realizes problem.pool (queries problem.pool) rows allValues allRealizes,
    retained_original_edges problem.pool problem.edges state returned allValues allEdges, originalValid⟩

theorem solveProblem_sound (problem : Problem m) (scheme : Scheme m problem.pool.size)
    (member : scheme ∈ solveProblem problem)
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) :
    (compileProblem problem).Models (scheme.instantiateRows rowParameters)
      (scheme.instantiateValues rowParameters parameters) := by
  obtain ⟨originalRows, declaredOriginal, state, returned, auxRows, declaredAux, rfl⟩ :=
    (mem_solveProblem problem scheme).mp member
  exact ofState_sound problem originalRows declaredOriginal state returned auxRows declaredAux
    rowParameters parameters

/-- All parameters of every returned scheme satisfy the original independent
compiled constraints. This soundness statement needs no generated grammar,
support checker, successful model, residual predicate or caller fuel. -/
theorem all_parameter_sound (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (scheme : Scheme m (compile atoms).size) (member : scheme ∈ solveAll (compile atoms))
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) :
    (compile atoms).Models (scheme.instantiateRows rowParameters)
      (scheme.instantiateValues rowParameters parameters) :=
  solveProblem_sound (splitAtoms atoms) scheme ((solveAll_compile atoms) ▸ member) rowParameters parameters

end Yulang.CommonPatternSolvedConstraints
