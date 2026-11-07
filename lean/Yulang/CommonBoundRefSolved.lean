import Yulang.CommonBoundRefSolvedRows

/-!
# Finite solved schemes for the actual common subtype worklist

A scheme contains the encoded finite edge list and a declared row problem.
Instantiation solves all rows and all clamped equations simultaneously, with
unrestricted common type and row parameters. Original compiled nodes are read
through the literal initial-segment embedding into the extended shared pool.
-/

namespace Yulang.CommonBoundRefSolved

open PresenceOpenTailGenerationLowering (Pool)
open PresenceNormalForm (Atom)
open Common (Row Ty Equivalent)
open CommonOptionalPoolQueries (queries)
open CommonBoundRefClosedSoundness (Extended encodedEdges)
open CommonPresenceConstraintGraph (splitAtoms compile Realizes EdgesHold)
open CommonBoundRefSolvedRows (declareRows auxiliaryRows)

variable {m : Nat}

/-- Finite syntax only: there are no model, residual, or closure fields. -/
structure Scheme (pool : Pool m) where
  edges : List (Fin (Extended pool).size × Fin (Extended pool).size)
  rows : List (CommonRowTailInference.RowConstraint m)

def Scheme.family {pool : Pool m} (scheme : Scheme pool) : CommonClampedRowFamily.Scheme m :=
  CommonClampedRowFamily.build (Extended pool) scheme.edges scheme.rows

abbrev Scheme.Parameters {pool : Pool m} (scheme : Scheme pool) := scheme.family.Parameters

def Scheme.instantiateRows {pool : Pool m} (scheme : Scheme pool)
    (rowParameters : Fin m → Row) : Fin m → Row := scheme.family.instantiateRows rowParameters

def Scheme.instantiateValues {pool : Pool m} (scheme : Scheme pool)
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) : Fin pool.size → Ty :=
  CommonOptionalPool.restrictValues pool (queries pool)
    (scheme.family.instantiateValues rowParameters parameters)

@[simp] theorem Scheme.instantiate_input {pool : Pool m} (scheme : Scheme pool)
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) (index : Fin m) :
    scheme.instantiateValues rowParameters parameters (pool.input index) =
      scheme.family.instantiateValues rowParameters parameters (scheme.family.pool.input index) := by
  change _ = scheme.family.instantiateValues rowParameters parameters ((Extended pool).input index)
  rw [CommonOptionalPool.input_embed]
  rfl

/-- The only failure here is a finite unsupported row-syntax test. -/
def solveState (atoms : List (Atom (Fin m)))
    (state : CommonBoundRefWorklist.State (splitAtoms atoms).pool) :
    Option (Scheme (splitAtoms atoms).pool) :=
  (declareRows ((splitAtoms atoms).rows ++ auxiliaryRows state.aux)).map
    (fun rows => ⟨encodedEdges (splitAtoms atoms).pool state, rows⟩)

/-- No semantic assignment, successful solver, cache, or caller fuel occurs
in this computation. -/
def solveAll (atoms : List (Atom (Fin m))) : List (Scheme (splitAtoms atoms).pool) :=
  (CommonBoundRefWorklist.run (splitAtoms atoms).pool
    (CommonBoundRefWorklist.originalEdges (splitAtoms atoms).pool (compile atoms).edges)).filterMap
      (solveState atoms)

theorem mem_solveAll (atoms : List (Atom (Fin m))) (scheme : Scheme (splitAtoms atoms).pool) :
    scheme ∈ solveAll atoms ↔
      ∃ state ∈ CommonBoundRefWorklist.run (splitAtoms atoms).pool
          (CommonBoundRefWorklist.originalEdges (splitAtoms atoms).pool (compile atoms).edges),
        ∃ constraints, declareRows ((splitAtoms atoms).rows ++ auxiliaryRows state.aux) = some constraints ∧
          scheme = ⟨encodedEdges (splitAtoms atoms).pool state, constraints⟩ := by
  simp only [solveAll, List.mem_filterMap, solveState, Option.map_eq_some_iff]
  constructor
  · rintro ⟨state, returned, constraints, declared, rfl⟩
    exact ⟨state, returned, constraints, declared, rfl⟩
  · rintro ⟨state, returned, constraints, declared, rfl⟩
    exact ⟨state, returned, constraints, declared, rfl⟩

theorem initial_edges_hold (atoms : List (Atom (Fin m)))
    (state : CommonBoundRefWorklist.State (splitAtoms atoms).pool)
    (returned : state ∈ CommonBoundRefWorklist.run (splitAtoms atoms).pool
      (CommonBoundRefWorklist.originalEdges (splitAtoms atoms).pool (compile atoms).edges))
    (values : Fin (Extended (splitAtoms atoms).pool).size → Ty)
    (valid : EdgesHold (encodedEdges (splitAtoms atoms).pool state) values) :
    EdgesHold (compile atoms).edges
      (CommonOptionalPool.restrictValues (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) values) := by
  intro edge member
  let pair := (CommonBoundRefCoalescing.original (splitAtoms atoms).pool
    (queries (splitAtoms atoms).pool) edge.1,
    CommonBoundRefCoalescing.original (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) edge.2)
  have original : pair ∈ CommonBoundRefWorklist.originalEdges (splitAtoms atoms).pool (compile atoms).edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have retained := CommonBoundRefWorklist.run_retains _ _ state returned original
  have encoded := valid _ (List.mem_map.mpr ⟨pair, retained, rfl⟩)
  exact encoded

/-- Every returned scheme models the original compiled graph at every row
and type parameter assignment. There are no semantic conditions on either
parameter family and no source-grammar premise in this soundness direction. -/
theorem all_parameters_models (atoms : List (Atom (Fin m)))
    (scheme : Scheme (splitAtoms atoms).pool) (returned : scheme ∈ solveAll atoms)
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) :
    (compile atoms).Models (scheme.instantiateRows rowParameters)
      (scheme.instantiateValues rowParameters parameters) := by
  obtain ⟨state, included, constraints, declared, rfl⟩ := (mem_solveAll atoms scheme).mp returned
  let family := CommonClampedRowFamily.build (Extended (splitAtoms atoms).pool)
    (encodedEdges (splitAtoms atoms).pool state) constraints
  have rowModel := CommonClampedRowFamily.build_rows_hold (Extended (splitAtoms atoms).pool)
    (encodedEdges (splitAtoms atoms).pool state) constraints rowParameters
  have rowParts := (CommonBoundRefSolvedRows.rowsHold_append (splitAtoms atoms).rows
    (auxiliaryRows state.aux) (family.instantiateRows rowParameters)).mp
      ((CommonBoundRefSolvedRows.declareRows_exact _ constraints declared _).mp rowModel)
  have auxiliary := (CommonBoundRefSolvedRows.auxiliaryRows_exact state.aux
    (CommonBoundRefWorklist.run_row_or_true _ _ state included)
    (family.instantiateRows rowParameters)
    (CommonOptionalPool.restrictValues (splitAtoms atoms).pool (queries (splitAtoms atoms).pool)
      (family.instantiateValues rowParameters parameters))).mp rowParts.2
  have edges := CommonBoundRefClosedSoundness.returned_solve_soundness _ _ state included
    (family.instantiateRows rowParameters) parameters.1 parameters.2 auxiliary
  exact ⟨CommonOptionalPool.restrict_realizes _ _ _ _
      (CommonClampedRowFamily.Scheme.instantiate_realizes family rowParameters parameters),
    initial_edges_hold atoms state included _ edges, rowParts.1⟩

theorem compiled_models_congr (atoms : List (Atom (Fin m))) (rows : Fin m → Row)
    (first last : Fin (splitAtoms atoms).pool.size → Ty)
    (same : ∀ index, Equivalent (first index) (last index)) :
    (compile atoms).Models rows first ↔ (compile atoms).Models rows last :=
  and_congr (CommonPresenceVariableBounds.realizes_congr (splitAtoms atoms).pool rows first last same)
    (and_congr (CommonPresenceConstraintGraph.edgesHold_congr (compile atoms).edges first last same) Iff.rfl)

/-- The exact per-branch stopping and closure result for the actual compiler
input. This uses the internally constructed finite reference inventory. -/
theorem saturation_closed (atoms : List (Atom (Fin m)))
    (state : CommonBoundRefWorklist.State (splitAtoms atoms).pool)
    (returned : state ∈ CommonBoundRefWorklist.run (splitAtoms atoms).pool
      (CommonBoundRefWorklist.originalEdges (splitAtoms atoms).pool (compile atoms).edges)) :
    FiniteBranchingWorklist.pending (CommonBoundRefWorklist.inventory (splitAtoms atoms).pool)
        (CommonBoundRefWorklist.rigid (splitAtoms atoms).pool) state = none ∧
      FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid (splitAtoms atoms).pool)
        (CommonBoundRefWorklist.inspect (splitAtoms atoms).pool) state ∧
      state.processed.Nodup ∧ state.trace.length = state.processed.length ∧
      state.trace.length ≤ (5 * (splitAtoms atoms).pool.size + 3) ^ 2 :=
  ⟨CommonBoundRefWorklist.run_finished _ _ state returned,
    CommonBoundRefWorklist.run_closed _ _ state returned,
    CommonBoundRefWorklist.run_bound _ _ state returned⟩

end Yulang.CommonBoundRefSolved
