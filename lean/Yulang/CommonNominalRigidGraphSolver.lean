import Yulang.CommonNominalRigidClampedSoundness
import Yulang.CommonNominalTemplateRowSolver

/-!
# Unrestricted all-instance families for cyclic nominal rigid graphs

Actual finite saturation discharges every rigid/nominal comparison. The row
table solver discharges all generated signed-row constraints. Every returned
scheme has unrestricted row/type/recursive parameters; no original edge or
model predicate is tested at instantiation. Every original node and row is
recovered simultaneously.

This is the full solver for the displayed finite rigid-head graph grammar,
not the full source construction theorem: record/default/lattice root
inspection, original source lowering and runtime casts remain separate.
-/

namespace Yulang.CommonNominalRigidGraphSolver

open CommonNominalCarrier
open CommonNominalRigidWorklist (Pool RowEdge Realizes edgeHolds rowHolds)
open CommonNominalRigidClampedSoundness (clampedPool realizes_exact)
open CommonNominalTypeFlow (Edge)

def Models (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows))
    (rowValues : Fin rows → Row) (values : Fin nodes → Ty) : Prop :=
  Realizes pool rowValues values ∧ (∀ edge ∈ edges, edgeHolds values edge) ∧
    ∀ edge ∈ rowEdges, rowHolds rowValues edge

structure Scheme (nodes rows : Nat) where
  pool : Pool nodes rows
  edges : List (Edge nodes)
  rowSolution : CommonNominalTemplateRowSolver.Scheme rows

abbrev Scheme.Parameters (_scheme : Scheme nodes rows) :=
  CommonNominalRowCells.Parameters rows × ((Fin nodes → Ty) × (Fin nodes → Ty))

def Scheme.instantiateRows (scheme : Scheme nodes rows) (parameters : scheme.Parameters) : Fin rows → Row :=
  scheme.rowSolution.instantiate parameters.1

def Scheme.instantiateValues (scheme : Scheme nodes rows) (parameters : scheme.Parameters) : Fin nodes → Ty :=
  CommonNominalClampedGraphFamily.instantiate (clampedPool scheme.pool) scheme.edges
    (scheme.instantiateRows parameters) parameters.2.1 parameters.2.2

def solve (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows)) : List (Scheme nodes rows) :=
  (CommonNominalRigidWorklist.run pool edges rowEdges).flatMap fun state =>
    (CommonNominalTemplateRowSolver.solve state.aux).map fun rowScheme => ⟨pool, state.edges, rowScheme⟩

/-- All rows, both free type vectors and all cyclic node parameters are
arbitrary. The original full subtype edges are conclusions, not guards. -/
theorem all_parameters_models (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows))
    (scheme : Scheme nodes rows) (member : scheme ∈ solve pool edges rowEdges) (parameters : scheme.Parameters) :
    Models pool edges rowEdges (scheme.instantiateRows parameters) (scheme.instantiateValues parameters) := by
  obtain ⟨state, stateReturned, included⟩ := List.mem_flatMap.mp member
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp included
  have rowModel := CommonNominalTemplateRowSolver.all_parameters_models state.aux rowScheme rowReturned parameters.1
  have retained := CommonNominalRigidWorklist.run_retains pool edges rowEdges state stateReturned
  refine ⟨(realizes_exact pool _ _).mp
    (CommonNominalClampedGraphFamily.all_parameters_realizes _ _ _ _ _), ?_, ?_⟩
  · have final := CommonNominalRigidClampedSoundness.returned_clamped_sound pool edges rowEdges state stateReturned
      (rowScheme.instantiate parameters.1) parameters.2.1 _
      (CommonNominalPresenceTailRegular.solveBlock_models _ parameters.2.2) rowModel
    exact fun edge present => final edge (retained.1 present)
  · exact fun edge present => rowModel edge (retained.2 present)

theorem realizes_congr (pool : Pool nodes rows) (rowValues : Fin rows → Row) (first last : Fin nodes → Ty)
    (same : ∀ index, Equivalent (first index) (last index)) :
    Realizes pool rowValues first ↔ Realizes pool rowValues last := by
  rw [← realizes_exact, ← realizes_exact]
  exact CommonNominalPresenceTailRegular.models_congr _ first last same

/-- All original row slots are recovered literally, and every original
flexible/constructed/nominal argument node is recovered up to demand
equivalence, by a single unrestricted parameter tuple. -/
theorem solve_all_instances_exact (pool : Pool nodes rows) (edges : List (Edge nodes))
    (rowEdges : List (RowEdge rows)) (rowValues : Fin rows → Row) (values : Fin nodes → Ty) :
    Models pool edges rowEdges rowValues values ↔
      ∃ scheme ∈ solve pool edges rowEdges, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows parameters = rowValues ∧
        ∀ index, Equivalent (scheme.instantiateValues parameters index) (values index) := by
  constructor
  · rintro ⟨original, originalEdges, originalRows⟩
    obtain ⟨state, stateReturned, finalEdges, finalRows⟩ :=
      (CommonNominalRigidWorklist.run_models_exact pool rowValues values original edges rowEdges).mp
        ⟨originalEdges, originalRows⟩
    obtain ⟨rowScheme, rowReturned, rowParameters, rowsSame⟩ :=
      (CommonNominalTemplateRowSolver.solve_all_instances_exact state.aux rowValues).mp finalRows
    let scheme : Scheme nodes rows := ⟨pool, state.edges, rowScheme⟩
    refine ⟨scheme, List.mem_flatMap.mpr ⟨state, stateReturned,
      List.mem_map.mpr ⟨rowScheme, rowReturned, rfl⟩⟩,
      ⟨rowParameters, values, values⟩, rowsSame, ?_⟩
    intro index
    change Equivalent (CommonNominalClampedGraphFamily.instantiate (clampedPool pool) state.edges
      (rowScheme.instantiate rowParameters) values values index) (values index)
    rw [rowsSame]
    exact CommonNominalClampedGraphFamily.all_models_retraction _ _ _ values
      ((realizes_exact pool rowValues values).mpr original) finalEdges index
  · rintro ⟨scheme, member, parameters, rowsSame, valuesSame⟩
    have sound := all_parameters_models pool edges rowEdges scheme member parameters
    rw [rowsSame] at sound
    refine ⟨(realizes_congr pool rowValues _ values valuesSame).mp sound.1, ?_, sound.2.2⟩
    intro edge present
    exact subtype_trans (valuesSame edge.1).2 (subtype_trans (sound.2.1 edge present) (valuesSame edge.2).1)

theorem rejected_iff (pool : Pool nodes rows) (edges : List (Edge nodes)) (rowEdges : List (RowEdge rows)) :
    solve pool edges rowEdges = [] ↔ ¬ ∃ rowValues values, Models pool edges rowEdges rowValues values := by
  constructor
  · intro rejected ⟨rowValues, values, model⟩
    obtain ⟨scheme, returned, _⟩ := (solve_all_instances_exact pool edges rowEdges rowValues values).mp model
    simp [rejected] at returned
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro scheme member
    let parameters : scheme.Parameters := ⟨fun _ => Common.rowEmpty, (fun _ => .bottom), (fun _ => .bottom)⟩
    exact absent ⟨scheme.instantiateRows parameters, scheme.instantiateValues parameters,
      all_parameters_models pool edges rowEdges scheme member parameters⟩

end Yulang.CommonNominalRigidGraphSolver
