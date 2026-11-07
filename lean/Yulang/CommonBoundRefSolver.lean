import Yulang.CommonBoundRefClosedSoundness
import Yulang.CommonBoundRefRowDeclarations

/-!
# Finite unrestricted-parameter schemes for common compiled constraints

The solver runs the finite bound-reference worklist and declares its retained
row constraints. Each returned scheme stores a finite clamped family and a
readout of the original shared nodes. Parameters are arbitrary row, type and
recursive-node assignments. No semantic law or residual check is stored in
the scheme, passed to the computation or imposed on its parameters.

Compiled source metadata is used only to recover the finite original pool.
The meaning being solved remains the independent constructor equations,
type edges and row constraints of the original compiled graph.
-/

namespace Yulang.CommonBoundRefSolver

open Common (Ty Row Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Problem Compiled compileProblem compile splitAtoms Realizes EdgesHold)
open CommonOptionalPoolQueries (queries)
open CommonOptionalPool (embed restrictValues extendValues)
open CommonBoundRefWorklist (State originalEdges run)
open CommonBoundRefClosedSoundness (Extended encodedEdges)
open CommonRowTailInference (RowConstraint RowsHold)
open CommonRowDeclarations (declareRows declareChecks)

variable {m originalSlots : Nat}

structure Scheme (inputs originalSlots : Nat) where
  family : CommonClampedRowFamily.Scheme inputs
  readout : Fin originalSlots → Fin family.pool.size

abbrev Scheme.Parameters (scheme : Scheme m originalSlots) := scheme.family.Parameters

def Scheme.instantiateRows (scheme : Scheme m originalSlots)
    (rowParameters : Fin m → Row) : Fin m → Row :=
  scheme.family.instantiateRows rowParameters

def Scheme.instantiateValues (scheme : Scheme m originalSlots)
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) : Fin originalSlots → Ty :=
  scheme.family.instantiateValues rowParameters parameters ∘ scheme.readout

def ofState (pool : Pool m) (originalRows : List (RowConstraint m)) (state : State pool)
    (auxRows : List (RowConstraint m)) : Scheme m pool.size where
  family := CommonClampedRowFamily.build (Extended pool) (encodedEdges pool state) (originalRows ++ auxRows)
  readout := embed pool (queries pool)

def solveState (pool : Pool m) (originalRows : List (RowConstraint m)) (state : State pool) :
    List (Scheme m pool.size) :=
  match declareChecks state.aux with
  | none => []
  | some auxRows => [ofState pool originalRows state auxRows]

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
    CommonBoundRefWorklist.run_retains pool (originalEdges pool edges) state returned
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
  have auxValid : CommonBoundRefClosedSoundness.AuxHolds problem.pool state rows allValues :=
    (CommonRowDeclarations.declare_checks_exact state.aux auxRows declaredAux rows values
      (CommonSymbolicBoundInspection.BoundRef.eval values)).mp bothRows.2
  have allRealizes : Realizes (Extended problem.pool) rows allValues :=
    CommonClampedRowFamily.Scheme.instantiate_realizes scheme.family rowParameters parameters
  have allEdges : EdgesHold (encodedEdges problem.pool state) allValues :=
    CommonBoundRefClosedSoundness.returned_solve_soundness problem.pool
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

/-- All independent graph models are invariant under demand equivalence
at every node, including negatively used arrow children. -/
theorem models_congr (compiled : Compiled m) (rows : Fin m → Row)
    (first last : Fin compiled.size → Ty)
    (same : ∀ index, Equivalent (first index) (last index)) :
    compiled.Models rows first ↔ compiled.Models rows last :=
  and_congr (CommonOptionalGraphExtension.realizes_congr compiled.definitions rows first last same)
    (and_congr (CommonPresenceConstraintGraph.edgesHold_congr compiled.edges first last same) Iff.rfl)

/-- A model of a selected branch is recovered by choosing its exact row
assignment and the conservative extension of all its node values. -/
theorem ofState_retract (problem : Problem m) (originalRows : List (RowConstraint m))
    (declaredOriginal : declareRows problem.rows = some originalRows)
    (state : State problem.pool) (auxRows : List (RowConstraint m))
    (declaredAux : declareChecks state.aux = some auxRows)
    (rows : Fin m → Row) (values : Fin problem.pool.size → Ty)
    (models : (compileProblem problem).Models rows values)
    (selected : state.Models (CommonBoundRefWorklist.edgeHolds problem.pool values)
      (CommonBoundRefWorklist.auxHolds problem.pool rows values)) :
    ∃ parameters : (ofState problem.pool originalRows state auxRows).Parameters,
      (ofState problem.pool originalRows state auxRows).instantiateRows rows = rows ∧
        ∀ index, Equivalent
          ((ofState problem.pool originalRows state auxRows).instantiateValues rows parameters index)
          (values index) := by
  let lifted := extendValues problem.pool (queries problem.pool) rows values
  have originalRowsModel : RowsHold originalRows rows :=
    (CommonRowDeclarations.declare_rows_exact problem.rows originalRows declaredOriginal rows).mpr models.2.2
  have auxRowsModel : RowsHold auxRows rows :=
    (CommonRowDeclarations.declare_checks_exact state.aux auxRows declaredAux rows values
      (CommonSymbolicBoundInspection.BoundRef.eval values)).mpr selected.2
  have liftedRealizes : Realizes (Extended problem.pool) rows lifted :=
    CommonOptionalPool.extend_realizes problem.pool (queries problem.pool) rows values models.1
  have liftedEdges : EdgesHold (encodedEdges problem.pool state) lifted := by
    intro edge member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact (CommonBoundRefWorklist.extended_edge_exact problem.pool rows values models.1 original).mpr
      (selected.1 original included)
  have same := CommonClampedRowFamily.build_retract (Extended problem.pool) (encodedEdges problem.pool state)
    (originalRows ++ auxRows) rows lifted
    ((CommonRowDeclarations.rows_hold_append originalRows auxRows rows).mpr ⟨originalRowsModel, auxRowsModel⟩)
    liftedRealizes liftedEdges
  refine ⟨(CommonPresenceConstraintGraph.restrict (Extended problem.pool) lifted, lifted), same.1, ?_⟩
  intro index
  change Equivalent
    ((CommonClampedRowFamily.build (Extended problem.pool) (encodedEdges problem.pool state)
      (originalRows ++ auxRows)).instantiateValues rows
      (CommonPresenceConstraintGraph.restrict (Extended problem.pool) lifted, lifted)
      (embed problem.pool (queries problem.pool) index)) (values index)
  simpa only [lifted, CommonOptionalPool.extendValues_original] using
    same.2 (embed problem.pool (queries problem.pool) index)

/-- Completeness for the finite generated syntax invariants. These three
syntactic premises are supplied internally by the source/Core theorems below;
no premise is imposed on the recovered parameters. -/
theorem compiled_models_complete (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (rowGrammar : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (childGrammar : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty)
    (models : (compile atoms).Models rows values) :
    ∃ scheme ∈ solveAll (compile atoms), ∃ rowParameters : Fin m → Row,
      ∃ parameters : scheme.Parameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨originalRows, declaredOriginal⟩ := CommonRowDeclarations.declare_split_rows_some atoms rowGrammar
  obtain ⟨state, returned, selected⟩ :=
    (CommonBoundRefWorklist.compiled_run_models_exact atoms childGrammar widths rows values models.1).mp models.2.1
  obtain ⟨auxRows, declaredAux⟩ := CommonBoundRefRowDeclarations.run_declare_checks_some
    (splitAtoms atoms).pool (CommonGeneratedPoolRows.compiled_pool_rows atoms rowGrammar) _ state returned
  let scheme := ofState (splitAtoms atoms).pool originalRows state auxRows
  have member : scheme ∈ solveAll (compile atoms) := by
    rw [solveAll_compile]
    exact (mem_solveProblem (splitAtoms atoms) scheme).mpr
      ⟨originalRows, declaredOriginal, state, returned, auxRows, declaredAux, rfl⟩
  obtain ⟨parameters, sameRows, sameValues⟩ := ofState_retract (splitAtoms atoms) originalRows
    declaredOriginal state auxRows declaredAux rows values models selected
  exact ⟨scheme, member, rows, parameters, sameRows, sameValues⟩

theorem compiled_models_exact (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (rowGrammar : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (childGrammar : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty) :
    (compile atoms).Models rows values ↔
      ∃ scheme ∈ solveAll (compile atoms), ∃ rowParameters : Fin m → Row,
        ∃ parameters : scheme.Parameters,
          scheme.instantiateRows rowParameters = rows ∧
            ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  constructor
  · exact compiled_models_complete atoms rowGrammar childGrammar widths rows values
  · rintro ⟨scheme, member, rowParameters, parameters, sameRows, sameValues⟩
    have model := all_parameter_sound atoms scheme member rowParameters parameters
    rw [sameRows] at model
    exact (models_congr (compile atoms) rows _ values sameValues).mp model

/-- Every independent model of every actual source-generated clause is
exactly an unrestricted-parameter instance of a returned finite scheme,
with literal row equality and demand-equivalent values at all original nodes.
All syntax invariants are derived from generation, normalization and packing. -/
theorem generated_models_exact (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row) (values : Fin (compile clause.pack).size → Ty) :
    (compile clause.pack).Models rows values ↔
      ∃ scheme ∈ solveAll (compile clause.pack), ∃ rowParameters : Fin (clause.locals + 1) → Row,
        ∃ parameters : scheme.Parameters,
          scheme.instantiateRows rowParameters = rows ∧
            ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  compiled_models_exact clause.pack
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause member)
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member)
    (PresenceGeneratedWidth.generated_width_atoms expression clause member) rows values

theorem generated_core_models_exact (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise
      (Core.PresenceGeneration.CoreRules.principalCore
        ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row) (values : Fin (compile clause.pack).size → Ty) :
    (compile clause.pack).Models rows values ↔
      ∃ scheme ∈ solveAll (compile clause.pack), ∃ rowParameters : Fin (clause.locals + 1) → Row,
        ∃ parameters : scheme.Parameters,
          scheme.instantiateRows rowParameters = rows ∧
            ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  compiled_models_exact clause.pack
    (CommonPresenceSourceFamily.generated_core_row_shapes expression clause member)
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause member) rows values

end Yulang.CommonBoundRefSolver
