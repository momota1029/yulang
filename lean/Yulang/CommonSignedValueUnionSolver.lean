import Yulang.CommonSignedUnionCompilation
import Yulang.CommonBoundRefSolvedExact

/-! Simultaneous all-node value and signed-row solving without the old
simple-row grammar premise. The worklist's actual raw upper unions go to the
choice-row solver; they are never rejected by declareUpper. Type-child and
record-width syntax premises remain, independently of all parameters. -/
namespace Yulang.CommonSignedValueUnionSolver
open Common (Row Ty Equivalent)
open Core.PresenceGeneration (RowTerm)
open PresenceOpenTailGenerationLowering (Pool)
open PresenceNormalForm (Atom Clause)
open CommonPresenceConstraintGraph (splitAtoms compile Realizes EdgesHold rowEval)
open CommonBoundRefClosedSoundness (Extended encodedEdges)
open CommonBoundRefSolvedRows (auxiliaryRows)
open CommonOptionalPoolQueries (queries)
open CommonSignedUnionCompilation (Problem)

variable {scopes inputs : Nat}

def fromPairs (pairs : List (RowTerm (Fin inputs) × RowTerm (Fin inputs))) : Problem scopes inputs :=
  pairs.map (fun pair => ⟨.fromPresence pair.1, pair.2⟩)

theorem fromPairs_models (pairs : List (RowTerm (Fin inputs) × RowTerm (Fin inputs))) (rows : Fin inputs → Row) :
    CommonSignedUnionCompilation.Models (fromPairs (scopes := scopes) pairs) rows ↔
      CommonPresenceConstraintGraph.RowsHold pairs rows := by
  simp only [fromPairs, CommonSignedUnionCompilation.Models, List.forall_mem_map, CommonPresenceConstraintGraph.RowsHold]
  apply forall_congr'; intro pair
  apply forall_congr'; intro _
  simp only [CommonSignedExpressionPool.evaluate, CommonEffectRequestGeneration.RowExpr.eval_fromPresence,
    CommonSignedUnionCompilation.upperEval, ← CommonPresenceConstraintGraph.rowEval_exact rows (fun _ => .base .unit)]

theorem models_append (first last : Problem scopes inputs) (rows : Fin inputs → Row) :
    CommonSignedUnionCompilation.Models (first ++ last) rows ↔
      CommonSignedUnionCompilation.Models first rows ∧ CommonSignedUnionCompilation.Models last rows := by
  simp [CommonSignedUnionCompilation.Models, List.mem_append, or_imp, forall_and]

structure Scheme (pool : Pool inputs) where
  edges : List (Fin (Extended pool).size × Fin (Extended pool).size)
  rows : CommonSignedUnionCompilation.Scheme inputs

abbrev Scheme.RowParameters {pool : Pool inputs} (scheme : Scheme pool) := Fin scheme.rows.slots → Row
abbrev Scheme.ValueParameters {pool : Pool inputs} (_scheme : Scheme pool) :=
  (Fin inputs → Ty) × (Fin (Extended pool).size → Ty)

def Scheme.instantiateRows {pool : Pool inputs} (scheme : Scheme pool) (parameters : scheme.RowParameters) : Fin inputs → Row :=
  scheme.rows.instantiate parameters

def Scheme.instantiateValues {pool : Pool inputs} (scheme : Scheme pool) (rowParameters : scheme.RowParameters)
    (parameters : scheme.ValueParameters) : Fin pool.size → Ty :=
  CommonOptionalPool.restrictValues pool (queries pool)
    (CommonPresenceClampedBounds.solve (Extended pool) scheme.edges (scheme.instantiateRows rowParameters) parameters.1 parameters.2)

def solve (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs) : List (Scheme (splitAtoms atoms).pool) :=
  (CommonBoundRefWorklist.run (splitAtoms atoms).pool
    (CommonBoundRefWorklist.originalEdges (splitAtoms atoms).pool (compile atoms).edges)).flatMap (fun state =>
      (CommonSignedUnionCompilation.solve (effects ++ fromPairs ((splitAtoms atoms).rows ++ auxiliaryRows state.aux))).map
        (fun rows => ⟨encodedEdges (splitAtoms atoms).pool state, rows⟩))

def Models (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (rows : Fin inputs → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) : Prop :=
  (compile atoms).Models rows values ∧ CommonSignedUnionCompilation.Models effects rows

theorem all_parameters_models (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (scheme : Scheme (splitAtoms atoms).pool) (returned : scheme ∈ solve atoms effects)
    (rowParameters : scheme.RowParameters) (parameters : scheme.ValueParameters) :
    Models atoms effects (scheme.instantiateRows rowParameters) (scheme.instantiateValues rowParameters parameters) := by
  obtain ⟨state, stateReturned, rowMember⟩ := List.mem_flatMap.mp returned
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp rowMember
  have joined := (models_append effects _ _).mp
    (CommonSignedUnionCompilation.all_parameters_models _ rowScheme rowReturned rowParameters)
  have rowParts := (CommonBoundRefSolvedRows.rowsHold_append (splitAtoms atoms).rows (auxiliaryRows state.aux) _).mp
    ((fromPairs_models _ _).mp joined.2)
  let rows := rowScheme.instantiate rowParameters
  let values := CommonPresenceClampedBounds.solve (Extended (splitAtoms atoms).pool)
    (encodedEdges (splitAtoms atoms).pool state) rows parameters.1 parameters.2
  have auxiliary := (CommonBoundRefSolvedRows.auxiliaryRows_exact state.aux
    (CommonBoundRefWorklist.run_row_or_true _ _ state stateReturned) rows
    (CommonOptionalPool.restrictValues (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) values)).mp rowParts.2
  have edges := CommonBoundRefClosedSoundness.returned_solve_soundness _ _ state stateReturned rows parameters.1 parameters.2 auxiliary
  exact ⟨⟨CommonOptionalPool.restrict_realizes _ _ _ _ (CommonPresenceClampedBounds.solve_realizes _ _ _ _ _),
    CommonBoundRefSolved.initial_edges_hold atoms state stateReturned values edges, rowParts.1⟩, joined.1⟩

theorem model_is_instance (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms) (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin inputs → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) (model : Models atoms effects rows values) :
    ∃ scheme ∈ solve atoms effects, ∃ rowParameters : scheme.RowParameters, ∃ parameters : scheme.ValueParameters,
      scheme.instantiateRows rowParameters = rows ∧
        ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨state, stateReturned, stateModel⟩ :=
    (CommonBoundRefWorklist.compiled_run_models_exact atoms good widths rows values model.1.1).mp model.1.2.1
  have auxiliaryRowsModel := (CommonBoundRefSolvedRows.auxiliaryRows_exact state.aux
    (CommonBoundRefWorklist.run_row_or_true _ _ state stateReturned) rows values).mpr stateModel.2
  have joined : CommonSignedUnionCompilation.Models
      (effects ++ fromPairs ((splitAtoms atoms).rows ++ auxiliaryRows state.aux)) rows :=
    (models_append _ _ rows).mpr ⟨model.2, (fromPairs_models _ rows).mpr
      ((CommonBoundRefSolvedRows.rowsHold_append _ _ rows).mpr ⟨model.1.2.2, auxiliaryRowsModel⟩)⟩
  obtain ⟨rowScheme, rowReturned, rowParameters, rowSame⟩ :=
    (CommonSignedUnionCompilation.solve_all_instances_exact _ rows).mp joined
  let expanded := CommonOptionalPool.extendValues (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) rows values
  have expandedRealizes : Realizes (Extended (splitAtoms atoms).pool) rows expanded :=
    CommonOptionalPool.extend_realizes _ _ rows values model.1.1
  have expandedEdges : EdgesHold (encodedEdges (splitAtoms atoms).pool state) expanded := by
    intro edge member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact (CommonBoundRefWorklist.extended_edge_exact (splitAtoms atoms).pool rows values model.1.1 original).mpr
      (stateModel.1 original included)
  let scheme : Scheme (splitAtoms atoms).pool := ⟨encodedEdges (splitAtoms atoms).pool state, rowScheme⟩
  have returned : scheme ∈ solve atoms effects := List.mem_flatMap.mpr
    ⟨state, stateReturned, List.mem_map.mpr ⟨rowScheme, rowReturned, rfl⟩⟩
  refine ⟨scheme, returned, rowParameters, (CommonPresenceConstraintGraph.restrict _ expanded, expanded), rowSame, ?_⟩
  intro index
  change Equivalent
    (CommonPresenceClampedBounds.solve (Extended (splitAtoms atoms).pool) (encodedEdges (splitAtoms atoms).pool state)
      (rowScheme.instantiate rowParameters) (CommonPresenceConstraintGraph.restrict _ expanded) expanded
      (CommonOptionalPool.embed (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) index)) (values index)
  rw [rowSame]
  have recovered := CommonPresenceClampedBounds.solve_retract _ _ rows expanded expandedRealizes expandedEdges
    (CommonOptionalPool.embed (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) index)
  simpa only [expanded, CommonOptionalPool.extendValues_original] using recovered

theorem solve_all_instances_exact (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms) (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin inputs → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) :
    Models atoms effects rows values ↔
      ∃ scheme ∈ solve atoms effects, ∃ rowParameters : scheme.RowParameters, ∃ parameters : scheme.ValueParameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  constructor
  · exact model_is_instance atoms effects good widths rows values
  · rintro ⟨scheme, returned, rowParameters, parameters, sameRows, sameValues⟩
    have model := all_parameters_models atoms effects scheme returned rowParameters parameters
    rw [sameRows] at model
    exact ⟨(CommonBoundRefSolved.compiled_models_congr atoms rows _ values sameValues).mp model.1, model.2⟩

theorem generated_all_instances_exact (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (effects : Problem scopes (clause.locals + 1)) (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty) :
    Models clause.pack effects rows values ↔
      ∃ scheme ∈ solve clause.pack effects, ∃ rowParameters : scheme.RowParameters, ∃ parameters : scheme.ValueParameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  solve_all_instances_exact clause.pack effects
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated) rows values
end Yulang.CommonSignedValueUnionSolver
