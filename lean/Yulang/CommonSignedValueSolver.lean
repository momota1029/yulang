import Yulang.CommonSignedOrdinaryRows
import Yulang.CommonBoundRefSolvedExact

/-!
# Simultaneous common values and independent signed row graph constraints

Every actual branch of the common subtype worklist contributes its ordinary
row requirements to the signed graph solver. Its solved rows then enter the
existing value family unchanged. Parameters are unrestricted. All original
rows and every original value node are recovered.

The input here is a presence clause plus a signed graph. A universal-type
formula or recursive effect source has not been compiled to that input here.
-/
namespace Yulang.CommonSignedValueSolver
open Common (Row Ty Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open PresenceNormalForm (Atom Clause)
open CommonPresenceConstraintGraph (splitAtoms compile)
open CommonSignedOrdinaryRows (augment augment_models)

variable {m : Nat}

structure Scheme (pool : Pool m) where
  values : CommonBoundRefSolved.Scheme pool
  rows : CommonSignedGraphSolver.Scheme m

abbrev Scheme.Parameters {pool : Pool m} (scheme : Scheme pool) := scheme.values.Parameters

def Scheme.instantiateRows {pool : Pool m} (scheme : Scheme pool) (parameters : Fin m → Row) : Fin m → Row :=
  CommonSignedGraphSolver.instantiate scheme.rows parameters

def Scheme.instantiateValues {pool : Pool m} (scheme : Scheme pool) (rowParameters : Fin m → Row)
    (parameters : scheme.Parameters) : Fin pool.size → Ty :=
  scheme.values.instantiateValues (scheme.instantiateRows rowParameters) parameters

def solve (atoms : List (Atom (Fin m))) (effect : CommonSignedGraphSolver.Scheme m) :
    List (Scheme (splitAtoms atoms).pool) :=
  (CommonBoundRefSolved.solveAll atoms).flatMap (fun values =>
    (CommonSignedGraphSolver.solve (augment effect values.rows)).map (fun rows => ⟨values, rows⟩))

def Models (atoms : List (Atom (Fin m))) (effect : CommonSignedGraphSolver.Scheme m)
    (rows : Fin m → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) : Prop :=
  (compile atoms).Models rows values ∧ CommonSignedGraphSolver.Models effect rows

theorem value_row_model {pool : Pool m} (scheme : CommonBoundRefSolved.Scheme pool)
    (parameters : Fin m → Row) : CommonRowTailInference.RowsHold scheme.rows (scheme.instantiateRows parameters) :=
  CommonClampedRowFamily.build_rows_hold _ scheme.edges scheme.rows parameters

theorem value_row_retraction {pool : Pool m} (scheme : CommonBoundRefSolved.Scheme pool)
    (rows : Fin m → Row) (model : CommonRowTailInference.RowsHold scheme.rows rows) :
    scheme.instantiateRows rows = rows := CommonRowTailInference.rowScheme_retract scheme.rows rows model

theorem values_depend_on_rows {pool : Pool m} (scheme : CommonBoundRefSolved.Scheme pool)
    (first last : Fin m → Row) (same : scheme.instantiateRows first = scheme.instantiateRows last)
    (parameters : scheme.Parameters) : scheme.instantiateValues first parameters = scheme.instantiateValues last parameters := by
  change CommonOptionalPool.restrictValues pool (CommonOptionalPoolQueries.queries pool)
      (CommonPresenceClampedBounds.solve _ _ (scheme.instantiateRows first) parameters.1 parameters.2) = _
  rw [same]
  rfl

/-- Soundness needs only actual returned-scheme membership, with no syntax
support conditions and no predicates on any row or value parameter. -/
theorem all_parameters_models (atoms : List (Atom (Fin m))) (effect : CommonSignedGraphSolver.Scheme m)
    (scheme : Scheme (splitAtoms atoms).pool) (returned : scheme ∈ solve atoms effect)
    (rowParameters : Fin m → Row) (parameters : scheme.Parameters) :
    Models atoms effect (scheme.instantiateRows rowParameters) (scheme.instantiateValues rowParameters parameters) := by
  obtain ⟨valueScheme, valueReturned, rowMember⟩ := List.mem_flatMap.mp returned
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp rowMember
  have rowModel := (augment_models effect valueScheme.rows _).mp
    (CommonSignedGraphSolver.all_parameters_models _ rowScheme rowReturned rowParameters)
  have selfRows := value_row_retraction valueScheme _ rowModel.2
  have valueModel := CommonBoundRefSolved.all_parameters_models atoms valueScheme valueReturned
    (CommonSignedGraphSolver.instantiate rowScheme rowParameters) parameters
  rw [selfRows] at valueModel
  exact ⟨valueModel, rowModel.1⟩

/-- The syntax premises are those of the original value solver. Generated
clauses below discharge all of them; none restricts a recovered parameter. -/
theorem model_is_instance (atoms : List (Atom (Fin m))) (effect : CommonSignedGraphSolver.Scheme m)
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rowShapes : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (splitAtoms atoms).pool.size → Ty)
    (model : Models atoms effect rows values) :
    ∃ scheme ∈ solve atoms effect, ∃ rowParameters : Fin m → Row, ∃ parameters : scheme.Parameters,
      scheme.instantiateRows rowParameters = rows ∧
        ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨valueScheme, valueReturned, oldRows, parameters, sameRows, sameValues⟩ :=
    CommonBoundRefSolved.model_is_instance atoms good widths rowShapes rows values model.1
  have rowModel := value_row_model valueScheme oldRows
  rw [sameRows] at rowModel
  let joined := augment effect valueScheme.rows
  have joinedModel : CommonSignedGraphSolver.Models joined rows :=
    (augment_models effect valueScheme.rows rows).mpr ⟨model.2, rowModel⟩
  have recovered := CommonSignedGraphSolver.model_retraction joined rows joinedModel
  let scheme : Scheme (splitAtoms atoms).pool := ⟨valueScheme, joined⟩
  have returned : scheme ∈ solve atoms effect := List.mem_flatMap.mpr
    ⟨valueScheme, valueReturned, List.mem_map.mpr ⟨joined, recovered.1, rfl⟩⟩
  refine ⟨scheme, returned, rows, parameters, recovered.2, ?_⟩
  intro index
  change Equivalent (valueScheme.instantiateValues (CommonSignedGraphSolver.instantiate joined rows) parameters index)
    (values index)
  rw [recovered.2]
  have selfRows := value_row_retraction valueScheme rows rowModel
  rw [values_depend_on_rows valueScheme rows oldRows (selfRows.trans sameRows.symm) parameters]
  exact sameValues index

theorem solve_all_instances_exact (atoms : List (Atom (Fin m))) (effect : CommonSignedGraphSolver.Scheme m)
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rowShapes : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) :
    Models atoms effect rows values ↔
      ∃ scheme ∈ solve atoms effect, ∃ rowParameters : Fin m → Row, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  constructor
  · exact model_is_instance atoms effect good widths rowShapes rows values
  · rintro ⟨scheme, returned, rowParameters, parameters, sameRows, sameValues⟩
    have model := all_parameters_models atoms effect scheme returned rowParameters parameters
    rw [sameRows] at model
    exact ⟨(CommonBoundRefSolved.compiled_models_congr atoms rows _ values sameValues).mp model.1, model.2⟩

/-- Any actual presence-generated clause, any extra finite signed/residual
row graph with heads and purity, independent rows and every value node. -/
theorem generated_all_instances_exact (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (effect : CommonSignedGraphSolver.Scheme (clause.locals + 1))
    (rows : Fin (clause.locals + 1) → Row) (values : Fin (splitAtoms clause.pack).pool.size → Ty) :
    Models clause.pack effect rows values ↔
      ∃ scheme ∈ solve clause.pack effect, ∃ rowParameters : Fin (clause.locals + 1) → Row,
        ∃ parameters : scheme.Parameters,
          scheme.instantiateRows rowParameters = rows ∧
            ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  solve_all_instances_exact clause.pack effect
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) rows values
end Yulang.CommonSignedValueSolver
