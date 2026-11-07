import Yulang.CommonSignedConstraintCompilation
import Yulang.CommonSignedValueSolver

/-!
# Solved common values with actual signed row expressions

The input is a finite presence value clause plus finite signed-expression row
constraints (variable/empty upper bounds). Each actual value-solver branch's
ordinary row conditions are included in the same row problem. The row solver
constructs its own shared graph; callers supply no graph, support or model.

All original rows and every original value node are recovered, with unrestricted
parameters. General quantified effect-source compilation remains separate.
-/
namespace Yulang.CommonSignedValueExpressionSolver
open Common (Row Ty Equivalent)
open PresenceOpenTailGenerationLowering (Pool)
open PresenceNormalForm (Atom Clause)
open CommonPresenceConstraintGraph (splitAtoms compile)
open CommonSignedConstraintCompilation (Problem)

variable {scopes inputs : Nat}

def fromOrdinary : Inference.RowTerm (Fin inputs) → CommonEffectRequestGeneration.RowExpr scopes (Fin inputs)
  | .var index => .var index
  | .empty => .empty
  | .join first last => .union (fromOrdinary first) (fromOrdinary last)

theorem fromOrdinary_eval (rows : Fin inputs → Row) (term : Inference.RowTerm (Fin inputs)) :
    CommonSignedExpressionPool.evaluate rows (fromOrdinary (scopes := scopes) term) =
      RowFlowSchemes.eval Common.rowAlgebra rows term := by
  induction term <;> simp_all [CommonSignedExpressionPool.evaluate, fromOrdinary,
    CommonEffectRequestGeneration.RowExpr.eval, RowFlowSchemes.eval, Common.rowAlgebra]

def ofOrdinaryConstraint (constraint : CommonRowTailInference.RowConstraint inputs) :
    CommonSignedConstraintCompilation.Constraint scopes inputs :=
  ⟨fromOrdinary constraint.lower, match constraint.upper with | .var index => .var index | .empty => .empty⟩

def ofOrdinary (constraints : List (CommonRowTailInference.RowConstraint inputs)) : Problem scopes inputs :=
  constraints.map ofOrdinaryConstraint

theorem ofOrdinary_models (constraints : List (CommonRowTailInference.RowConstraint inputs)) (rows : Fin inputs → Row) :
    CommonSignedConstraintCompilation.Models (ofOrdinary (scopes := scopes) constraints) rows ↔
      CommonRowTailInference.RowsHold constraints rows := by
  simp only [CommonSignedConstraintCompilation.Models, ofOrdinary, List.forall_mem_map,
    CommonRowTailInference.RowsHold]
  apply forall_congr'
  intro constraint
  apply forall_congr'
  intro _
  cases constraint with
  | mk lower upper =>
    cases upper <;> simp only [ofOrdinaryConstraint, fromOrdinary_eval,
      CommonSignedConstraintCompilation.Upper.eval, CommonRowTailInference.Upper.term,
      RowFlowSchemes.eval, Common.rowAlgebra]

theorem models_append (first last : Problem scopes inputs) (rows : Fin inputs → Row) :
    CommonSignedConstraintCompilation.Models (first ++ last) rows ↔
      CommonSignedConstraintCompilation.Models first rows ∧ CommonSignedConstraintCompilation.Models last rows := by
  simp [CommonSignedConstraintCompilation.Models, List.mem_append, or_imp, forall_and]

structure Scheme (pool : Pool inputs) where
  values : CommonBoundRefSolved.Scheme pool
  rows : CommonSignedConstraintCompilation.Scheme inputs

abbrev Scheme.RowParameters {pool : Pool inputs} (scheme : Scheme pool) := Fin scheme.rows.slots → Row
abbrev Scheme.ValueParameters {pool : Pool inputs} (scheme : Scheme pool) := scheme.values.Parameters

def Scheme.instantiateRows {pool : Pool inputs} (scheme : Scheme pool) (parameters : scheme.RowParameters) : Fin inputs → Row :=
  scheme.rows.instantiate parameters

def Scheme.instantiateValues {pool : Pool inputs} (scheme : Scheme pool) (rowParameters : scheme.RowParameters)
    (parameters : scheme.ValueParameters) : Fin pool.size → Ty :=
  scheme.values.instantiateValues (scheme.instantiateRows rowParameters) parameters

def solve (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs) : List (Scheme (splitAtoms atoms).pool) :=
  (CommonBoundRefSolved.solveAll atoms).flatMap (fun values =>
    (CommonSignedConstraintCompilation.solve (effects ++ ofOrdinary values.rows)).map (fun rows => ⟨values, rows⟩))

def Models (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (rows : Fin inputs → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) : Prop :=
  (compile atoms).Models rows values ∧ CommonSignedConstraintCompilation.Models effects rows

theorem all_parameters_models (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (scheme : Scheme (splitAtoms atoms).pool) (returned : scheme ∈ solve atoms effects)
    (rowParameters : scheme.RowParameters) (parameters : scheme.ValueParameters) :
    Models atoms effects (scheme.instantiateRows rowParameters) (scheme.instantiateValues rowParameters parameters) := by
  obtain ⟨valueScheme, valueReturned, rowMember⟩ := List.mem_flatMap.mp returned
  obtain ⟨rowScheme, rowReturned, rfl⟩ := List.mem_map.mp rowMember
  have both := (models_append effects (ofOrdinary valueScheme.rows) _).mp
    (CommonSignedConstraintCompilation.all_parameters_models _ rowScheme rowReturned rowParameters)
  have ordinary := (ofOrdinary_models valueScheme.rows _).mp both.2
  have rowSame := CommonSignedValueSolver.value_row_retraction valueScheme _ ordinary
  have valueModel := CommonBoundRefSolved.all_parameters_models atoms valueScheme valueReturned
    (rowScheme.instantiate rowParameters) parameters
  rw [rowSame] at valueModel
  exact ⟨valueModel, both.1⟩

theorem model_is_instance (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rowShapes : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin inputs → Row) (values : Fin (splitAtoms atoms).pool.size → Ty)
    (model : Models atoms effects rows values) :
    ∃ scheme ∈ solve atoms effects, ∃ rowParameters : scheme.RowParameters, ∃ parameters : scheme.ValueParameters,
      scheme.instantiateRows rowParameters = rows ∧
        ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨valueScheme, valueReturned, oldRows, parameters, sameRows, sameValues⟩ :=
    CommonBoundRefSolved.model_is_instance atoms good widths rowShapes rows values model.1
  have ordinary := CommonSignedValueSolver.value_row_model valueScheme oldRows
  rw [sameRows] at ordinary
  have joined : CommonSignedConstraintCompilation.Models (effects ++ ofOrdinary valueScheme.rows) rows :=
    (models_append effects (ofOrdinary valueScheme.rows) rows).mpr
      ⟨model.2, (ofOrdinary_models valueScheme.rows rows).mpr ordinary⟩
  obtain ⟨rowScheme, rowReturned, rowParameters, rowSame⟩ :=
    (CommonSignedConstraintCompilation.solve_all_instances_exact _ rows).mp joined
  let scheme : Scheme (splitAtoms atoms).pool := ⟨valueScheme, rowScheme⟩
  have returned : scheme ∈ solve atoms effects := List.mem_flatMap.mpr
    ⟨valueScheme, valueReturned, List.mem_map.mpr ⟨rowScheme, rowReturned, rfl⟩⟩
  refine ⟨scheme, returned, rowParameters, parameters, rowSame, ?_⟩
  intro index
  change Equivalent (valueScheme.instantiateValues (rowScheme.instantiate rowParameters) parameters index) (values index)
  rw [rowSame]
  have selfRows := CommonSignedValueSolver.value_row_retraction valueScheme rows ordinary
  rw [CommonSignedValueSolver.values_depend_on_rows valueScheme rows oldRows (selfRows.trans sameRows.symm) parameters]
  exact sameValues index

theorem solve_all_instances_exact (atoms : List (Atom (Fin inputs))) (effects : Problem scopes inputs)
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rowShapes : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin inputs → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) :
    Models atoms effects rows values ↔
      ∃ scheme ∈ solve atoms effects, ∃ rowParameters : scheme.RowParameters, ∃ parameters : scheme.ValueParameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  constructor
  · exact model_is_instance atoms effects good widths rowShapes rows values
  · rintro ⟨scheme, returned, rowParameters, parameters, sameRows, sameValues⟩
    have model := all_parameters_models atoms effects scheme returned rowParameters parameters
    rw [sameRows] at model
    exact ⟨(CommonBoundRefSolved.compiled_models_congr atoms rows _ values sameValues).mp model.1, model.2⟩

/-- All actual presence-generated clauses, arbitrary additional signed row
expressions, independent rows and every compiled node. No caller graph. -/
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
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) rows values
end Yulang.CommonSignedValueExpressionSolver
