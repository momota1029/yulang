import Yulang.CommonBoundRefSolved

/-!
# Every independent generated common model is a solved instance

The exactness theorem quantifies independently over all input rows and all
compiled node values. Every returned scheme has unrestricted row, original
value, and regular-block parameters. The construction recovers rows literally
and every compiled value up to the common equivalence. Source generation
supplies the finite syntax premises internally.
-/

namespace Yulang.CommonBoundRefSolved

open PresenceOpenTailGenerationLowering (Pool)
open PresenceNormalForm (Atom Clause)
open Common (Row Ty Equivalent)
open CommonOptionalPoolQueries (queries)
open CommonBoundRefClosedSoundness (Extended encodedEdges)
open CommonPresenceConstraintGraph (splitAtoms compile Realizes EdgesHold)
open CommonBoundRefSolvedRows (declareRows auxiliaryRows)

variable {m : Nat}

theorem model_is_instance (atoms : List (Atom (Fin m)))
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rowShapes : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (splitAtoms atoms).pool.size → Ty)
    (model : (compile atoms).Models rows values) :
    ∃ scheme ∈ solveAll atoms, ∃ rowParameters, ∃ parameters : scheme.Parameters,
      scheme.instantiateRows rowParameters = rows ∧
        ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨state, returned, stateModel⟩ :=
    (CommonBoundRefWorklist.compiled_run_models_exact atoms good widths rows values model.1).mp model.2.1
  obtain ⟨constraints, declared⟩ := CommonBoundRefSolvedRows.declareRows_complete
    ((splitAtoms atoms).rows ++ auxiliaryRows state.aux)
    (CommonBoundRefSolvedRows.supported_append _ _
      (CommonBoundRefSolvedRows.original_rows_supported atoms rowShapes)
      (CommonBoundRefSolvedRows.run_rows_supported _
        (CommonGeneratedPoolRows.compiled_pool_rows atoms rowShapes) _ state returned))
  let scheme : Scheme (splitAtoms atoms).pool := ⟨encodedEdges _ state, constraints⟩
  have member : scheme ∈ solveAll atoms :=
    (mem_solveAll atoms scheme).mpr ⟨state, returned, constraints, declared, rfl⟩
  let expanded := CommonOptionalPool.extendValues (splitAtoms atoms).pool
    (queries (splitAtoms atoms).pool) rows values
  have expandedRealizes : Realizes (Extended (splitAtoms atoms).pool) rows expanded :=
    CommonOptionalPool.extend_realizes _ _ rows values model.1
  have expandedEdges : EdgesHold (encodedEdges (splitAtoms atoms).pool state) expanded := by
    intro edge member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact (CommonBoundRefWorklist.extended_edge_exact (splitAtoms atoms).pool rows values
      model.1 original).mpr (stateModel.1 original included)
  have auxiliaryRowsModel := (CommonBoundRefSolvedRows.auxiliaryRows_exact state.aux
    (CommonBoundRefWorklist.run_row_or_true _ _ state returned) rows values).mpr stateModel.2
  have rowModel := (CommonBoundRefSolvedRows.declareRows_exact _ constraints declared rows).mpr
    ((CommonBoundRefSolvedRows.rowsHold_append _ _ rows).mpr ⟨model.2.2, auxiliaryRowsModel⟩)
  have recovered := CommonClampedRowFamily.build_retract (Extended (splitAtoms atoms).pool)
    (encodedEdges (splitAtoms atoms).pool state) constraints rows expanded rowModel
    expandedRealizes expandedEdges
  refine ⟨scheme, member, rows,
    (CommonPresenceConstraintGraph.restrict (Extended (splitAtoms atoms).pool) expanded, expanded),
    recovered.1, ?_⟩
  intro index
  have same := recovered.2
    (CommonOptionalPool.embed (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) index)
  change Equivalent
    (scheme.instantiateValues rows
      (CommonPresenceConstraintGraph.restrict (Extended (splitAtoms atoms).pool) expanded, expanded) index)
    (CommonOptionalPool.extendValues (splitAtoms atoms).pool (queries (splitAtoms atoms).pool)
      rows values (CommonOptionalPool.embed (splitAtoms atoms).pool (queries (splitAtoms atoms).pool) index)) at same
  rw [CommonOptionalPool.extendValues_original] at same
  exact same

/-- Exact common scheme coverage, with independent input rows and node
assignments. The premises describe finite input syntax only. Generated
source/Core corollaries below supply all of them internally. -/
theorem solve_all_instances_exact (atoms : List (Atom (Fin m)))
    (good : PresenceGeneratedChildGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rowShapes : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (splitAtoms atoms).pool.size → Ty) :
    (compile atoms).Models rows values ↔
      ∃ scheme ∈ solveAll atoms, ∃ rowParameters, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  constructor
  · exact model_is_instance atoms good widths rowShapes rows values
  · rintro ⟨scheme, returned, rowParameters, parameters, sameRows, sameValues⟩
    have model := all_parameters_models atoms scheme returned rowParameters parameters
    rw [sameRows] at model
    exact (compiled_models_congr atoms rows _ values sameValues).mp model

theorem generated_solve_all_instances_exact (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty) :
    (compile clause.pack).Models rows values ↔
      ∃ scheme ∈ solveAll clause.pack, ∃ rowParameters, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  solve_all_instances_exact clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) rows values

theorem generated_core_solve_all_instances_exact (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty) :
    (compile clause.pack).Models rows values ↔
      ∃ scheme ∈ solveAll clause.pack, ∃ rowParameters, ∃ parameters : scheme.Parameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  solve_all_instances_exact clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause generated)
    (CommonPresenceSourceFamily.generated_core_row_shapes expression clause generated) rows values

end Yulang.CommonBoundRefSolved
