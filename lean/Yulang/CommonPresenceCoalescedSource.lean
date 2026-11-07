import Yulang.CommonPresenceVariableBounds
import Yulang.CommonPresenceSourceFamily

/-!
# Actual source inference after coalescing common variable edges

This finite algorithm consumes the actual presence generator, normalizes its
formula, packs every binder, collects a shared constructor pool, and coalesces
all variable-incident edges. Its finite scheme stores that pool, the original
edge topology, the solved row syntax, and the output IDs. Instantiation uses
three families: arbitrary common rows, arbitrary common types for the original
variables, and arbitrary common types for the recursive equation parameters.

Only the computed rigid-to-rigid comparisons remain in `ResidualHolds`.
Those comparisons read instantiated graph nodes and can therefore restrict
the parameters. This is not yet an unconstrained inference family. The
missing step is symbolic decomposition and finite saturation of those rigid
comparisons, including full record/default and shared negative occurrences.

Both principal theorems quantify over every closed expression and every
result. Generated row shapes, binder support, equation witnesses, successful
inference, and fuel are not public premises. The independent typing judgment
is unchanged, and the public `Core.infer` is neither introduced nor replaced.
-/

namespace Yulang.CommonPresenceCoalescedSource

open Core.PresenceGeneration
open PresenceNormalForm (Atom Clause normalise)
open PresenceSourceConstraintSupport (GoodAtoms)
open CommonPresenceConstraintGraph
open CommonPresenceClauseFamily (declareRows declared_rows_models_exact)
open CommonPresenceVariableBounds (solve solveRows)
open Common (Ty Row)
open Inference (Expr)

/-- Finite syntax only. The source pool's closure/distinctness proofs are
syntactic and erased; no typing judgment or semantic model certificate is
stored in a scheme. Original type and row slot identities remain shared. -/
structure Scheme where
  parameters : Nat
  pool : PresenceOpenTailGenerationLowering.Pool parameters
  rows : RowFlowSchemes.Scheme parameters
  edges : List (Fin pool.size × Fin pool.size)
  outputValue : Fin pool.size
  outputRow : Fin parameters

def Scheme.instantiateRows (scheme : Scheme) (rows : Fin scheme.parameters → Row) :
    Fin scheme.parameters → Row :=
  RowFlowSchemes.instantiate Common.rowAlgebra scheme.rows rows

def Scheme.instantiateValues (scheme : Scheme) (rows : Fin scheme.parameters → Row)
    (types : Fin scheme.parameters → Ty) (recursiveTypes : Fin scheme.pool.size → Ty) :
    Fin scheme.pool.size → Ty :=
  solve scheme.pool scheme.edges (scheme.instantiateRows rows) types recursiveTypes

def Scheme.instantiate (scheme : Scheme) (rows : Fin scheme.parameters → Row)
    (types : Fin scheme.parameters → Ty) (recursiveTypes : Fin scheme.pool.size → Ty) : Comp Common.model :=
  ((scheme.instantiateValues rows types recursiveTypes) scheme.outputValue,
    (scheme.instantiateRows rows) scheme.outputRow)

def Scheme.rigidComparisons (scheme : Scheme) : List (Fin scheme.pool.size × Fin scheme.pool.size) :=
  CommonBoundCoalescing.rigidComparisons (CommonPresenceVariableBounds.template scheme.pool scheme.edges)

def Scheme.ResidualHolds (scheme : Scheme) (rows : Fin scheme.parameters → Row)
    (types : Fin scheme.parameters → Ty) (recursiveTypes : Fin scheme.pool.size → Ty) : Prop :=
  EdgesHold scheme.rigidComparisons (scheme.instantiateValues rows types recursiveTypes)

/-- Every comparison retained by any scheme has two genuine constructor
endpoints in its finite source pool. Children can still refer to variables. -/
theorem Scheme.residuals_rigid (scheme : Scheme) (edge : Fin scheme.pool.size × Fin scheme.pool.size)
    (member : edge ∈ scheme.rigidComparisons) :
    CommonPresenceVariableBounds.inputAt scheme.pool edge.1 = none ∧
      CommonPresenceVariableBounds.inputAt scheme.pool edge.2 = none :=
  CommonPresenceVariableBounds.residuals_rigid scheme.pool scheme.edges edge member

def ofClause (clause : Clause (Option Empty)) (good : GoodAtoms clause.pack) : Scheme where
  parameters := clause.locals + 1
  pool := (splitAtoms clause.pack).pool
  rows := CommonRowTailInference.rowScheme (declareRows clause.pack good)
  edges := (compile clause.pack).edges
  outputValue := (compile clause.pack).input (Fin.last clause.locals)
  outputRow := Fin.last clause.locals

/-- The actual generator supplies all row-shape proofs. Packing preserves
the sharing of captured slots across value-let alternatives and occurrences. -/
def inferSource (expression : Expr) : List Scheme :=
  (normalise (principal ([] : SchemeEnv Empty) expression)).attach.map fun clause =>
    ofClause clause.val (PresenceSourceConstraintSupport.generated_row_shapes expression clause.val clause.property)

def inferCore (expression : Core.Required.Term) : List Scheme :=
  (normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)).attach.map fun clause =>
    ofClause clause.val
      (CommonPresenceSourceFamily.generated_core_row_shapes expression clause.val clause.property)

/-- Every satisfying packed source assignment is recovered by the concrete
three-family algorithm. The result value is demand equivalent and the result
row is literally equal. Only rigid comparisons remain on the parameters. -/
theorem clause_parameter_retraction (clause : Clause (Option Empty)) (good : GoodAtoms clause.pack)
    (assignment : Fin (clause.locals + 1) → Comp Common.model)
    (accepted : PresenceNormalForm.All Common.model assignment clause.pack) :
    ∃ rows : Fin (ofClause clause good).parameters → Row,
    ∃ types : Fin (ofClause clause good).parameters → Ty,
    ∃ recursiveTypes : Fin (ofClause clause good).pool.size → Ty,
      (ofClause clause good).ResidualHolds rows types recursiveTypes ∧
      Common.Equivalent ((ofClause clause good).instantiate rows types recursiveTypes).1
        (assignment (Fin.last clause.locals)).1 ∧
      ((ofClause clause good).instantiate rows types recursiveTypes).2 =
        (assignment (Fin.last clause.locals)).2 := by
  obtain ⟨nodes, models, readback⟩ := (compile_atoms_exact clause.pack assignment).mp accepted
  obtain ⟨rows, types, recursiveTypes, rowSame, residual, same⟩ :=
    (CommonPresenceVariableBounds.compiled_joint_elimination_exact clause.pack good
      (fun index => (assignment index).2) nodes).mp models
  refine ⟨rows, types, recursiveTypes, residual, ?_, ?_⟩
  · have output := same ((compile clause.pack).input (Fin.last clause.locals))
    have equal := congrArg Prod.fst (congrFun readback (Fin.last clause.locals))
    change Common.Equivalent _ (assignment (Fin.last clause.locals)).1
    rw [← equal]
    exact output
  · change (solveRows clause.pack good rows) (Fin.last clause.locals) = _
    exact congrFun rowSame (Fin.last clause.locals)

/-- Instantiation has already solved the original equations, every explicit
row constraint, and every variable edge. Rigid comparisons are explicit and
are the sole semantic premise. -/
theorem clause_instantiation_models (clause : Clause (Option Empty)) (good : GoodAtoms clause.pack)
    (rows : Fin (ofClause clause good).parameters → Row)
    (types : Fin (ofClause clause good).parameters → Ty)
    (recursiveTypes : Fin (ofClause clause good).pool.size → Ty)
    (residual : (ofClause clause good).ResidualHolds rows types recursiveTypes) :
    (compile clause.pack).Models ((ofClause clause good).instantiateRows rows)
      ((ofClause clause good).instantiateValues rows types recursiveTypes) := by
  refine ⟨CommonPresenceVariableBounds.solve_realizes _ _ _ types recursiveTypes,
    CommonPresenceVariableBounds.solve_edges _ _ _ types recursiveTypes residual, ?_⟩
  exact (declared_rows_models_exact clause.pack good _).mp
    (CommonRowTailInference.rowScheme_models (declareRows clause.pack good) rows)

/-- All closed source expressions and all results, including both binding
forms, record construction and whole defaults. The remaining rigid comparison
condition is displayed; no support, success, model or fuel premise is hidden. -/
theorem residual_source_principal (expression : Expr) (result : Comp Common.model) :
    Typing Common.model [] expression result ↔
      ∃ scheme ∈ inferSource expression,
      ∃ rows : Fin scheme.parameters → Row,
      ∃ types : Fin scheme.parameters → Ty,
      ∃ recursiveTypes : Fin scheme.pool.size → Ty,
        scheme.ResidualHolds rows types recursiveTypes ∧
          Comp.le Common.model (scheme.instantiate rows types recursiveTypes) result := by
  constructor
  · intro typed
    obtain ⟨clause, member, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_source_exact Common.model expression result).mp typed
    let good := PresenceSourceConstraintSupport.generated_row_shapes expression clause member
    obtain ⟨rows, types, recursiveTypes, residual, same, rowSame⟩ :=
      clause_parameter_retraction clause good assignment accepted
    refine ⟨ofClause clause good, List.mem_map.mpr ⟨⟨clause, member⟩, by simp, rfl⟩,
      rows, types, recursiveTypes, residual, ?_, ?_⟩
    · change Common.Subtype _ result.1
      simpa only [output] using same.1
    · change Common.rowLe _ result.2
      rw [rowSame, output]
      exact Common.rowLe_refl _
  · rintro ⟨scheme, member, rows, types, recursiveTypes, residual, bounded⟩
    obtain ⟨clause, _, rfl⟩ := List.mem_map.mp member
    let good := PresenceSourceConstraintSupport.generated_row_shapes expression clause.val clause.property
    have models := clause_instantiation_models clause.val good rows types recursiveTypes residual
    have accepted := compile_atoms_reflects clause.val.pack _ _ models
    have typed : Typing Common.model [] expression
        ((ofClause clause.val good).instantiate rows types recursiveTypes) := by
      apply (PresenceNormalForm.closed_source_exact Common.model expression _).mpr
      exact ⟨clause.val, clause.property, _, rfl, accepted⟩
    exact CommonPresenceSourceFamily.typing_subsume typed result bounded

/-- The actual Core lowering, binder packing, row family, variable-bound
coalescing and regular equation solving are connected for every closed term
and result. Only the explicit rigid residual awaits symbolic saturation. -/
theorem residual_core_principal (expression : Core.Required.Term) (result : Comp Common.model) :
    Core.Typing (CoreRules.model Common.model) [] expression result ↔
      ∃ scheme ∈ inferCore expression,
      ∃ rows : Fin scheme.parameters → Row,
      ∃ types : Fin scheme.parameters → Ty,
      ∃ recursiveTypes : Fin scheme.pool.size → Ty,
        scheme.ResidualHolds rows types recursiveTypes ∧
          Comp.le Common.model (scheme.instantiate rows types recursiveTypes) result := by
  constructor
  · intro typed
    obtain ⟨clause, member, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_core_exact Common.model expression result).mp typed
    let good := CommonPresenceSourceFamily.generated_core_row_shapes expression clause member
    obtain ⟨rows, types, recursiveTypes, residual, same, rowSame⟩ :=
      clause_parameter_retraction clause good assignment accepted
    refine ⟨ofClause clause good, List.mem_map.mpr ⟨⟨clause, member⟩, by simp, rfl⟩,
      rows, types, recursiveTypes, residual, ?_, ?_⟩
    · change Common.Subtype _ result.1
      simpa only [output] using same.1
    · change Common.rowLe _ result.2
      rw [rowSame, output]
      exact Common.rowLe_refl _
  · rintro ⟨scheme, member, rows, types, recursiveTypes, residual, bounded⟩
    obtain ⟨clause, _, rfl⟩ := List.mem_map.mp member
    let good := CommonPresenceSourceFamily.generated_core_row_shapes expression clause.val clause.property
    have models := clause_instantiation_models clause.val good rows types recursiveTypes residual
    have accepted := compile_atoms_reflects clause.val.pack _ _ models
    have typed : Core.Typing (CoreRules.model Common.model) [] expression
        ((ofClause clause.val good).instantiate rows types recursiveTypes) := by
      apply (PresenceNormalForm.closed_core_exact Common.model expression _).mpr
      exact ⟨clause.val, clause.property, _, rfl, accepted⟩
    exact CommonPresenceSourceFamily.core_typing_subsume expression _ result typed bounded

end Yulang.CommonPresenceCoalescedSource
