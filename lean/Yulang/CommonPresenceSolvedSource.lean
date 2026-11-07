import Yulang.CommonBoundRefSolvedExact
import Yulang.CommonPresenceSourceFamily

/-!
# Residual-free source inference from finite common solved families

A source scheme stores an actual simultaneous row/clamped-value family and
its original output computation ID. Parameters are unrestricted common rows,
original-variable types and recursive-node types. The same row assignment
is used inside the value graph and for the output computation.

The actual source generator, normalizer, binder packer and finite subtype
worklist are executed before a family is returned. Soundness holds for every
parameter assignment, and every independent typing derivation is recovered.
-/

namespace Yulang.CommonPresenceSolvedSource

open Core.PresenceGeneration
open PresenceNormalForm (Clause normalise)
open CommonPresenceConstraintGraph
open Common (Ty Row)
open Inference (Expr)

/-- Finite syntax only, with the original shared output ID. No model,
residual predicate or proof of typing is stored in the scheme. -/
structure Scheme where
  parameters : Nat
  family : CommonClampedRowFamily.Scheme parameters
  output : Fin parameters

abbrev Scheme.Parameters (scheme : Scheme) :=
  (Fin scheme.parameters → Row) × scheme.family.Parameters

def Scheme.instantiate (scheme : Scheme) (parameters : scheme.Parameters) : Comp Common.model :=
  (scheme.family.instantiateValues parameters.1 parameters.2 (scheme.family.pool.input scheme.output),
    scheme.family.instantiateRows parameters.1 scheme.output)

/-- A single freely chosen parameter assignment. It is used only to witness
that a returned family is inhabited, never to restrict its instances. -/
def Scheme.defaultParameters (scheme : Scheme) : scheme.Parameters :=
  (fun _ => Common.rowEmpty, (fun _ => .bottom, fun _ => .bottom))

def Scheme.Instance (scheme : Scheme) (target : Comp Common.model) : Prop :=
  ∃ parameters : scheme.Parameters, Comp.le Common.model (scheme.instantiate parameters) target

def ofClause (clause : Clause (Option Empty))
    (solution : CommonBoundRefSolved.Scheme (splitAtoms clause.pack).pool) : Scheme where
  parameters := clause.locals + 1
  family := solution.family
  output := Fin.last clause.locals

/-- The finite source pipeline. No assignment or semantic certificate is an
input to normalization, packing or the actual branch-solving computation. -/
def inferSource (expression : Expr) : List Scheme :=
  (normalise (principal ([] : SchemeEnv Empty) expression)).flatMap fun clause =>
    (CommonBoundRefSolved.solveAll clause.pack).map (ofClause clause)

def inferCore (expression : Core.Required.Term) : List Scheme :=
  if Core.InferenceSyntax.supported expression then inferSource (CoreRules.decode expression)
  else []

/-- The original computation ID is preserved through optional-pool extension
and the clamped shared graph. This is literal equality of computations. -/
theorem ofClause_instantiate (clause : Clause (Option Empty))
    (solution : CommonBoundRefSolved.Scheme (splitAtoms clause.pack).pool)
    (rows : Fin (clause.locals + 1) → Row) (values : solution.Parameters) :
    (ofClause clause solution).instantiate (rows, values) =
      (compile clause.pack).readback (solution.instantiateRows rows)
        (solution.instantiateValues rows values) (Fin.last clause.locals) := by
  apply Prod.ext
  · exact (CommonBoundRefSolved.Scheme.instantiate_input solution rows values
      (Fin.last clause.locals)).symm
  · rfl

/-- Every actual generated clause and every arbitrary independent satisfying
packed assignment are recovered by a returned family. Values are demand
equivalent and the output row is literally unchanged. -/
theorem clause_parameter_retraction (expression : Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression))
    (assignment : Fin (clause.locals + 1) → Comp Common.model)
    (accepted : PresenceNormalForm.All Common.model assignment clause.pack) :
    ∃ solution ∈ CommonBoundRefSolved.solveAll clause.pack,
    ∃ parameters : (ofClause clause solution).Parameters,
      Common.Equivalent ((ofClause clause solution).instantiate parameters).1
        (assignment (Fin.last clause.locals)).1 ∧
      ((ofClause clause solution).instantiate parameters).2 =
        (assignment (Fin.last clause.locals)).2 := by
  obtain ⟨nodes, models, readback⟩ := (compile_atoms_exact clause.pack assignment).mp accepted
  obtain ⟨solution, returned, rows, values, rowSame, same⟩ :=
    (CommonBoundRefSolved.generated_solve_all_instances_exact expression clause generated
      (fun index => (assignment index).2) nodes).mp models
  refine ⟨solution, returned, (rows, values), ?_, ?_⟩
  · rw [ofClause_instantiate]
    have equal := congrArg Prod.fst (congrFun readback (Fin.last clause.locals))
    change Common.Equivalent _ (assignment (Fin.last clause.locals)).1
    rw [← equal]
    exact same ((compile clause.pack).input (Fin.last clause.locals))
  · rw [ofClause_instantiate]
    exact congrFun rowSame (Fin.last clause.locals)

/-- Every returned solution of every actual source clause gives a typing
at all free row/type/recursive parameters, with no residual premise. -/
theorem clause_all_parameters (expression : Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression))
    (solution : CommonBoundRefSolved.Scheme (splitAtoms clause.pack).pool)
    (returned : solution ∈ CommonBoundRefSolved.solveAll clause.pack)
    (parameters : (ofClause clause solution).Parameters) :
    Typing Common.model [] expression ((ofClause clause solution).instantiate parameters) := by
  rcases parameters with ⟨rows, values⟩
  have model := CommonBoundRefSolved.all_parameters_models clause.pack solution returned rows values
  have accepted := compile_atoms_reflects clause.pack _ _ model
  apply (PresenceNormalForm.closed_source_exact Common.model expression _).mpr
  exact ⟨clause, generated, _, (ofClause_instantiate clause solution rows values).symm, accepted⟩

/-- Every closed source expression and every common result. The only
existential data are a computed finite scheme and its arbitrary parameters,
followed by ordinary result subsumption. -/
theorem source_principal (expression : Expr) (result : Comp Common.model) :
    Typing Common.model [] expression result ↔
      ∃ scheme ∈ inferSource expression, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result := by
  constructor
  · intro typed
    obtain ⟨clause, generated, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_source_exact Common.model expression result).mp typed
    obtain ⟨solution, returned, parameters, same, rowSame⟩ :=
      clause_parameter_retraction expression clause generated assignment accepted
    refine ⟨ofClause clause solution, List.mem_flatMap.mpr ⟨clause, generated,
      List.mem_map.mpr ⟨solution, returned, rfl⟩⟩, parameters, ?_, ?_⟩
    · change Common.Subtype _ result.1
      simpa only [output] using same.1
    · change Common.rowLe _ result.2
      rw [rowSame, output]
      exact Common.rowLe_refl _
  · rintro ⟨scheme, member, parameters, bounded⟩
    obtain ⟨clause, generated, member⟩ := List.mem_flatMap.mp member
    obtain ⟨solution, returned, rfl⟩ := List.mem_map.mp member
    exact CommonPresenceSourceFamily.typing_subsume
      (clause_all_parameters expression clause generated solution returned parameters) result bounded

theorem source_all_parameters (expression : Expr) (scheme : Scheme)
    (returned : scheme ∈ inferSource expression) (parameters : scheme.Parameters) :
    Typing Common.model [] expression (scheme.instantiate parameters) :=
  (source_principal expression _).mpr
    ⟨scheme, returned, parameters, Common.subtype_refl _, Common.rowLe_refl _⟩

/-- The same residual-free statement for every closed Core term and every
common result. The established syntax boundary is supplied by the independent
Core typing rules and the computation itself, not by the theorem caller. -/
theorem core_principal (expression : Core.Required.Term) (result : Comp Common.model) :
    Core.Typing (CoreRules.model Common.model) [] expression result ↔
      ∃ scheme ∈ inferCore expression, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result := by
  cases checked : Core.InferenceSyntax.supported expression with
  | false =>
      constructor
      · intro typed
        have inside := CoreRules.typing_syntax typed
        rw [checked] at inside
        cases inside
      · rintro ⟨scheme, member, _, _⟩
        simp only [inferCore, checked, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at member
  | true =>
      have bridge := CoreRules.conservative Common.model [] (CoreRules.decode expression) result
      have reconstructed : CoreRules.embed (CoreRules.decode expression) = expression :=
        Core.InferenceSyntax.embed_decode expression checked
      simp only [List.map_nil, reconstructed] at bridge
      simp only [inferCore, checked, ↓reduceIte]
      exact bridge.symm.trans (source_principal (CoreRules.decode expression) result)

end Yulang.CommonPresenceSolvedSource
