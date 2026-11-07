import Yulang.CommonBoundRefSolver
import Yulang.CommonPresenceSourceFamily

/-!
# Solved common schemes for the presence source and Core fragment

The algorithm generates the actual source/Core formula, normalizes and packs
its binders, compiles each clause into a shared graph, and invokes the finite
bound-reference solver. Each returned source scheme contains only finite
solver syntax and its two output IDs.

Parameters form the ordinary product of arbitrary common row parameters and
the solver's arbitrary type/recursive-node parameters. No residual predicate,
typing judgment, generated formula, model law or successful-solver witness is
stored in a scheme or imposed on an instantiation.

The Core interpretation is `CoreRules.model Common.model`, the presence
fragment. This module does not identify it with the effect or qualified Core
models, and leaves every older inference entry and theorem unchanged.
-/

namespace Yulang.CommonSolvedSource

open Core.PresenceGeneration
open PresenceNormalForm (Clause normalise)
open CommonPresenceConstraintGraph (compile compile_atoms_exact compile_atoms_reflects)
open Common (Ty Row)
open Inference (Expr)

structure Scheme where
  rowSlots : Nat
  originalSlots : Nat
  solution : CommonBoundRefSolver.Scheme rowSlots originalSlots
  outputValue : Fin originalSlots
  outputRow : Fin rowSlots

abbrev Scheme.Parameters (scheme : Scheme) :=
  (Fin scheme.rowSlots → Row) × scheme.solution.Parameters

def Scheme.instantiate (scheme : Scheme) (parameters : scheme.Parameters) : Comp Common.model :=
  (scheme.solution.instantiateValues parameters.1 parameters.2 scheme.outputValue,
    scheme.solution.instantiateRows parameters.1 scheme.outputRow)

/-- Merely an inhabitance witness for the unrestricted parameter product;
the inference computation never selects or fixes these parameters. -/
theorem Scheme.parameters_nonempty (scheme : Scheme) : Nonempty scheme.Parameters :=
  ⟨(fun _ => Common.rowEmpty), (fun _ => .bottom), (fun _ => .bottom)⟩

def ofClause (clause : Clause (Option Empty))
    (solution : CommonBoundRefSolver.Scheme (clause.locals + 1) (compile clause.pack).size) : Scheme where
  rowSlots := clause.locals + 1
  originalSlots := (compile clause.pack).size
  solution := solution
  outputValue := (compile clause.pack).input (Fin.last clause.locals)
  outputRow := Fin.last clause.locals

def solveClause (clause : Clause (Option Empty)) : List Scheme :=
  (CommonBoundRefSolver.solveAll (compile clause.pack)).map (ofClause clause)

/-- Actual finite source inference. There are no grammar proofs in its input. -/
def inferSource (expression : Expr) : List Scheme :=
  (normalise (principal ([] : SchemeEnv Empty) expression)).flatMap solveClause

/-- The actual Core formula includes the established presence syntax gate;
terms without a rule in this model produce no satisfying clause. -/
def inferCore (expression : Core.Required.Term) : List Scheme :=
  (normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression)).flatMap solveClause

@[simp] theorem inferCore_embed (expression : Expr) :
    inferCore (Core.Required.embed expression) = inferSource expression := by
  simp only [inferCore, inferSource, CoreRules.principalCore, principal, CoreRules.generateCore_embed]

/-- Every returned source scheme and every arbitrary parameter choice gives
a typing in the independent common presence judgment. -/
theorem source_instantiates (expression : Expr) (scheme : Scheme)
    (member : scheme ∈ inferSource expression) (parameters : scheme.Parameters) :
    Typing Common.model [] expression (scheme.instantiate parameters) := by
  obtain ⟨clause, generated, returned⟩ := List.mem_flatMap.mp member
  obtain ⟨solution, solved, rfl⟩ := List.mem_map.mp returned
  have models := CommonBoundRefSolver.all_parameter_sound clause.pack solution solved parameters.1 parameters.2
  have accepted := compile_atoms_reflects clause.pack _ _ models
  exact (PresenceNormalForm.closed_source_exact Common.model expression _).mpr
    ⟨clause, generated, _, rfl, accepted⟩

theorem core_instantiates (expression : Core.Required.Term) (scheme : Scheme)
    (member : scheme ∈ inferCore expression) (parameters : scheme.Parameters) :
    Core.Typing (CoreRules.model Common.model) [] expression (scheme.instantiate parameters) := by
  obtain ⟨clause, generated, returned⟩ := List.mem_flatMap.mp member
  obtain ⟨solution, solved, rfl⟩ := List.mem_map.mp returned
  have models := CommonBoundRefSolver.all_parameter_sound clause.pack solution solved parameters.1 parameters.2
  have accepted := compile_atoms_reflects clause.pack _ _ models
  exact (PresenceNormalForm.closed_core_exact Common.model expression _).mpr
    ⟨clause, generated, _, rfl, accepted⟩

/-- Every satisfying packed source assignment is recovered with the same
result row and a demand-equivalent result value, using unrestricted parameters. -/
theorem source_parameter_retraction (expression : Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression))
    (assignment : Fin (clause.locals + 1) → Comp Common.model)
    (accepted : PresenceNormalForm.All Common.model assignment clause.pack) :
    ∃ solution ∈ CommonBoundRefSolver.solveAll (compile clause.pack),
      ∃ parameters : (ofClause clause solution).Parameters,
        Common.Equivalent ((ofClause clause solution).instantiate parameters).1
          (assignment (Fin.last clause.locals)).1 ∧
        ((ofClause clause solution).instantiate parameters).2 = (assignment (Fin.last clause.locals)).2 := by
  obtain ⟨nodes, models, readback⟩ := (compile_atoms_exact clause.pack assignment).mp accepted
  obtain ⟨solution, returned, rowParameters, parameters, rowSame, same⟩ :=
    (CommonBoundRefSolver.generated_models_exact expression clause generated
      (fun index => (assignment index).2) nodes).mp models
  refine ⟨solution, returned, ⟨rowParameters, parameters⟩, ?_, ?_⟩
  · have output := same ((compile clause.pack).input (Fin.last clause.locals))
    have equal := congrArg Prod.fst (congrFun readback (Fin.last clause.locals))
    change Common.Equivalent _ (assignment (Fin.last clause.locals)).1
    rw [← equal]
    exact output
  · exact congrFun rowSame (Fin.last clause.locals)

theorem core_parameter_retraction (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression))
    (assignment : Fin (clause.locals + 1) → Comp Common.model)
    (accepted : PresenceNormalForm.All Common.model assignment clause.pack) :
    ∃ solution ∈ CommonBoundRefSolver.solveAll (compile clause.pack),
      ∃ parameters : (ofClause clause solution).Parameters,
        Common.Equivalent ((ofClause clause solution).instantiate parameters).1
          (assignment (Fin.last clause.locals)).1 ∧
        ((ofClause clause solution).instantiate parameters).2 = (assignment (Fin.last clause.locals)).2 := by
  obtain ⟨nodes, models, readback⟩ := (compile_atoms_exact clause.pack assignment).mp accepted
  obtain ⟨solution, returned, rowParameters, parameters, rowSame, same⟩ :=
    (CommonBoundRefSolver.generated_core_models_exact expression clause generated
      (fun index => (assignment index).2) nodes).mp models
  refine ⟨solution, returned, ⟨rowParameters, parameters⟩, ?_, ?_⟩
  · have output := same ((compile clause.pack).input (Fin.last clause.locals))
    have equal := congrArg Prod.fst (congrFun readback (Fin.last clause.locals))
    change Common.Equivalent _ (assignment (Fin.last clause.locals)).1
    rw [← equal]
    exact output
  · exact congrFun rowSame (Fin.last clause.locals)

/-- Every closed source expression and every result computation. All row,
type and recursive-node parameters are free; no support checker, successful
inference, solver solution, residual condition or fuel is a premise. -/
theorem source_principal (expression : Expr) (result : Comp Common.model) :
    Typing Common.model [] expression result ↔
      ∃ scheme ∈ inferSource expression, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result := by
  constructor
  · intro typed
    obtain ⟨clause, generated, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_source_exact Common.model expression result).mp typed
    obtain ⟨solution, returned, parameters, same, rowSame⟩ :=
      source_parameter_retraction expression clause generated assignment accepted
    refine ⟨ofClause clause solution,
      List.mem_flatMap.mpr ⟨clause, generated, List.mem_map.mpr ⟨solution, returned, rfl⟩⟩,
      parameters, ?_, ?_⟩
    · change Common.Subtype _ result.1
      simpa only [output] using same.1
    · change Common.rowLe _ result.2
      rw [rowSame, output]
      exact Common.rowLe_refl _
  · rintro ⟨scheme, member, parameters, bounded⟩
    exact CommonPresenceSourceFamily.typing_subsume
      (source_instantiates expression scheme member parameters) result bounded

/-- The corresponding all-result theorem for the independent Core presence
model. Record construction, strict whole defaults and both binding forms
are included; no claim about other Core typing models is made. -/
theorem core_principal (expression : Core.Required.Term) (result : Comp Common.model) :
    Core.Typing (CoreRules.model Common.model) [] expression result ↔
      ∃ scheme ∈ inferCore expression, ∃ parameters : scheme.Parameters,
        Comp.le Common.model (scheme.instantiate parameters) result := by
  constructor
  · intro typed
    obtain ⟨clause, generated, assignment, output, accepted⟩ :=
      (PresenceNormalForm.closed_core_exact Common.model expression result).mp typed
    obtain ⟨solution, returned, parameters, same, rowSame⟩ :=
      core_parameter_retraction expression clause generated assignment accepted
    refine ⟨ofClause clause solution,
      List.mem_flatMap.mpr ⟨clause, generated, List.mem_map.mpr ⟨solution, returned, rfl⟩⟩,
      parameters, ?_, ?_⟩
    · change Common.Subtype _ result.1
      simpa only [output] using same.1
    · change Common.rowLe _ result.2
      rw [rowSame, output]
      exact Common.rowLe_refl _
  · rintro ⟨scheme, member, parameters, bounded⟩
    exact CommonPresenceSourceFamily.core_typing_subsume expression _ result
      (core_instantiates expression scheme member parameters) bounded

theorem source_empty_iff (expression : Expr) :
    inferSource expression = [] ↔ ¬ ∃ result, Typing Common.model [] expression result := by
  constructor
  · intro empty ⟨result, typed⟩
    obtain ⟨scheme, member, _, _⟩ := (source_principal expression result).mp typed
    simp only [empty, List.not_mem_nil] at member
  · intro untypable
    cases found : inferSource expression with
    | nil => rfl
    | cons scheme rest =>
        have member : scheme ∈ inferSource expression := by rw [found]; exact List.mem_cons_self
        obtain ⟨parameters⟩ := scheme.parameters_nonempty
        exact False.elim (untypable ⟨_, source_instantiates expression scheme member parameters⟩)

theorem core_empty_iff (expression : Core.Required.Term) :
    inferCore expression = [] ↔
      ¬ ∃ result, Core.Typing (CoreRules.model Common.model) [] expression result := by
  constructor
  · intro empty ⟨result, typed⟩
    obtain ⟨scheme, member, _, _⟩ := (core_principal expression result).mp typed
    simp only [empty, List.not_mem_nil] at member
  · intro untypable
    cases found : inferCore expression with
    | nil => rfl
    | cons scheme rest =>
        have member : scheme ∈ inferCore expression := by rw [found]; exact List.mem_cons_self
        obtain ⟨parameters⟩ := scheme.parameters_nonempty
        exact False.elim (untypable ⟨_, core_instantiates expression scheme member parameters⟩)

end Yulang.CommonSolvedSource
