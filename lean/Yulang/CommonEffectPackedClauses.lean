import Yulang.CommonEffectClauseNormalisation
import Yulang.CommonSignedValueUnionSolver
import Yulang.CommonEffectRowQuantifiers

/-! Shared numeric slots for normalized effect clauses. The value graph and
signed row constraints use exactly the same original computations. The actual
mixed solver recovers ALL compiled value nodes, not just the result. -/
namespace Yulang.CommonEffectPackedClauses
open Common (Ty Row Equivalent)
open Core.PresenceGeneration (Comp CompTerm extend)
open CommonEffectRequestGeneration (Computation)
open CommonEffectClauses (Atom Clause All)
open PresenceNormalForm (resultName)

variable {scopes inputs : Nat}

def pack (clause : Clause scopes (Option Empty)) : List (Atom scopes (Fin (clause.locals + 1))) :=
  clause.atoms.map (Atom.rename (resultName clause.locals))

theorem pack_exact (clause : Clause scopes (Option Empty)) (result : Computation) :
    clause.Satisfiable (extend Empty.elim result) ↔
      ∃ assignment : Fin (clause.locals + 1) → Computation,
        assignment (Fin.last clause.locals) = result ∧ All assignment (pack clause) := by
  constructor
  · rintro ⟨values, held⟩
    refine ⟨Fin.lastCases result values, Fin.lastCases_last, ?_⟩
    rw [pack, CommonEffectClauses.all_rename]
    have same : Fin.lastCases result values ∘ resultName clause.locals = Sum.elim values (extend Empty.elim result) := by
      funext name
      cases name with
      | inl index => simp [resultName]
      | inr name =>
        cases name with
        | none => simp [resultName, Core.PresenceGeneration.extend]
        | some impossible => exact impossible.elim
    rw [same]
    exact held
  · rintro ⟨assignment, resultEqual, held⟩
    refine ⟨fun index => assignment index.castSucc, ?_⟩
    rw [pack, CommonEffectClauses.all_rename] at held
    have same : assignment ∘ resultName clause.locals =
        Sum.elim (fun index => assignment index.castSucc) (extend Empty.elim result) := by
      funext name
      cases name with
      | inl => rfl
      | inr name =>
        cases name with
        | none => exact resultEqual
        | some impossible => exact impossible.elim
    rw [same] at held
    exact held

def typeAtoms : List (Atom scopes α) → List (PresenceNormalForm.Atom α)
  | [] => []
  | .tyLe first last :: rest => .tyLe first last :: typeAtoms rest
  | .rowLe _ _ :: rest => typeAtoms rest

def rowConstraints : List (Atom scopes (Fin inputs)) → CommonSignedUnionCompilation.Problem scopes inputs
  | [] => []
  | .tyLe _ _ :: rest => rowConstraints rest
  | .rowLe first last :: rest => ⟨first, last⟩ :: rowConstraints rest

theorem row_atom_exact (first : CommonEffectRequestGeneration.RowExpr scopes (Fin inputs))
    (last : Core.PresenceGeneration.RowTerm (Fin inputs)) (assignment : Fin inputs → Computation) :
    Common.rowLe (CommonSignedExpressionPool.evaluate (fun index => (assignment index).2) first)
      (CommonSignedUnionCompilation.upperEval (fun index => (assignment index).2) last) ↔
        (Atom.rowLe first last).Holds assignment := by
  have lower := CommonEffectRowQuantifiers.rowExpr_congr first
    (fun index => ((.base .unit : Ty), (assignment index).2)) assignment (fun _ => rfl)
  have upper := CommonEffectRowQuantifiers.rowTerm_congr last
    (fun index => ((.base .unit : Ty), (assignment index).2)) assignment (fun _ => rfl)
  simp only [CommonSignedExpressionPool.evaluate, CommonSignedUnionCompilation.upperEval, lower, upper]
  rfl

theorem all_split_exact (atoms : List (Atom scopes (Fin inputs))) (assignment : Fin inputs → Computation) :
    All assignment atoms ↔ PresenceNormalForm.All Common.model assignment (typeAtoms atoms) ∧
      CommonSignedUnionCompilation.Models (rowConstraints atoms) (fun index => (assignment index).2) := by
  induction atoms with
  | nil => simp [All, typeAtoms, rowConstraints, PresenceNormalForm.All, CommonSignedUnionCompilation.Models]
  | cons atom rest ih =>
    cases atom with
    | tyLe first last =>
      simp only [All, typeAtoms, rowConstraints, List.mem_cons, forall_eq_or_imp, PresenceNormalForm.All,
        Atom.Holds, PresenceNormalForm.Atom.Holds] at *
      rw [ih]
      exact and_assoc.symm
    | rowLe first last =>
      simp only [All, typeAtoms, rowConstraints, List.mem_cons, forall_eq_or_imp, CommonSignedUnionCompilation.Models] at *
      rw [row_atom_exact first last assignment, ih]
      exact and_left_comm

abbrev Models (atoms : List (Atom scopes (Fin inputs))) (rows : Fin inputs → Row)
    (values : Fin (CommonPresenceConstraintGraph.splitAtoms (typeAtoms atoms)).pool.size → Ty) : Prop :=
  CommonSignedValueUnionSolver.Models (typeAtoms atoms) (rowConstraints atoms) rows values

theorem compile_exact (atoms : List (Atom scopes (Fin inputs))) (assignment : Fin inputs → Computation) :
    All assignment atoms ↔
      ∃ values, Models atoms (fun index => (assignment index).2) values ∧
        (CommonPresenceConstraintGraph.compile (typeAtoms atoms)).readback (fun index => (assignment index).2) values = assignment := by
  rw [all_split_exact, CommonPresenceConstraintGraph.compile_atoms_exact]
  constructor
  · rintro ⟨⟨values, model, same⟩, rows⟩
    exact ⟨values, ⟨model, rows⟩, same⟩
  · rintro ⟨values, ⟨model, rows⟩, same⟩
    exact ⟨⟨values, model, same⟩, rows⟩

theorem compile_reflects (atoms : List (Atom scopes (Fin inputs))) (rows : Fin inputs → Row)
    (values : Fin (CommonPresenceConstraintGraph.splitAtoms (typeAtoms atoms)).pool.size → Ty) (model : Models atoms rows values) :
    All ((CommonPresenceConstraintGraph.compile (typeAtoms atoms)).readback rows values) atoms := by
  apply (all_split_exact atoms _).mpr
  exact ⟨CommonPresenceConstraintGraph.compile_atoms_reflects _ rows values model.1, model.2⟩

def solve (atoms : List (Atom scopes (Fin inputs))) := CommonSignedValueUnionSolver.solve (typeAtoms atoms) (rowConstraints atoms)

theorem solve_all_instances_exact (atoms : List (Atom scopes (Fin inputs)))
    (good : PresenceGeneratedChildGrammar.GoodAtoms (typeAtoms atoms))
    (widths : PresenceGeneratedWidth.WidthAtoms (typeAtoms atoms))
    (rows : Fin inputs → Row) (values : Fin (CommonPresenceConstraintGraph.splitAtoms (typeAtoms atoms)).pool.size → Ty) :
    Models atoms rows values ↔
      ∃ scheme ∈ solve atoms, ∃ rowParameters : scheme.RowParameters, ∃ parameters : scheme.ValueParameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) :=
  CommonSignedValueUnionSolver.solve_all_instances_exact (typeAtoms atoms) (rowConstraints atoms) good widths rows values

theorem all_parameters_models (atoms : List (Atom scopes (Fin inputs)))
    (scheme : CommonSignedValueUnionSolver.Scheme (CommonPresenceConstraintGraph.splitAtoms (typeAtoms atoms)).pool)
    (returned : scheme ∈ solve atoms) (rowParameters : scheme.RowParameters) (parameters : scheme.ValueParameters) :
    Models atoms (scheme.instantiateRows rowParameters) (scheme.instantiateValues rowParameters parameters) :=
  CommonSignedValueUnionSolver.all_parameters_models (typeAtoms atoms) (rowConstraints atoms) scheme returned rowParameters parameters
end Yulang.CommonEffectPackedClauses
