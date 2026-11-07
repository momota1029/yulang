import Yulang.CommonPresenceConstraintGraph

/-!
# Eliminating source graph definitions with the common joint equation family

Actual packed presence clauses are compiled to shared constructor equations
and subtype edges. The complete source row-shape invariant discharges the row
grammar of the existing simultaneous solver. Every parameter assignment then
satisfies all constructor equations and all explicit row constraints, and
every independent graph model is recovered with its rows literally unchanged.

The result eliminates the existential *definition* witnesses and the explicit
row constraints. Subtype comparisons between the instantiated graph nodes
remain explicit residual edges. No theorem here calls those edges solved or
claims a free-parameter source inference entry.
-/

namespace Yulang.CommonPresenceClauseFamily

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open PresenceNormalForm (Atom Clause)
open PresenceSourceConstraintSupport (GoodAtoms GoodAtom simpleRow)
open CommonPresenceConstraintGraph
open Common (Ty Row)

variable {m : Nat}

private theorem good_tail {atom : Atom (Fin m)} {rest : List (Atom (Fin m))}
    (good : GoodAtoms (atom :: rest)) : GoodAtoms rest :=
  fun actual member => good actual (List.mem_cons_of_mem _ member)

private theorem good_upper (lower upper : RowTerm (Fin m)) (rest : List (Atom (Fin m)))
    (good : GoodAtoms (.rowLe lower upper :: rest)) : simpleRow upper = true :=
  good _ List.mem_cons_self

def declareUpper (term : RowTerm (Fin m)) (good : simpleRow term = true) :
    CommonRowTailInference.Upper m :=
  match term with
  | .var index => .var index
  | .empty => .empty
  | .join _ _ => by cases good

@[simp] theorem declareUpper_term (term : RowTerm (Fin m)) (good : simpleRow term = true) :
    (declareUpper term good).term = PresenceSourceConstraintSupport.originalRow term := by
  cases term with
  | var | empty => rfl
  | join => cases good

/-- The source theorem supplies the proof of the finite row grammar. The
generated data contains only the actual row constraints; the proof is erased. -/
def declareRows (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    List (CommonRowTailInference.RowConstraint m) :=
  match atoms with
  | [] => []
  | .tyLe _ _ :: rest => declareRows rest (good_tail good)
  | .rowLe lower upper :: rest =>
      ⟨PresenceSourceConstraintSupport.originalRow lower,
        declareUpper upper (good_upper lower upper rest good)⟩ :: declareRows rest (good_tail good)

theorem declared_rows_exact (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    CommonRowTailInference.rowProblem (declareRows atoms good) =
      PresenceSourceConstraintSupport.explicitRows atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      cases atom <;>
        simp only [declareRows, CommonRowTailInference.rowProblem, List.map_cons,
          CommonRowTailInference.RowConstraint.erase,
          PresenceSourceConstraintSupport.explicitRows, ← ih (good_tail good)]
      rw [declareUpper_term]

theorem explicit_rows_exact (atoms : List (Atom (Fin m))) (rows : Fin m → Row) :
    RowFlowSchemes.Models Common.rowAlgebra
      (PresenceSourceConstraintSupport.explicitRows atoms) rows ↔
        RowsHold (splitAtoms atoms).rows rows := by
  induction atoms with
  | nil => simp [RowsHold, splitAtoms, PresenceSourceConstraintSupport.explicitRows,
      RowFlowSchemes.Models]
  | cons atom rest ih =>
      cases atom <;>
        simp only [splitAtoms, PresenceSourceConstraintSupport.explicitRows, RowsHold,
          RowFlowSchemes.Models, List.mem_cons, forall_eq_or_imp,
          RowFlowSchemes.Constraint.Holds] at *
      · exact ih
      · exact and_congr Iff.rfl ih

theorem declared_rows_models_exact (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (rows : Fin m → Row) :
    CommonRowTailInference.RowsHold (declareRows atoms good) rows ↔
      RowsHold (splitAtoms atoms).rows rows := by
  rw [CommonRowTailInference.rows_hold_iff, declared_rows_exact]
  exact explicit_rows_exact atoms rows

/-- Only the compiled constructor definitions and explicit row constraints
are passed to this solver. Subtype edges are deliberately outside this input. -/
def definitionProblem (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    CommonRowTailInference.Problem (compile atoms).size 0 m where
  rows := declareRows atoms good
  body := (compile atoms).definitions

def family (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    CommonRowTailInference.Scheme (compile atoms).size 0 m :=
  CommonRowTailInference.solve (definitionProblem atoms good)

theorem definition_models_exact (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty) :
    CommonRowTailInference.Models (definitionProblem atoms good) rows values ↔
      RowsHold (splitAtoms atoms).rows rows ∧ (compile atoms).Realizes rows values := by
  change CommonRowTailInference.RowsHold (declareRows atoms good) rows ∧
      (compile atoms).Realizes rows values ↔ _
  exact and_congr (declared_rows_models_exact atoms good rows) Iff.rfl

/-- Every choice of free row and value parameters satisfies the entire
compiled definition system and all explicit source rows. There is no `Models`
or other semantic side condition on the parameters. -/
theorem family_instantiates (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (rowParameters : Fin m → Row) (valueParameters : Fin (compile atoms).size → Ty) :
    RowsHold (splitAtoms atoms).rows ((family atoms good).instantiateRows rowParameters) ∧
      (compile atoms).Realizes ((family atoms good).instantiateRows rowParameters)
        ((family atoms good).instantiateValues rowParameters valueParameters) :=
  (definition_models_exact atoms good _ _).mp
    (CommonRowTailInference.solve_models (definitionProblem atoms good) rowParameters valueParameters)

/-- Every independent compiled model is recovered by the concrete family.
Rows, including rows shared by negative arrow inputs and positive outputs,
are equal, while every common value is demand equivalent. -/
theorem family_retracts (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty)
    (models : (compile atoms).Models rows values) :
    (family atoms good).instantiateRows rows = rows ∧
      ∀ index, Common.Equivalent ((family atoms good).instantiateValues rows values index)
        (values index) :=
  CommonRowTailInference.solve_retract (definitionProblem atoms good) rows values
    ((definition_models_exact atoms good rows values).mpr ⟨models.2.2, models.1⟩)

/-- All constructor witnesses and explicit row constraints have been
eliminated. The sole parameter restriction is the displayed, independent list
of remaining subtype edges. This is a bridge for the missing edge inspector,
not a claim that those parameters already form an unconstrained solved family. -/
theorem eliminate_definitions_exact (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty) :
    (compile atoms).Models rows values ↔
      ∃ rowParameters : Fin m → Row,
      ∃ valueParameters : Fin (compile atoms).size → Ty,
        (family atoms good).instantiateRows rowParameters = rows ∧
        (∀ index, Common.Equivalent
          ((family atoms good).instantiateValues rowParameters valueParameters index) (values index)) ∧
        EdgesHold (compile atoms).edges
          ((family atoms good).instantiateValues rowParameters valueParameters) := by
  constructor
  · intro models
    have same := family_retracts atoms good rows values models
    exact ⟨rows, values, same.1, same.2,
      (edgesHold_congr _ _ _ same.2).mpr models.2.1⟩
  · rintro ⟨rowParameters, valueParameters, rowSame, valueSame, edges⟩
    have equations := (CommonRowTailInference.joint_instances_exact
      (definitionProblem atoms good) rows values).mpr
        ⟨rowParameters, valueParameters, rowSame, valueSame⟩
    have original := (definition_models_exact atoms good rows values).mp equations
    exact ⟨original.2, (edgesHold_congr _ _ _ valueSame).mp edges, original.1⟩

end Yulang.CommonPresenceClauseFamily
