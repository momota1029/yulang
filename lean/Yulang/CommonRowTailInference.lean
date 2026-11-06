import Yulang.CommonPresenceTailRegular

/-!
# Simultaneous row and presence-tail families in the common carrier

The declared finite input syntax has arbitrary empty/variable/join row terms
on the left of inequalities and a variable or empty on the right. Type atoms
and record payloads are finite common syntax whose two arrow rows contain
those same row terms. Their row identities therefore remain shared with the
explicit row constraints. Same-depth value references may occur under record
tails, whole-default sources, masks, unions and intersections, with arbitrary
cycles. A symbolic layer and explicit record/default reference constructors
also share the same unknowns at guarded payload positions, including arrow
arguments. Both reference kinds are closed into one common regular block.

The output stores a finite row scheme and the symbolic constructor graph.
Instantiation substitutes arbitrary row parameters, then solves the resulting
presence-tail equations using arbitrary common value parameters. All original
row assignments are recovered by literal equality, using the antisymmetry of
the concrete common rows. No equivalence-transport law for rows inside a type
is added to the semantic model.

This is an exact simultaneous solver for this syntax. It is not an inspector
for arbitrary producer inequalities or a proof that every source-generated
problem has this shape.
-/

namespace Yulang.CommonRowTailInference

open Common (Ty Row)
open Inference (RowTerm)
open PresenceTailElimination (Mask)

variable {slots labels rowSlots : Nat}

/-- The right-hand support boundary is part of finite input syntax. -/
inductive Upper (rowSlots : Nat) where
  | var : Fin rowSlots → Upper rowSlots
  | empty : Upper rowSlots

def Upper.term : Upper rowSlots → RowTerm (Fin rowSlots)
  | .var index => .var index
  | .empty => .empty

structure RowConstraint (rowSlots : Nat) where
  lower : RowTerm (Fin rowSlots)
  upper : Upper rowSlots

def RowConstraint.erase (constraint : RowConstraint rowSlots) : RowFlowSchemes.Constraint rowSlots :=
  (constraint.lower, constraint.upper.term)

def rowProblem (constraints : List (RowConstraint rowSlots)) : RowFlowSchemes.Problem rowSlots :=
  constraints.map RowConstraint.erase

def RowsHold (constraints : List (RowConstraint rowSlots)) (rows : Fin rowSlots → Row) : Prop :=
  ∀ constraint ∈ constraints,
    Common.rowLe (RowFlowSchemes.eval Common.rowAlgebra rows constraint.lower)
      (RowFlowSchemes.eval Common.rowAlgebra rows constraint.upper.term)

theorem rows_hold_iff (constraints : List (RowConstraint rowSlots)) (rows : Fin rowSlots → Row) :
    RowsHold constraints rows ↔ RowFlowSchemes.Models Common.rowAlgebra (rowProblem constraints) rows := by
  simp only [RowsHold, RowFlowSchemes.Models, rowProblem, List.forall_mem_map,
    RowConstraint.erase, RowFlowSchemes.Constraint.Holds]
  rfl

theorem declared_rows_supported (constraints : List (RowConstraint rowSlots)) :
    RowFlowSchemes.supported (rowProblem constraints) = true := by
  apply List.all_eq_true.mpr
  intro constraint member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  cases original with
  | mk lower upper => cases upper <;> rfl

def rowScheme (constraints : List (RowConstraint rowSlots)) : RowFlowSchemes.Scheme rowSlots :=
  RowFlowSchemes.coalesce (RowFlowSchemes.flatten (rowProblem constraints))

theorem rowScheme_solved (constraints : List (RowConstraint rowSlots)) :
    RowFlowSchemes.solve (rowProblem constraints) = .solved (rowScheme constraints) :=
  (RowFlowSchemes.solve_solved_iff _ _).mpr ⟨rfl, declared_rows_supported constraints⟩

theorem rowScheme_models (constraints : List (RowConstraint rowSlots))
    (parameters : Fin rowSlots → Row) :
    RowsHold constraints (RowFlowSchemes.instantiate Common.rowAlgebra (rowScheme constraints) parameters) :=
  (rows_hold_iff constraints _).mpr
    (RowFlowSchemes.solve_instantiates_model Common.rowAlgebra _ _ (rowScheme_solved constraints) parameters)

theorem rowScheme_retract (constraints : List (RowConstraint rowSlots))
    (rows : Fin rowSlots → Row) (valid : RowsHold constraints rows) :
    RowFlowSchemes.instantiate Common.rowAlgebra (rowScheme constraints) rows = rows := by
  have flat := (RowFlowSchemes.flatten_models_iff Common.rowAlgebra _
    (declared_rows_supported constraints) rows).mpr ((rows_hold_iff constraints rows).mp valid)
  have same := RowFlowSchemes.expand_equivalent Common.rowAlgebra flat
  rw [rowScheme, RowFlowSchemes.instantiate_coalesce]
  funext index
  exact Common.rowLe_antisymm (same index).1 (same index).2

/-- Closed finite common constructor syntax with symbolic rows in every arrow. -/
abbrev TypeTerm (rowSlots : Nat) := CommonFinite.Ty (RowTerm (Fin rowSlots))

def TypeTerm.eval (rows : Fin rowSlots → Row) : TypeTerm rowSlots → Ty
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (eval rows first) (eval rows last)
  | .inter first last => .inter (eval rows first) (eval rows last)
  | .pair first last => Common.pair (eval rows first) (eval rows last)
  | .emptyRecord => Common.emptyRecord
  | .exactEmpty => Common.exactEmpty
  | .record label payload tail => Common.record label (eval rows payload) (eval rows tail)
  | .recordDefault label source fallback => Common.recordDefault label (eval rows source) (eval rows fallback)
  | .variant label payload => Common.variant label (eval rows payload)
  | .arrow arg input result output =>
      Common.arrow (eval rows arg) (RowFlowSchemes.eval Common.rowAlgebra rows input)
        (eval rows result) (RowFlowSchemes.eval Common.rowAlgebra rows output)
  | .mask hidden type => Common.mask hidden (eval rows type)

/-- Only row annotations are substituted; every guarded slot ID is retained. -/
def layerAtRows (rows : Fin rowSlots → Row) :
    CommonSyntax.Layer (RowTerm (Fin rowSlots)) (Fin slots) → CommonSyntax.Layer Row (Fin slots)
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (layerAtRows rows first) (layerAtRows rows last)
  | .inter first last => .inter (layerAtRows rows first) (layerAtRows rows last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => .record label payload (layerAtRows rows tail)
  | .recordDefault label source fallback => .recordDefault label (layerAtRows rows source) fallback
  | .variant label payload => .variant label payload
  | .arrow arg input result output => .arrow arg (RowFlowSchemes.eval Common.rowAlgebra rows input)
      result (RowFlowSchemes.eval Common.rowAlgebra rows output)
  | .mask hidden source => .mask hidden (layerAtRows rows source)

theorem TypeTerm.quote_external (type : TypeTerm rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) :
    CommonPresenceTailLayers.quoteLayer (CommonPresenceTailRegular.payload values)
      ((type.eval rows).map Sum.inr) = type.eval rows := by
  induction type <;>
    simp_all [eval, CommonPresenceTailLayers.quoteLayer, CommonPresenceTailRegular.payload,
      CommonSyntax.Layer.map, Function.comp_def, Common.pair, Common.emptyRecord,
      Common.exactEmpty, Common.record, Common.recordDefault, Common.variant,
      Common.arrow, Common.mask, CommonSyntax.graph_node]

inductive Body (slots labels rowSlots : Nat) where
  | atom : TypeTerm rowSlots → Body slots labels rowSlots
  | layer : CommonSyntax.Layer (RowTerm (Fin rowSlots)) (Fin slots) → Body slots labels rowSlots
  | ref : Fin slots → Body slots labels rowSlots
  | union : Body slots labels rowSlots → Body slots labels rowSlots → Body slots labels rowSlots
  | inter : Body slots labels rowSlots → Body slots labels rowSlots → Body slots labels rowSlots
  | mask : Mask labels → Body slots labels rowSlots → Body slots labels rowSlots
  | record : Nat → TypeTerm rowSlots → Body slots labels rowSlots → Body slots labels rowSlots
  | recordDefault : Nat → Body slots labels rowSlots → TypeTerm rowSlots → Body slots labels rowSlots
  | recordRef : Nat → Fin slots → Body slots labels rowSlots → Body slots labels rowSlots
  | recordDefaultRef : Nat → Body slots labels rowSlots → Fin slots → Body slots labels rowSlots

namespace Body

/-- Direct interpretation of the original symbolic constructor syntax. -/
def eval (rows : Fin rowSlots → Row) (values : Fin slots → Ty) : Body slots labels rowSlots → Ty
  | .atom type => type.eval rows
  | .layer layerSyntax => CommonPresenceTailLayers.quoteLayer values (layerAtRows rows layerSyntax)
  | .ref index => values index
  | .union first last => .union (eval rows values first) (eval rows values last)
  | .inter first last => .inter (eval rows values first) (eval rows values last)
  | .mask hidden body => Common.mask hidden.names (eval rows values body)
  | .record label payload tail => Common.record label (payload.eval rows) (eval rows values tail)
  | .recordDefault label source fallback => Common.recordDefault label (eval rows values source) (fallback.eval rows)
  | .recordRef label payload tail => Common.record label (values payload) (eval rows values tail)
  | .recordDefaultRef label source fallback => Common.recordDefault label (eval rows values source) (values fallback)

def atRows (rows : Fin rowSlots → Row) : Body slots labels rowSlots →
    CommonPresenceTailLayers.Body slots labels (CommonPresenceTailRegular.Payload slots)
  | .atom type => .atom ((type.eval rows).map Sum.inr)
  | .layer layerSyntax => .atom ((layerAtRows rows layerSyntax).map Sum.inl)
  | .ref index => .ref index
  | .union first last => .union (atRows rows first) (atRows rows last)
  | .inter first last => .inter (atRows rows first) (atRows rows last)
  | .mask hidden body => .mask hidden (atRows rows body)
  | .record label payload tail => .record label (.inr (.node (payload.eval rows))) (atRows rows tail)
  | .recordDefault label source fallback => .recordDefault label (atRows rows source) (.inr (.node (fallback.eval rows)))
  | .recordRef label payload tail => .record label (.inl payload) (atRows rows tail)
  | .recordDefaultRef label source fallback => .recordDefault label (atRows rows source) (.inl fallback)

@[simp] theorem eval_atRows (body : Body slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) :
    ((body.atRows rows).quote (CommonPresenceTailRegular.payload values)).eval values = body.eval rows values := by
  induction body
  case atom type => exact type.quote_external rows values
  all_goals
    simp_all [atRows, CommonPresenceTailLayers.Body.quote, CommonPresenceTailElimination.Body.eval,
      CommonPresenceTailLayers.quoteLayer_map, CommonPresenceTailRegular.payload,
      CommonSyntax.graph_node, Function.comp_def, eval]

end Body

structure Problem (slots labels rowSlots : Nat) where
  rows : List (RowConstraint rowSlots)
  body : Fin slots → Body slots labels rowSlots

def Problem.atRows (problem : Problem slots labels rowSlots) (rows : Fin rowSlots → Row) :
    CommonPresenceTailRegular.Graph slots labels := fun index => (problem.body index).atRows rows

def Models (problem : Problem slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) : Prop :=
  RowsHold problem.rows rows ∧
    ∀ index, Common.Equivalent ((problem.body index).eval rows values) (values index)

theorem models_iff_atRows (problem : Problem slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) :
    Models problem rows values ↔ RowsHold problem.rows rows ∧
      CommonPresenceTailRegular.Models (problem.atRows rows) values := by
  simp only [Models, CommonPresenceTailRegular.Models, Problem.atRows, Body.eval_atRows]

/-- Finite syntax only: no semantic row function or assumed model law is
stored in an inferred scheme. -/
structure Scheme (slots labels rowSlots : Nat) where
  rows : RowFlowSchemes.Scheme rowSlots
  body : Fin slots → Body slots labels rowSlots

def solve (problem : Problem slots labels rowSlots) : Scheme slots labels rowSlots :=
  ⟨rowScheme problem.rows, problem.body⟩

def Scheme.instantiateRows (scheme : Scheme slots labels rowSlots) (parameters : Fin rowSlots → Row) :
    Fin rowSlots → Row := RowFlowSchemes.instantiate Common.rowAlgebra scheme.rows parameters

def Scheme.instantiateValues (scheme : Scheme slots labels rowSlots)
    (rowParameters : Fin rowSlots → Row) (valueParameters : Fin slots → Ty) : Fin slots → Ty :=
  CommonPresenceTailRegular.solveBlock
    (fun index => (scheme.body index).atRows (scheme.instantiateRows rowParameters)) valueParameters

theorem solve_models (problem : Problem slots labels rowSlots)
    (rowParameters : Fin rowSlots → Row) (valueParameters : Fin slots → Ty) :
    Models problem ((solve problem).instantiateRows rowParameters)
      ((solve problem).instantiateValues rowParameters valueParameters) := by
  apply (models_iff_atRows problem _ _).mpr
  exact ⟨rowScheme_models problem.rows rowParameters,
    CommonPresenceTailRegular.solveBlock_models _ valueParameters⟩

/-- Retraction recovers rows literally, so every shared input/output arrow
row is preserved inside the simultaneous value family as well. -/
theorem solve_retract (problem : Problem slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) (valid : Models problem rows values) :
    (solve problem).instantiateRows rows = rows ∧
      ∀ index, Common.Equivalent ((solve problem).instantiateValues rows values index) (values index) := by
  have rowSame := rowScheme_retract problem.rows rows valid.1
  refine ⟨rowSame, ?_⟩
  change ∀ index, Common.Equivalent
    (CommonPresenceTailRegular.solveBlock
      (problem.atRows (RowFlowSchemes.instantiate Common.rowAlgebra (rowScheme problem.rows) rows)) values index)
    (values index)
  rw [rowSame]
  exact CommonPresenceTailRegular.solveBlock_retract _ values
    ((models_iff_atRows problem rows values).mp valid).2

/-- All inputs in the declared syntax, all independent row/value solutions,
and all free parameter assignments are quantified without support, success,
closedness, finite-fuel or residual-model premises. -/
theorem joint_instances_exact (problem : Problem slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) :
    Models problem rows values ↔
      ∃ rowParameters : Fin rowSlots → Row, ∃ valueParameters : Fin slots → Ty,
        (solve problem).instantiateRows rowParameters = rows ∧
          ∀ index, Common.Equivalent
            ((solve problem).instantiateValues rowParameters valueParameters index) (values index) := by
  constructor
  · intro valid
    exact ⟨rows, values, solve_retract problem rows values valid⟩
  · rintro ⟨rowParameters, valueParameters, rowSame, valueSame⟩
    apply (models_iff_atRows problem rows values).mpr
    constructor
    · have valid := rowScheme_models problem.rows rowParameters
      change RowsHold problem.rows ((solve problem).instantiateRows rowParameters) at valid
      simpa only [rowSame] using valid
    · apply (CommonPresenceTailRegular.guarded_solved_instances_exact (problem.atRows rows) values).mpr
      refine ⟨valueParameters, ?_⟩
      change ∀ index, Common.Equivalent
        (CommonPresenceTailRegular.solveBlock
          (problem.atRows ((solve problem).instantiateRows rowParameters)) valueParameters index)
        (values index) at valueSame
      simpa only [rowSame] using valueSame

/-- Unconstrained row identities stay free, even when supplied an infinite
nonempty occurrence set; no row is implicitly replaced with empty. -/
theorem unconstrained_rows_exact (parameters : Fin rowSlots → Row) :
    RowFlowSchemes.instantiate Common.rowAlgebra (rowScheme []) parameters = parameters := by
  apply rowScheme_retract [] parameters
  intro constraint impossible
  cases impossible

end Yulang.CommonRowTailInference
