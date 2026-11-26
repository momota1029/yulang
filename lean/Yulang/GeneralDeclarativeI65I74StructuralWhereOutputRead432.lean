import Yulang.GeneralDeclarativeI65I74StructuralWhereAssociatedLocal432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65
open GeneralDeclarations (DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonDeclaredNominalInspection (Parameter)
open CommonRecursiveNominalIntervals (effectiveParameter)

/-- Exact read from the original typed atlas plan. It inspects the
typed constructor and argument occurrence, without guessing mode
from a printable key or from evaluation of the result. -/
structure ReadInvariantUnary432 {s : GeneralDeclarativeI65.State} {ctor binder : Nat}
    (plan : B6MixedRhs401 s false (.app ctor [.var binder])) where
  param : Parameter
  use : Use s.current.environment ctor 1
  mode : names use.mode 1 = some [param]
  table : s.modes[ctor]? = some [param]
  kind : param.kind = .value
  invariant : (effectiveParameter false param).variance = .invariant
  exactPlan : HEq plan (invariantUnaryValuePlan432 ctor binder param use mode table kind invariant)

def readInvariantUnary432 {s : GeneralDeclarativeI65.State} {ctor binder : Nat}
    (plan : B6MixedRhs401 s false (.app ctor [.var binder])) :
    Option (ReadInvariantUnary432 plan) :=
  match plan with
  | .declaredApp _ use mode table (.cons (.valueInterval _ kind invariant slot) .nil) =>
    match slot with
    | () => some ⟨_,use,mode,table,kind,invariant,HEq.rfl⟩
  | _ => none

structure ReadOriginalOutput432 (s : I72.State) {q : Request}
    (frame : AuthoredBodyFrame393 s.core q) (i : Fin q.demand.outputs.length) where
  output : NamedMixedOutput401 s.b6 frame i
  code : Expr
  valueCode : fixedValueCode403 output.rhs = some code
  rowOrdinal : Nat
  row : s.core.current.ordinary.equations[rowOrdinal]? =
    some ⟨q.demand.outputs[i].target,code⟩

/-- Given the independently checked original frame, read the unique
literal body, original occurrence/ordinal-indexed B6 plan, substitute
its lexical slots, and verify this exact already-retained row.
Missing mode/plan/row is unsupported: this function never creates a
target or diagnoses an input from a failed read. -/
def readOriginalOutput432 (s : I72.State) {q : Request}
    (frame : AuthoredBodyFrame393 s.core q)
    (checked : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles frame.decl)
    (i : Fin q.demand.outputs.length) (outRow : Nat) :
    Option (ReadOriginalOutput432 s frame i) := do
  let registry := authoredRegistry s.core.current
  let name := q.demand.outputs[i].name
  match exactBody : lookup registry.roles frame.decl name with
  | none => none
  | some body =>
    match exactPlan : s.b6.read q frame.ordinal i body with
    | none => none
    | some plan =>
      match formed : substituteMixedRhs401 (instantiateName401 (frame.slots body)) plan with
      | none => none
      | some rhs =>
        match encoded : fixedValueCode403 rhs with
        | none => none
        | some code =>
          match atRow : s.core.current.ordinary.equations[outRow]? with
          | none => none
          | some row =>
            if target : row.left = q.demand.outputs[i].target then
              if raw : eqExpr row.right code = true then
                let source := (lookup_exact _ _ checked.identified.2.2.1 _ _).mp exactBody
                let out : NamedMixedOutput401 s.b6 frame i :=
                  ⟨body,source,plan,exactPlan,rhs,formed⟩
                have equality : row = ⟨q.demand.outputs[i].target,code⟩ := by
                  cases row
                  cases target
                  exact congrArg (Equation.mk _) ((eq_expr ..).mp raw)
                some ⟨out,code,encoded,outRow,atRow.trans (congrArg some equality)⟩
              else none
            else none

theorem read_original_output_keeps_actual_B6_and_literal_fixed_row432
    {s : I72.State} {q : Request} {frame : AuthoredBodyFrame393 s.core q}
    {i : Fin q.demand.outputs.length} (a : ReadOriginalOutput432 s frame i) :
    s.b6.read q frame.ordinal i a.output.body = some a.output.plan ∧
    a.output.receipt.occurrence = q.occurrence ∧
    a.output.receipt.outputOrdinal = i.val ∧ a.output.receipt.original = q.demand.outputs[i] ∧
    ⟨q.demand.outputs[i].target,a.code⟩ ∈ s.core.current.ordinary.equations :=
  ⟨a.output.originalTyped,rfl,rfl,rfl,List.mem_of_getElem? a.row⟩

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
