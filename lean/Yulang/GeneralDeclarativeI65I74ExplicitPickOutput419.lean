import Yulang.GeneralDeclarativeI65I73UnifiedEntry408
import Yulang.GeneralDeclarativeWitnessLiteral349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open Check408 (TypeWire Write)
open Checker408 (Problem)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)

mutual
/-- Compare the literal typed tree, including ordered children and all payloads. -/
def eqWire : TypeWire → TypeWire → Bool
  | .node a as xs, .node b bs ys => decide (a = b ∧ as = bs) && eqWires xs ys
termination_by x _ => sizeOf x

def eqWires : List TypeWire → List TypeWire → Bool
  | [], [] => true
  | x::xs, y::ys => eqWire x y && eqWires xs ys
  | _, _ => false
termination_by xs _ => sizeOf xs
end

mutual
theorem eq_wire419 (x y : TypeWire) : eqWire x y = true ↔ x = y := by
  cases x with | node a as xs =>
    cases y with | node b bs ys =>
      rw [eqWire.eq_def]
      simp only [Bool.and_eq_true, decide_eq_true_eq, eq_wires419 xs ys, TypeWire.node.injEq,
        and_assoc]
termination_by sizeOf x

theorem eq_wires419 (xs ys : List TypeWire) : eqWires xs ys = true ↔ xs = ys := by
  cases xs <;> cases ys
  case cons.cons x xs y ys =>
    rw [eqWires.eq_def]
    simp only [Bool.and_eq_true, eq_wire419 x y, eq_wires419 xs ys, List.cons.injEq]
  all_goals simp [eqWires.eq_def]
termination_by sizeOf xs
end

def eqWrite (a b : Write) : Bool :=
  decide (a.occurrence = b.occurrence ∧ a.declarationOrdinal = b.declarationOrdinal ∧
    a.outputOrdinal = b.outputOrdinal ∧ a.target.name = b.target.name ∧
    a.target.target = b.target.target ∧ a.body = b.body) && eqWire a.typedRhs b.typedRhs

theorem eq_write419 (a b : Write) : eqWrite a b = true ↔ a = b := by
  cases a with | mk ao ad ai atg ab ax =>
    cases b with | mk bo bd bi btg bb bx =>
      cases atg
      cases btg
      simp only [eqWrite, Bool.and_eq_true, decide_eq_true_eq, eq_wire419, Write.mk.injEq,
        GeneralSourceState.Output.mk.injEq, and_assoc]

/-- A checked equation ordinal carries original typed syntax and membership
in the same state. The ordinary expression is only a retention witness. -/
structure RetainedOutput (p : Problem) (f : AuthoredBodyFrame393 p.state.core p.root)
    (i : Fin p.root.demand.outputs.length) where
  output : NamedMixedOutput401 p.state.b6 f i
  expr : Expr
  code : fixedValueCode403 output.rhs = some expr
  atRow : ⟨p.root.demand.outputs[i].target,expr⟩ ∈ p.state.core.current.ordinary.equations

def RetainedOutput.write {p f i} (out : RetainedOutput p f i) : Write :=
  ⟨p.root.occurrence,f.ordinal,i.val,p.root.demand.outputs[i],out.output.body,
    Check408.encodeRhs out.output.rhs⟩

/-- Consult actual source and B6 State, not a proposed RHS from the witness.
The equation ordinal cannot set the target, declaration, body, or B6 plan. -/
def replayOutput (p : Problem) (f : AuthoredBodyFrame393 p.state.core p.root)
    (checked : GeneralDeclarations.Checked (authoredRegistry p.state.core.current))
    (i : Fin p.root.demand.outputs.length) (pos : Nat) : Option (RetainedOutput p f i) := do
  let roles := (authoredRegistry p.state.core.current).roles
  let supplied := checked.2 f.decl (List.mem_of_getElem? f.authored)
  match found : lookup roles f.decl p.root.demand.outputs[i].name with
  | none => none
  | some body =>
    match input : p.state.b6.read p.root f.ordinal i body with
    | none => none
    | some plan =>
      match formed : substituteMixedRhs401 (instantiateName401 (f.slots body)) plan with
      | none => none
      | some rhs =>
        match repr : fixedValueCode403 rhs with
        | none => none
        | some expr =>
          match row : p.state.core.current.ordinary.equations[pos]? with
          | none => none
          | some e =>
            if same : (e.left == p.root.demand.outputs[i].target) && eqExpr e.right expr then
              have pair := GeneralDeclarativeWitnessProblem349.splitAnd same
              have exactRow : e = (⟨p.root.demand.outputs[i].target,expr⟩ : Equation) := by
                cases e
                congr
                · exact beq_iff_eq.mp pair.1
                · exact (eq_expr _ _).mp pair.2
              some ⟨⟨body,(lookup_exact _ _ supplied.identified.2.2.1 _ _).mp found,
                plan,input,rhs,formed⟩,expr,repr,exactRow ▸ List.mem_of_getElem? row⟩
            else none

theorem replay_output_has_exact_source_and_row419 {p f checked i pos out}
    (_ : replayOutput p f checked i pos = some out) :
    p.state.b6.read p.root f.ordinal i out.output.body = some out.output.plan ∧
      out.write.occurrence = p.root.occurrence ∧ out.write.declarationOrdinal = f.ordinal ∧
      out.write.outputOrdinal = i.val ∧ out.write.target = p.root.demand.outputs[i] ∧
      ⟨p.root.demand.outputs[i].target,out.expr⟩ ∈ p.state.core.current.ordinary.equations :=
  ⟨out.output.originalTyped,rfl,rfl,rfl,rfl,out.atRow⟩

def exactlyOneOutput (p : Problem) (h : p.root.demand.outputs.length = 1) :
    Fin p.root.demand.outputs.length := ⟨0,by omega⟩

theorem one_output_is_zero419 (p : Problem) (h : p.root.demand.outputs.length = 1)
    (i : Fin p.root.demand.outputs.length) : i = exactlyOneOutput p h := by
  apply Fin.ext
  have bound := i.isLt
  change i.val = 0
  omega

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
