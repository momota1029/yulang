import Yulang.EvaluationOrder
import Yulang.RecursiveInference

/-!
# One resolved block, both type and initialization checks

The dependency syntax is translated structurally to the inference core. Global
declaration indices are shifted past lambda-bound locals, and a finite scope
check excludes local indices that could otherwise capture a global member.
The translation preserves the syntactic value restriction exactly.

`generate` checks those same bodies as one unannotated recursive block, and
conjoins the separately decidable initialization-order policy. Thus a computed
cycle is rejected even if the simultaneous type constraints have a solution.
There is no premise asserting successful type inference or absence of a cycle.

This is the dependency syntax fragment (unit literal, local/global reference,
lambda, application, pair, branch). Module statements contribute dependency
checks here; their result typing belongs to the subsequent expression checker.
This is not source name resolution or an operational callback-flow theorem.
-/

namespace Yulang.Initialization

open Inference
open RecursiveInference

def wellScoped : EvaluationOrder.Expr n → Nat → Bool
  | .bound index, depth => decide (index < depth)
  | .reference _, _ | .lit, _ => true
  | .lam body, depth => wellScoped body (depth + 1)
  | .app fn arg, depth | .pair fn arg, depth => wellScoped fn depth && wellScoped arg depth
  | .branch condition yes no, depth =>
      wellScoped condition depth && wellScoped yes depth && wellScoped no depth

def toCore : EvaluationOrder.Expr n → Nat → Inference.Expr
  | .bound index, _ => .var index
  | .reference name, depth => .var (depth + name.val)
  | .lit, _ => .lit .unit
  | .lam body, depth => .lam (toCore body (depth + 1))
  | .app fn arg, depth => .app (toCore fn depth) (toCore arg depth)
  | .pair left right, depth => .pair (toCore left depth) (toCore right depth)
  | .branch condition yes no, depth =>
      .branch (toCore condition depth) (toCore yes depth) (toCore no depth)

theorem value_restriction_agrees (expression : EvaluationOrder.Expr n) (depth : Nat) :
    (toCore expression depth).isValue = expression.isValue := by
  induction expression generalizing depth with
  | bound _ | reference _ | lit | lam _ _ | app _ _ _ _ | branch _ _ _ _ _ _ => rfl
  | pair left right ihl ihr => simp [toCore, Expr.isValue, EvaluationOrder.Expr.isValue, ihl, ihr]

theorem local_index_cannot_capture_member (index depth : Nat)
    (accepted : wellScoped (EvaluationOrder.Expr.bound index : EvaluationOrder.Expr n) depth = true)
    (member : Fin n) : index ≠ depth + member.val := by
  have less : index < depth := of_decide_eq_true accepted
  omega

def allScoped (program : EvaluationOrder.Program n)
    (statements : List (EvaluationOrder.Statement n)) : Bool :=
  (List.finRange n).all (fun name => wellScoped (program.body name) 0) &&
    statements.all (fun statement => wellScoped statement.expression 0)

def bodies (program : EvaluationOrder.Program n) : Fin n → Inference.Expr :=
  fun name => toCore (program.body name) 0

/-- The order checker and type checker classify the same binding as computed. -/
theorem computed_agrees (program : EvaluationOrder.Program n) (name : Fin n) :
    program.computed name = !(bodies program name).isValue := by
  simp [EvaluationOrder.Program.computed, bodies, value_restriction_agrees]

def generate (Γ : SchemeEnv α) (program : EvaluationOrder.Program n)
    (statements : List (EvaluationOrder.Statement n)) : Constraint α :=
  if allScoped program statements && EvaluationOrder.check program statements then
    inferUnannotatedSCC Γ (bodies program)
  else .core .bot

/-- The type judgement contains no occurrence of the generated constraint. -/
def Checked (m : Model) (Γ : List (Binding m)) (ρ : α → Comp m)
    (program : EvaluationOrder.Program n) (statements : List (EvaluationOrder.Statement n)) : Prop :=
  allScoped program statements = true ∧ EvaluationOrder.Ordered program statements ∧
    ∃ slots, SCCTyping m Γ (manyEnv ρ slots) (unannotatedMembers (bodies program))

theorem generate_exact (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (environment : EnvRel m ρ sΓ Γ)
    (program : EvaluationOrder.Program n) (statements : List (EvaluationOrder.Statement n)) :
    (generate sΓ program statements).Holds m ρ ↔ Checked m Γ ρ program statements := by
  have typeExact := inferUnannotatedSCC_exact m ρ sΓ Γ environment (bodies program)
  cases scopeCheck : allScoped program statements <;>
    cases orderCheck : EvaluationOrder.check program statements <;>
    simp [generate, scopeCheck, orderCheck, Constraint.Holds, Formula.Holds, Checked,
      ← EvaluationOrder.check_exact, typeExact]

theorem order_failure_rejects (m : Model) (ρ : α → Comp m) (Γ : SchemeEnv α)
    (program : EvaluationOrder.Program n) (statements : List (EvaluationOrder.Statement n))
    (rejected : EvaluationOrder.check program statements = false) :
    ¬ (generate Γ program statements).Holds m ρ := by
  simp [generate, rejected, Constraint.Holds, Formula.Holds]

theorem computed_cycle_rejects_generated_constraints (m : Model) (ρ : α → Comp m)
    (Γ : SchemeEnv α) (program : EvaluationOrder.Program n)
    (statements : List (EvaluationOrder.Statement n)) (name : Fin n)
    (computed : program.computed name = true)
    (cycle : EvaluationOrder.Depends program (program.body name) name) :
    ¬ (generate Γ program statements).Holds m ρ :=
  order_failure_rejects m ρ Γ program statements
    (EvaluationOrder.computed_self_dependency_rejected program statements name computed cycle)

theorem generated_initializers_use_earlier_values (m : Model) (ρ : α → Comp m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (environment : EnvRel m ρ sΓ Γ)
    (program : EvaluationOrder.Program n) (statements : List (EvaluationOrder.Statement n))
    (solution : (generate sΓ program statements).Holds m ρ) (source target : Fin n)
    (sourceComputed : program.computed source = true)
    (targetComputed : program.computed target = true)
    (dependency : EvaluationOrder.Depends program (program.body source) target) :
    program.position target < program.position source := by
  have checked := (generate_exact m ρ sΓ Γ environment program statements).mp solution
  exact checked.2.1.1 source sourceComputed target dependency targetComputed

namespace Examples

theorem value_cycle_is_scoped : allScoped EvaluationOrder.Examples.valueCycle [] = true := by
  decide

theorem value_cycle_has_no_generated_solution (m : Model) (ρ : α → Comp m) (Γ : SchemeEnv α) :
    ¬ (generate Γ EvaluationOrder.Examples.valueCycle []).Holds m ρ :=
  order_failure_rejects m ρ Γ _ _ EvaluationOrder.Examples.computed_cycle_rejected

theorem forward_function_cycle_is_scoped :
    allScoped EvaluationOrder.Examples.functionCycle [] = true := by decide

end Examples
end Yulang.Initialization
