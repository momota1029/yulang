import Yulang.CommonDeclaredCastCost

/-!
# Executing finite structural cast plans on actual finite values

This evaluator uses the computed immediate-plan rank. Product fields retain
their order and multiplicity, a variant tag selects one original branch, and
function conversion allocates a wrapper without evaluating either recursive
conversion plan. A shape or arity mismatch fails. A leaf primitive is called
once; its own implementation cost is outside the structural accounting.

This is an operational producer for the cost kernel, not a source/target
typing theorem. The declaration-directed typed-plan producer remains a
separate obligation.
-/

namespace Yulang.CommonDeclaredCastEvaluation

open CommonDeclaredCastCostGraph
open CommonDeclaredCastCost (Run Runs budget)

/-- Variant tags index the finite branch list of the structural plan.
Function tokens are opaque. A wrapper retains the original callable value. -/
inductive Value (n : Nat) where
  | atom (token : Nat)
  | product (parts : List (Value n))
  | variant (tag : Nat) (payload : Value n)
  | nominal (payload : Value n)
  | function (token : Nat)
  | wrapper (node : Fin n) (original : Value n)
  deriving Repr

def Value.callable : Value n → Bool
  | .function _ | .wrapper _ _ => true
  | _ => false

/-- Only the existing leaf operation is abstracted. No rank, success,
semantic compatibility or evaluation evidence is supplied by this parameter. -/
abbrev Leaf (n : Nat) := Fin n → Value n → Option (Value n)

structure Result (plan : Plan n) (node : Fin n) where
  value : Value n
  cost : Nat
  execution : Run plan node cost

structure Results (plan : Plan n) (nodes : List (Fin n)) where
  values : List (Value n)
  costs : List Nat
  executions : Runs plan nodes costs

/-- This helper only sequences the actual child evaluator supplied by
`evaluate`. Its recursion is on the original finite product-part list. -/
def evaluateParts (plan : Plan n) (nodes : List (Fin n)) (inputs : List (Value n))
    (evaluateChild : ∀ node, node ∈ nodes → Value n → Option (Result plan node)) :
    Option (Results plan nodes) :=
  match nodes, inputs with
  | [], [] => some ⟨[], [], .nil⟩
  | node :: rest, input :: remaining => do
      let first ← evaluateChild node (by simp) input
      let last ← evaluateParts plan rest remaining
        (fun child member => evaluateChild child (List.mem_cons_of_mem node member))
      pure ⟨first.value :: last.values, first.cost :: last.costs,
        .cons first.execution last.executions⟩
  | _, _ => none

/-- All recursive calls are actual immediate edges of the checked plan.
The proof fields are erased; values and costs are computed by the evaluator. -/
def evaluate (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n)
    (node : Fin n) (input : Value n) : Option (Result plan node) :=
  match shape : plan node with
  | .keep => some ⟨input, 1, .keep shape⟩
  | .leaf => (leaf node input).map fun value => ⟨value, 1, .leaf shape⟩
  | .product parts =>
      match input with
      | .product inputs =>
          (evaluateParts plan parts inputs
            (fun child _member value => evaluate plan accepted leaf child value)).map fun output =>
              ⟨.product output.values, 1 + output.costs.sum, .product shape output.executions⟩
      | _ => none
  | .variant branches =>
      match input with
      | .variant tag payload =>
          match branches.attach[tag]? with
          | none => none
          | some child =>
              (evaluate plan accepted leaf child.val payload).map fun output =>
                ⟨.variant tag output.value, 1 + output.cost,
                  .variant shape child.property output.execution⟩
      | _ => none
  | .nominal child =>
      match input with
      | .nominal payload =>
          (evaluate plan accepted leaf child payload).map fun output =>
            ⟨.nominal output.value, 1 + output.cost, .nominal shape output.execution⟩
      | _ => none
  | .function _ _ =>
      if input.callable then some ⟨.wrapper node input, 1, .function shape⟩ else none
termination_by rank plan node
decreasing_by
  all_goals apply rank_decreases plan accepted node
  · simpa [shape, Node.immediate] using _member
  · simpa [shape, Node.immediate] using child.property
  · simp [shape, Node.immediate]

def execute (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n)
    (node : Fin n) (input : Value n) : Option (Value n × Nat) :=
  (evaluate plan accepted leaf node input).map fun result => (result.value, result.cost)

/-- Every actual successful computation produces the independently defined
operational cost derivation; no successful run is an evaluator input. -/
theorem execute_run (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n)
    (node : Fin n) (input output : Value n) (cost : Nat)
    (returned : execute plan accepted leaf node input = some (output, cost)) :
    Run plan node cost := by
  obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp returned
  have equalCost : result.cost = cost := congrArg Prod.snd same
  rw [← equalCost]
  exact result.execution

/-- The bound contains the plan alone, and is uniform in the original
finite value, the output, and the implementation of the leaf primitive. -/
theorem execute_bound (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n)
    (node : Fin n) (input output : Value n) (cost : Nat)
    (returned : execute plan accepted leaf node input = some (output, cost)) :
    cost ≤ budget plan accepted node :=
  CommonDeclaredCastCost.run_bound plan accepted
    (execute_run plan accepted leaf node input output cost returned)

/-- A callable input is wrapped immediately; neither argument nor result
conversion is executed during this allocation. Other value shapes fail. -/
theorem execute_function (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n)
    (node argument result : Fin n) (shape : plan node = .function argument result)
    (input : Value n) :
    execute plan accepted leaf node input =
      if input.callable then some (.wrapper node input, 1) else none := by
  unfold execute
  rw [evaluate]
  split <;> simp_all

/-- The original callable is opaque at this layer. Calling it once is one
unit, excluding all execution inside that callable, as in `Invocation`. -/
abbrev Body (n : Nat) := Value n → Value n → Option (Value n)

structure InvocationResult (plan : Plan n) (node : Fin n) where
  value : Value n
  cost : Nat
  execution : CommonDeclaredCastCost.Invocation plan node cost

/-- Convert the actual argument, call the retained original callable once,
then convert the returned value. No result is invented for a failed step. -/
def invokeWrapper (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n) (body : Body n)
    (node : Fin n) (original input : Value n) : Option (InvocationResult plan node) :=
  match shape : plan node with
  | .function argument result =>
      if original.callable then do
        let before ← evaluate plan accepted leaf argument input
        let middle ← body original before.value
        let after ← evaluate plan accepted leaf result middle
        pure ⟨after.value, before.cost + 1 + after.cost,
          .call shape before.execution after.execution⟩
      else none
  | _ => none

def invoke (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n) (body : Body n)
    (callable input : Value n) : Option (Value n × Nat) :=
  match callable with
  | .wrapper node original =>
      (invokeWrapper plan accepted leaf body node original input).map fun result =>
        (result.value, result.cost)
  | _ => none

theorem invoke_run (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n) (body : Body n)
    (node : Fin n) (original input output : Value n) (cost : Nat)
    (returned : invoke plan accepted leaf body (.wrapper node original) input = some (output, cost)) :
    CommonDeclaredCastCost.Invocation plan node cost := by
  obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp returned
  have equalCost : result.cost = cost := congrArg Prod.snd same
  rw [← equalCost]
  exact result.execution

def invocationBudget (plan : Plan n) (accepted : check plan = true) (node : Fin n) : Nat :=
  match plan node with
  | .function argument result => CommonDeclaredCastCost.callBudget plan accepted argument result
  | _ => 0

/-- Every successful call has the one-call plan bound. The function-node
shape is checked inside the evaluator, rather than supplied as a premise. -/
theorem invoke_bound (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n) (body : Body n)
    (node : Fin n) (original input output : Value n) (cost : Nat)
    (returned : invoke plan accepted leaf body (.wrapper node original) input = some (output, cost)) :
    cost ≤ invocationBudget plan accepted node := by
  have execution := invoke_run plan accepted leaf body node original input output cost returned
  cases execution with
  | call shape before after =>
      simp only [invocationBudget, shape]
      exact CommonDeclaredCastCost.invocation_bound plan accepted node _ _ shape
        (.call shape before after)

/-- Successful computation recovers both the actual wrapper reference and
the plan shape, without assuming either in the public call. -/
theorem invoke_shape (plan : Plan n) (accepted : check plan = true) (leaf : Leaf n) (body : Body n)
    (callable input output : Value n) (cost : Nat)
    (returned : invoke plan accepted leaf body callable input = some (output, cost)) :
    ∃ node original argument result, callable = .wrapper node original ∧
      plan node = .function argument result ∧ cost ≤ invocationBudget plan accepted node := by
  cases callable with
  | wrapper node original =>
      have execution := invoke_run plan accepted leaf body node original input output cost returned
      cases execution with
      | @call argument result before after shape _ _ =>
          exact ⟨node, original, argument, result, rfl, shape,
            invoke_bound plan accepted leaf body node original input output (before + 1 + after) returned⟩
  | _ => simp [invoke] at returned

end Yulang.CommonDeclaredCastEvaluation
