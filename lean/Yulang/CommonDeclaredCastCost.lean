import Yulang.CommonDeclaredCastCostGraph

/-!
# Data-independent work bounds for finite structural cast plans

The computed budget counts structural visits/rebuilding, wrapper allocation,
and calls to an existing leaf cast. It does not count execution inside a
user-defined cast or the wrapped function. Product parts are visited in order;
a variant visits only its selected branch. Function conversion allocates a
wrapper without traversing its argument/result plans. One subsequent call
uses the separately computed argument and result budgets.

This is an operational cost kernel for finite plans. The source-declaration
variance algorithm must still prove that the plans it permits pass `check`.
-/

namespace Yulang.CommonDeclaredCastCost

open CommonDeclaredCastCostGraph

def budget (plan : Plan n) (accepted : check plan = true) (node : Fin n) : Nat :=
  1 + ((plan node).immediate.attach.map fun child => budget plan accepted child.val).sum
termination_by rank plan node
decreasing_by exact rank_decreases plan accepted node child.val child.property

theorem budget_eq (plan : Plan n) (accepted : check plan = true) (node : Fin n) :
    budget plan accepted node = 1 + ((plan node).immediate.map (budget plan accepted)).sum := by
  rw [budget]
  simp

mutual
  /-- Cost of one actual immediate conversion. A leaf cast is one call;
  function bodies and user cast internals are outside this accounting. -/
  inductive Run (plan : Plan n) : Fin n → Nat → Prop where
    | keep : plan node = .keep → Run plan node 1
    | leaf : plan node = .leaf → Run plan node 1
    | product : plan node = .product parts → Runs plan parts costs →
        Run plan node (1 + costs.sum)
    | variant : plan node = .variant branches → child ∈ branches → Run plan child cost →
        Run plan node (1 + cost)
    | nominal : plan node = .nominal child → Run plan child cost → Run plan node (1 + cost)
    | function : plan node = .function argument result → Run plan node 1
  /-- Retains order, multiplicity and separate costs of every product part. -/
  inductive Runs (plan : Plan n) : List (Fin n) → List Nat → Prop where
    | nil : Runs plan [] []
    | cons : Run plan node cost → Runs plan nodes costs →
        Runs plan (node :: nodes) (cost :: costs)
end

private theorem member_sum_bound (f : α → Nat) (xs : List α) (x : α) (member : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (ih later) (Nat.le_add_left _ _)

/-- Every execution has a bound computed solely from the finite plan. -/
theorem run_bound (plan : Plan n) (accepted : check plan = true)
    (execution : Run plan node cost) : cost ≤ budget plan accepted node := by
  induction execution using Run.rec
      (motive_2 := fun nodes costs _ => costs.sum ≤ (nodes.map (budget plan accepted)).sum) with
  | keep shape => simp [budget_eq, shape, Node.immediate]
  | leaf shape => simp [budget_eq, shape, Node.immediate]
  | product shape _ ih =>
      rw [budget_eq, shape]
      exact Nat.add_le_add_left ih 1
  | variant shape member _ ih =>
      rw [budget_eq, shape]
      exact Nat.add_le_add_left (Nat.le_trans ih (member_sum_bound _ _ _ member)) 1
  | nominal shape _ ih =>
      simpa [budget_eq, shape, Node.immediate] using Nat.add_le_add_left ih 1
  | function shape => simp [budget_eq, shape, Node.immediate]
  | nil => exact Nat.le_refl _
  | cons _ _ first rest => exact Nat.add_le_add first rest

theorem runs_bound (plan : Plan n) (accepted : check plan = true)
    (execution : Runs plan nodes costs) : costs.sum ≤ (nodes.map (budget plan accepted)).sum := by
  induction nodes generalizing costs with
  | nil => cases execution; exact Nat.le_refl _
  | cons node nodes ih =>
      cases execution with
      | cons first rest => exact Nat.add_le_add (run_bound plan accepted first) (ih rest)

/-- Wrapper construction does no work in either recursive conversion plan. -/
theorem wrapper_creation (plan : Plan n) (accepted : check plan = true)
    (node argument result : Fin n) (shape : plan node = .function argument result) :
    budget plan accepted node = 1 ∧ Run plan node 1 := by
  exact ⟨by simp [budget_eq, shape, Node.immediate], .function shape⟩

/-- One invocation converts its input, calls the original function once,
then converts its result. The body's own cost is deliberately not counted. -/
inductive Invocation (plan : Plan n) : Fin n → Nat → Prop where
  | call : plan wrapper = .function argument result →
      Run plan argument before → Run plan result after →
      Invocation plan wrapper (before + 1 + after)

def callBudget (plan : Plan n) (accepted : check plan = true) (argument result : Fin n) : Nat :=
  budget plan accepted argument + 1 + budget plan accepted result

theorem invocation_bound (plan : Plan n) (accepted : check plan = true)
    (wrapper argument result : Fin n) (shape : plan wrapper = .function argument result)
    (execution : Invocation plan wrapper cost) : cost ≤ callBudget plan accepted argument result := by
  cases execution with
  | call actual before after =>
      have same := Node.function.inj (actual.symm.trans shape)
      rcases same with ⟨rfl, rfl⟩
      exact Nat.add_le_add (Nat.add_le_add_right (run_bound plan accepted before) 1)
        (run_bound plan accepted after)

end Yulang.CommonDeclaredCastCost
