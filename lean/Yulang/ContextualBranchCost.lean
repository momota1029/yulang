import Yulang.ContextualBranchSolver

/-!
# Syntax-size bounds for actual contextual branch enumeration

The bound counts the concrete lists produced by `Formula.branches` and
`solve`, including duplicates. If the input has `D` disjunction nodes and
`E` edge leaves, enumeration produces at most `2^D` branches, each with at
most `E` edges. Every retained cache has at most `n*n` edges, so their total
stored size is at most `2^D * (n*n)`.

These are structural bounds on the implemented enumeration and solver
outputs. They do not assert polynomial DNF expansion, bound the internal
runtime of row comparison, or replace a cost model for saturation itself.
-/

namespace Yulang.ContextualBranchCost

open ContextualBranchSolver

universe u
variable {n : Nat} {Row : Type u}

def eitherNodes : Formula n → Nat
  | .truth | .falsity | .edge _ => 0
  | .both left right => eitherNodes left + eitherNodes right
  | .either left right => eitherNodes left + eitherNodes right + 1

def edgeLeaves : Formula n → Nat
  | .truth | .falsity => 0
  | .edge _ => 1
  | .both left right | .either left right => edgeLeaves left + edgeLeaves right

private theorem sum_map_constant (items : List α) (constant : Nat) :
    (items.map fun _ => constant).sum = items.length * constant := by
  induction items with
  | nil => simp
  | cons item rest ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem sum_map_le_length_mul (items : List α) (measure : α → Nat)
    (capacity : Nat) (bound : ∀ item ∈ items, measure item ≤ capacity) :
    (items.map measure).sum ≤ items.length * capacity := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have first := bound item List.mem_cons_self
      have last := ih (fun candidate member => bound candidate (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

private theorem one_le_two_pow (exponent : Nat) : 1 ≤ 2 ^ exponent := by
  induction exponent with
  | zero => decide
  | succ exponent ih => simp only [Nat.pow_succ]; omega

/-- Conjunction really enumerates the Cartesian product, including every
repeated branch. This exact count precedes the coarser exponential bound. -/
theorem branches_both_length (left right : Formula n) :
    (Formula.both left right).branches.length = left.branches.length * right.branches.length := by
  simp only [Formula.branches, List.length_flatMap, List.length_map]
  exact sum_map_constant left.branches right.branches.length

/-- All formulas, including truth/falsity and malformed constraint edges;
no semantic assumptions or successful solver result are required. -/
theorem branches_length_le (formula : Formula n) :
    formula.branches.length ≤ 2 ^ eitherNodes formula := by
  induction formula with
  | truth | falsity | edge => simp [Formula.branches, eitherNodes]
  | both left right leftBound rightBound =>
      rw [branches_both_length]
      simpa only [eitherNodes, Nat.pow_add] using Nat.mul_le_mul leftBound rightBound
  | either left right leftBound rightBound =>
      have growLeft : 2 ^ eitherNodes left ≤ 2 ^ eitherNodes left * 2 ^ eitherNodes right := by
        simpa only [Nat.mul_one] using
          Nat.mul_le_mul_left (2 ^ eitherNodes left) (one_le_two_pow (eitherNodes right))
      have growRight : 2 ^ eitherNodes right ≤ 2 ^ eitherNodes left * 2 ^ eitherNodes right := by
        simpa only [Nat.one_mul] using
          Nat.mul_le_mul_right (2 ^ eitherNodes right) (one_le_two_pow (eitherNodes left))
      have both := Nat.add_le_add (Nat.le_trans leftBound growLeft) (Nat.le_trans rightBound growRight)
      simpa only [Formula.branches, List.length_append, eitherNodes, Nat.pow_succ, Nat.pow_add,
        Nat.mul_two] using both

/-- Every actual branch contains no more edge occurrences than the entire
input formula. Leaves in unchosen alternatives are counted in the bound. -/
theorem branch_length_le (formula : Formula n) (branch : List (NestedValueSolver.Edge n))
    (member : branch ∈ formula.branches) : branch.length ≤ edgeLeaves formula := by
  induction formula generalizing branch with
  | truth =>
      have same : branch = [] := List.mem_singleton.mp member
      simp [same, edgeLeaves]
  | falsity => cases member
  | edge edge =>
      have same : branch = [edge] := List.mem_singleton.mp member
      simp [same, edgeLeaves]
  | both left right leftBound rightBound =>
      obtain ⟨first, firstMember, secondMember⟩ := List.mem_flatMap.mp member
      obtain ⟨last, lastMember, rfl⟩ := List.mem_map.mp secondMember
      simpa only [List.length_append, edgeLeaves] using Nat.add_le_add
        (leftBound first firstMember) (rightBound last lastMember)
  | either left right leftBound rightBound =>
      rcases List.mem_append.mp member with first | last
      · exact Nat.le_trans (leftBound branch first) (Nat.le_add_right _ _)
      · exact Nat.le_trans (rightBound branch last) (Nat.le_add_left _ _)

/-- The actual DNF stores at most `2^D * E` edge occurrences. -/
theorem branches_total_edges_le (formula : Formula n) :
    (formula.branches.map List.length).sum ≤ 2 ^ eitherNodes formula * edgeLeaves formula :=
  Nat.le_trans (sum_map_le_length_mul formula.branches List.length (edgeLeaves formula)
    (fun branch member => branch_length_le formula branch member))
      (Nat.mul_le_mul_right _ (branches_length_le formula))

/-- Filtering rejected branches never increases the number of branches;
the checker may be any Boolean function for this purely structural bound. -/
theorem solve_length_le (rowCheck : Row → Row → Bool)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n) :
    (solve rowCheck graph formula).length ≤ 2 ^ eitherNodes formula :=
  Nat.le_trans (List.length_filterMap_le _ formula.branches) (branches_length_le formula)

theorem accepted_input_length_le (rowCheck : Row → Row → Bool)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n)
    (branch : Branch n) (member : branch ∈ solve rowCheck graph formula) :
    branch.input.length ≤ edgeLeaves formula :=
  branch_length_le formula branch.input ((mem_solve rowCheck graph formula branch).mp member).1

theorem accepted_total_input_edges_le (rowCheck : Row → Row → Bool)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n) :
    ((solve rowCheck graph formula).map fun branch => branch.input.length).sum ≤
      2 ^ eitherNodes formula * edgeLeaves formula :=
  Nat.le_trans (sum_map_le_length_mul (solve rowCheck graph formula) (fun branch => branch.input.length)
    (edgeLeaves formula) (fun branch member => accepted_input_length_le rowCheck graph formula branch member))
      (Nat.mul_le_mul_right _ (solve_length_le rowCheck graph formula))

/-- Sum of all cache lengths actually returned by the branch solver. The
quadratic per-branch capacity is obtained from each returned cache, never
supplied as a premise or assumed of an external branch enumeration. -/
theorem accepted_total_cache_edges_le (rowCheck : Row → Row → Bool)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n) :
    ((solve rowCheck graph formula).map fun branch => branch.cache.length).sum ≤
      2 ^ eitherNodes formula * (n * n) :=
  Nat.le_trans (sum_map_le_length_mul (solve rowCheck graph formula) (fun branch => branch.cache.length)
    (n * n) (fun branch member => (accepted_closed_capacity rowCheck graph formula branch member).2.2))
      (Nat.mul_le_mul_right _ (solve_length_le rowCheck graph formula))

/-- A linear-size family whose repeated alternatives are deliberately kept
by the existing enumerator. This witnesses that the exponential count is
real even when there are no edge obligations; a future sharing/deduplication
pass would need its own semantic and cost theorem. -/
def duplicateTruth (alternatives : Nat) : Formula n :=
  match alternatives with
  | 0 => .truth
  | count + 1 => .both (.either .truth .truth) (duplicateTruth count)

theorem duplicateTruth_counts (alternatives : Nat) :
    eitherNodes (duplicateTruth (n := n) alternatives) = alternatives ∧
      edgeLeaves (duplicateTruth (n := n) alternatives) = 0 ∧
      (duplicateTruth (n := n) alternatives).branches.length = 2 ^ alternatives := by
  induction alternatives with
  | zero => simp [duplicateTruth, eitherNodes, edgeLeaves, Formula.branches]
  | succ count ih =>
      refine ⟨?_, ?_, ?_⟩
      · simp [duplicateTruth, eitherNodes, ih.1, Nat.add_comm]
      · simp [duplicateTruth, edgeLeaves, ih.2.1]
      · rw [duplicateTruth, branches_both_length, ih.2.2]
        simp [Formula.branches, Nat.pow_succ, Nat.mul_comm]

end Yulang.ContextualBranchCost
