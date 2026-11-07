import Yulang.ContextualNestedModels

/-!
# Executable branching over contextual constructor constraints

The input is an arbitrary finite conjunction/disjunction of graph-edge
obligations. `Formula.branches` computes the complete finite disjunctive form;
`solve` saturates and checks every resulting branch with the actual nested
constructor solver. No successful branch, solution or closed cache is an input.

For the declared graph language (variables, bases, pairs, arrows with rows,
proper record spines and variants), every independent contextual model survives
in exactly the accepted cache family. Empty output is exactly unsatisfiability.
Accepted caches carry constructor/variable closure and quadratic capacity.
Presence-specific optional/exact/default constructors require further lowering;
this module does not identify their inputs with these edge formulas.
-/

namespace Yulang.ContextualBranchSolver

open RegularValueTypes
open NestedValueSolver (Edge)

universe u v
variable {n : Nat} {Row : Type u} {State : Type v}

inductive Formula (n : Nat) where
  | truth
  | falsity
  | edge (obligation : Edge n)
  | both (left right : Formula n)
  | either (left right : Formula n)
  deriving Repr

def Formula.Holds (holds : Edge n → Prop) : Formula n → Prop
  | .truth => True
  | .falsity => False
  | .edge obligation => holds obligation
  | .both left right => left.Holds holds ∧ right.Holds holds
  | .either left right => left.Holds holds ∨ right.Holds holds

def Formula.branches : Formula n → List (List (Edge n))
  | .truth => [[]]
  | .falsity => []
  | .edge obligation => [[obligation]]
  | .both left right => left.branches.flatMap fun first =>
      right.branches.map fun last => first ++ last
  | .either left right => left.branches ++ right.branches

theorem branches_exact (holds : Edge n → Prop) (formula : Formula n) :
    formula.Holds holds ↔ ∃ branch ∈ formula.branches, ∀ edge ∈ branch, holds edge := by
  induction formula with
  | truth => simp [Formula.Holds, Formula.branches]
  | falsity => simp [Formula.Holds, Formula.branches]
  | edge edge => cases edge; simp [Formula.Holds, Formula.branches]
  | both left right first last =>
      constructor
      · rintro ⟨leftModel, rightModel⟩
        obtain ⟨leftBranch, leftMember, leftValid⟩ := first.mp leftModel
        obtain ⟨rightBranch, rightMember, rightValid⟩ := last.mp rightModel
        refine ⟨leftBranch ++ rightBranch, List.mem_flatMap.mpr
          ⟨leftBranch, leftMember, List.mem_map.mpr ⟨rightBranch, rightMember, rfl⟩⟩, ?_⟩
        intro edge member
        exact (List.mem_append.mp member).elim (leftValid edge) (rightValid edge)
      · rintro ⟨branch, member, valid⟩
        obtain ⟨leftBranch, leftMember, member⟩ := List.mem_flatMap.mp member
        obtain ⟨rightBranch, rightMember, rfl⟩ := List.mem_map.mp member
        exact ⟨first.mpr ⟨leftBranch, leftMember,
          fun edge present => valid edge (List.mem_append_left _ present)⟩,
          last.mpr ⟨rightBranch, rightMember,
            fun edge present => valid edge (List.mem_append_right _ present)⟩⟩
  | either left right first last =>
      constructor
      · intro valid
        rcases valid with valid | valid
        · obtain ⟨branch, member, valid⟩ := first.mp valid
          exact ⟨branch, List.mem_append_left _ member, valid⟩
        · obtain ⟨branch, member, valid⟩ := last.mp valid
          exact ⟨branch, List.mem_append_right _ member, valid⟩
      · rintro ⟨branch, member, valid⟩
        exact (List.mem_append.mp member).elim
          (fun member => Or.inl (first.mpr ⟨branch, member, valid⟩))
          (fun member => Or.inr (last.mpr ⟨branch, member, valid⟩))

structure Branch (n : Nat) where
  input : List (Edge n)
  cache : List (Edge n)
  deriving Repr

def solve (rowCheck : Row → Row → Bool) (graph : NestedValueSolver.Graph n Row)
    (formula : Formula n) : List (Branch n) :=
  formula.branches.filterMap fun input =>
    (NestedValueSolver.solve rowCheck graph input).map fun cache => ⟨input, cache⟩

theorem mem_solve (rowCheck : Row → Row → Bool) (graph : NestedValueSolver.Graph n Row)
    (formula : Formula n) (branch : Branch n) :
    branch ∈ solve rowCheck graph formula ↔
      branch.input ∈ formula.branches ∧
        NestedValueSolver.solve rowCheck graph branch.input = some branch.cache := by
  constructor
  · intro member
    obtain ⟨input, present, mapped⟩ := List.mem_filterMap.mp member
    cases found : NestedValueSolver.solve rowCheck graph input with
    | none => simp [found] at mapped
    | some cache =>
        have same : (⟨input, cache⟩ : Branch n) = branch := by simpa [found] using mapped
        subst branch
        exact ⟨present, found⟩
  · rintro ⟨member, found⟩
    exact List.mem_filterMap.mpr ⟨branch.input, member, by simp [found]⟩

def Models (leRow : Row → Row → Prop) (graph : NestedValueSolver.Graph n Row)
    (formula : Formula n) (modelGraph : Graph Row State) (value : Fin n → State) : Prop :=
  ContextualNestedModels.Realizes graph modelGraph leRow value ∧
    formula.Holds (fun edge => ContextualNestedModels.NodeLe modelGraph leRow
      (value edge.1) (value edge.2))

/-- Every independent input model is retained by an actual accepted branch,
and every model of an accepted cache is a model of the input formula. -/
theorem solve_models_exact (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n)
    (modelGraph : Graph Row State) (value : Fin n → State) :
    Models leRow graph formula modelGraph value ↔
      ∃ branch ∈ solve rowCheck graph formula,
        ContextualNestedModels.Models leRow graph branch.cache modelGraph value := by
  constructor
  · rintro ⟨realizes, valid⟩
    obtain ⟨input, member, satisfies⟩ := (branches_exact _ formula).mp valid
    have initial : ContextualNestedModels.Models leRow graph input modelGraph value := ⟨realizes, satisfies⟩
    have saturated := ContextualNestedModels.saturate_preserves leRow rowRefl rowTrans
      graph input modelGraph value initial
    have consistent := ContextualNestedModels.consistent_of_models rowCheck leRow rowRefl rowTrans
      rowExact graph _ modelGraph value saturated
    have solved : NestedValueSolver.solve rowCheck graph input =
        some (NestedValueSolver.saturate graph input) := by
      simp [NestedValueSolver.solve, consistent]
    exact ⟨⟨input, NestedValueSolver.saturate graph input⟩,
      (mem_solve rowCheck graph formula _).mpr ⟨member, solved⟩, saturated⟩
  · rintro ⟨branch, member, cached⟩
    obtain ⟨inputMember, solved⟩ := (mem_solve rowCheck graph formula branch).mp member
    have same := ((NestedValueSolver.solve_some_iff rowCheck graph branch.input branch.cache).mp solved).1
    have initial := (ContextualNestedModels.saturate_models_iff leRow rowRefl rowTrans
      graph branch.input modelGraph value).mp (same ▸ cached)
    exact ⟨initial.1, (branches_exact _ formula).mpr ⟨branch.input, inputMember, initial.2⟩⟩

/-- Closure and capacity are conclusions about every returned branch. -/
theorem accepted_closed_capacity (rowCheck : Row → Row → Bool)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n)
    (branch : Branch n) (member : branch ∈ solve rowCheck graph formula) :
    NestedValueSolver.Closed graph branch.input branch.cache ∧
      NestedValueSolver.consistent rowCheck graph branch.cache = true ∧ branch.cache.length ≤ n * n :=
  ContextualNestedModels.solve_closed_capacity rowCheck graph branch.input branch.cache
    ((mem_solve rowCheck graph formula branch).mp member).2

/-- All finite formulas are decided, including the empty disjunction. An
empty result is a semantic rejection, never a fuel/unsupported outcome. -/
theorem solve_nil_iff (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (formula : Formula n) :
    solve rowCheck graph formula = [] ↔
      ¬ ∃ (ModelState : Type) (modelGraph : Graph Row ModelState) (value : Fin n → ModelState),
        Models leRow graph formula modelGraph value := by
  constructor
  · rintro rejected ⟨ModelState, modelGraph, value, model⟩
    obtain ⟨branch, member, _⟩ :=
      (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact graph formula modelGraph value).mp model
    simp [rejected] at member
  · intro impossible
    cases result : solve rowCheck graph formula with
    | nil => rfl
    | cons branch rest =>
        have member : branch ∈ solve rowCheck graph formula := by simp [result]
        obtain ⟨inputMember, solved⟩ := (mem_solve rowCheck graph formula branch).mp member
        let modelGraph := RegularValueCoalescing.coalesceGraph graph branch.cache
          (fun _ : Unit => Layer.bottom) (fun _ => Layer.bottom)
        have initial := ContextualNestedModels.solve_instantiates_model rowCheck leRow rowTrans
          (fun left right => (rowExact left right).mp) graph branch.input branch.cache solved
          (fun _ : Unit => Layer.bottom) (fun _ => Layer.bottom)
        exact False.elim (impossible ⟨Fin n ⊕ Unit, modelGraph, Sum.inl,
          initial.1, (branches_exact _ formula).mpr ⟨branch.input, inputMember, initial.2⟩⟩)

end Yulang.ContextualBranchSolver
