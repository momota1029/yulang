import Yulang.RegularValueCoalescing

/-!
# An executable inference entry returning a regular principal scheme

The caller supplies a finite nested constraint problem and its output node,
not a successful cache, a type assignment, or a model-existence proof.
Instantiation of a returned scheme constructs a graph without testing the
original constraints again. The public exactness theorem quantifies over the
actual inference call and all original constrained output instances.
-/

namespace Yulang.RegularSchemeInference

open RegularValueTypes RegularValueCoalescing

universe u v

structure Scheme (n : Nat) (Row : Type u) where
  graph : NestedValueSolver.Graph n Row
  cache : List (NestedValueSolver.Edge n)
  output : Fin n

def Scheme.instantiate (scheme : Scheme n Row) (parameters : Graph Row State)
    (parameter : Fin n → Layer Row State) : Graph Row (Fin n ⊕ State) :=
  coalesceGraph scheme.graph scheme.cache parameters parameter

def Scheme.Instance (scheme : Scheme n Row) (leRow : Row → Row → Prop)
    (targetGraph : Graph Row State) (target : Layer Row State) : Prop :=
  SchemeInstance scheme.graph scheme.cache scheme.output leRow targetGraph target

def infer (rowCheck : Row → Row → Bool) (graph : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (output : Fin n) : Option (Scheme n Row) :=
  (NestedValueSolver.solve rowCheck graph constraints).map fun cache => ⟨graph, cache, output⟩

theorem infer_some_iff (rowCheck : Row → Row → Bool) (graph : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (output : Fin n) (scheme : Scheme n Row) :
    infer rowCheck graph constraints output = some scheme ↔
      ∃ cache, NestedValueSolver.solve rowCheck graph constraints = some cache ∧
        scheme = ⟨graph, cache, output⟩ := by
  simp only [infer, Option.map_eq_some_iff]
  constructor
  · rintro ⟨cache, solved, same⟩
    exact ⟨cache, solved, same.symm⟩
  · rintro ⟨cache, solved, rfl⟩
    exact ⟨cache, solved, rfl⟩

/-- Every free parameter choice yields a genuine model of the original
problem. There are no instantiation-time inequality side conditions. -/
theorem infer_sound (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (output : Fin n) {scheme : Scheme n Row}
    (inferred : infer rowCheck graph constraints output = some scheme)
    (parameters : Graph Row State) (parameter : Fin n → Layer Row State) :
    RegularNestedModels.Models leRow graph constraints (scheme.instantiate parameters parameter) Sum.inl := by
  obtain ⟨cache, solved, rfl⟩ := (infer_some_iff rowCheck graph constraints output scheme).mp inferred
  exact solve_instantiates_model rowCheck leRow rowSound graph constraints cache solved parameters parameter

/-- Actual inference and the independent existential source constraints
have precisely the same output instances, including recursive instances. -/
theorem infer_principal_exact (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (output : Fin n) (targetGraph : Graph Row State) (target : Layer Row State) :
    (∃ scheme, infer rowCheck graph constraints output = some scheme ∧
      scheme.Instance leRow targetGraph target) ↔
      ConstrainedInstance graph constraints output leRow targetGraph target := by
  constructor
  · rintro ⟨scheme, inferred, instanceOf⟩
    obtain ⟨cache, solved, rfl⟩ := (infer_some_iff rowCheck graph constraints output scheme).mp inferred
    exact (solve_instances_exact rowCheck leRow rowRefl rowTrans rowExact graph constraints cache
      solved output targetGraph target).mpr instanceOf
  · intro instanceOf
    cases solved : NestedValueSolver.solve rowCheck graph constraints with
    | none =>
        obtain ⟨ModelState, model, value, _, _, satisfies, _⟩ := instanceOf
        exact False.elim (RegularNestedModels.solve_rejects_model rowCheck leRow rowRefl rowTrans
          rowExact graph constraints solved model value satisfies)
    | some cache =>
        exact ⟨⟨graph, cache, output⟩,
          (infer_some_iff rowCheck graph constraints output _).mpr ⟨cache, solved, rfl⟩,
          (solve_instances_exact rowCheck leRow rowRefl rowTrans rowExact graph constraints cache
            solved output targetGraph target).mp instanceOf⟩

theorem infer_none_iff (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (output : Fin n) :
    infer rowCheck graph constraints output = none ↔
      ¬ ∃ (ModelState : Type) (model : Graph Row ModelState) (value : Fin n → ModelState),
        RegularNestedModels.Models leRow graph constraints model value := by
  simp only [infer, Option.map_eq_none_iff]
  exact solve_none_iff rowCheck leRow rowRefl rowTrans rowExact graph constraints

end Yulang.RegularSchemeInference
