import Yulang.ContextualConstructorInspection
import Yulang.ProducerContextualRegular
import Yulang.RegularValueCoalescing

/-!
# All-input constructor saturation in the contextual demand model

This module gives independent regular models to the existing finite nested
constructor graph syntax. Every unknown remains an arbitrary graph-rooted
contextual type. The actual executable `NestedValueSolver.saturate` preserves
all these models, and its accepted output is a finite closed cache.

Rejection is exact for every input graph and edge list: accepted caches have
explicit regular solutions, constructed by the existing coalescer and moved
through proved structural preservation. No input solution, successful solve,
fuel or precomputed closed cache is a premise of the all-input theorem.

The graph language here has pairs, arrows with rows, finite proper record
spines and variants. It does not yet include presence-specific exact emptiness,
optional fields, record-default images or symbolic mask-family constructors.
-/

namespace Yulang.ContextualNestedModels

open RegularValueTypes
open RigidValueLayers (rigidLayer)

universe u v
variable {n : Nat} {Row : Type u} {State : Type v}

def NodeLe (graph : Graph Row State) (leRow : Row → Row → Prop) (left right : State) : Prop :=
  ProducerContextualRegular.ProducerLe graph leRow (graph left) (graph right)

theorem nodeLe_trans {graph : Graph Row State} {leRow : Row → Row → Prop} {a b c : State}
    (first : NodeLe graph leRow a b) (last : NodeLe graph leRow b c) : NodeLe graph leRow a c :=
  ProducerContextualRegular.producerLe_trans first last

def Realizes (graph : NestedValueSolver.Graph n Row) (modelGraph : Graph Row State)
    (leRow : Row → Row → Prop) (valuation : Fin n → State) : Prop :=
  ∀ node, graph node ≠ .var →
    (ProducerContextualRegular.ProducerLe modelGraph leRow (modelGraph (valuation node)) ((rigidLayer (graph node)).map valuation) ∧
      ProducerContextualRegular.ProducerLe modelGraph leRow ((rigidLayer (graph node)).map valuation) (modelGraph (valuation node)))

def Satisfies (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (constraints : List (NestedValueSolver.Edge n)) (valuation : Fin n → State) : Prop :=
  ∀ edge ∈ constraints, NodeLe modelGraph leRow (valuation edge.1) (valuation edge.2)

def Models (leRow : Row → Row → Prop) (graph : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (modelGraph : Graph Row State)
    (valuation : Fin n → State) : Prop :=
  Realizes graph modelGraph leRow valuation ∧ Satisfies modelGraph leRow constraints valuation

def RequirementsHolds (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (valuation : Fin n → State) (requirements : NestedValueSolver.Requirements n Row) : Prop :=
  (∀ child ∈ requirements.types,
    NodeLe modelGraph leRow (valuation child.1) (valuation child.2)) ∧
    ∀ row ∈ requirements.rows, leRow row.1 row.2

def InspectionHolds (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (valuation : Fin n → State) : Option (NestedValueSolver.Requirements n Row) → Prop
  | none => False
  | some requirements => RequirementsHolds modelGraph leRow valuation requirements

theorem observe_subtype (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    {left right : State} (subtype : NodeLe modelGraph leRow left right) (depth : Nat) :
    ProducerContextual.ProducerLe leRow (observe modelGraph depth left) (observe modelGraph depth right) := by
  cases depth with
  | zero => exact ProducerContextual.producerLe_refl _
  | succ depth => exact subtype depth

/-- One extra observation layer exposes the actual child comparison; no
cyclic assumption is used before crossing its constructor. -/
theorem inspect_sound (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (modelGraph : Graph Row State)
    (valuation : Fin n → State) (realizes : Realizes graph modelGraph leRow valuation)
    (edge : NestedValueSolver.Edge n)
    (subtype : NodeLe modelGraph leRow (valuation edge.1) (valuation edge.2)) :
    InspectionHolds modelGraph leRow valuation (NestedValueSolver.inspect (graph edge.1) (graph edge.2)) := by
  by_cases sourceVariable : graph edge.1 = .var
  · simp [sourceVariable, NestedValueSolver.inspect, InspectionHolds, RequirementsHolds]
  by_cases targetVariable : graph edge.2 = .var
  · simp [targetVariable, NestedValueSolver.inspect, InspectionHolds, RequirementsHolds]
  have rigidComparison : ProducerContextualRegular.ProducerLe modelGraph leRow
      ((rigidLayer (graph edge.1)).map valuation) ((rigidLayer (graph edge.2)).map valuation) :=
    ProducerContextualRegular.producerLe_trans (realizes edge.1 sourceVariable).2
      (ProducerContextualRegular.producerLe_trans subtype (realizes edge.2 targetVariable).1)
  have finite (depth : Nat) : ContextualConstructorInspection.InspectionHolds leRow
      (fun node => observe modelGraph depth (valuation node))
      (NestedValueSolver.inspect (graph edge.1) (graph edge.2)) := by
    apply ContextualConstructorInspection.inspect_sound leRow rowRefl rowTrans
      (fun node => observe modelGraph depth (valuation node)) (graph edge.1) (graph edge.2)
      (RigidValueLayers.rigidLayer_holds _ _) (RigidValueLayers.rigidLayer_holds _ _)
    simpa only [Layer.eval_map] using rigidComparison depth
  cases found : NestedValueSolver.inspect (graph edge.1) (graph edge.2) with
  | none =>
      have impossible := finite 0
      simp only [found, ContextualConstructorInspection.InspectionHolds] at impossible
  | some requirements =>
      constructor
      · intro child member depth
        have valid := finite (depth + 1)
        rw [found] at valid
        exact valid.1 child member
      · intro row member
        have valid := finite 0
        rw [found] at valid
        exact valid.2 row member

theorem rules_valid (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row State) (valuation : Fin n → State)
    (model : Models leRow graph constraints modelGraph valuation) :
    ∀ rule ∈ NestedValueSolver.rules graph constraints,
      FiniteHorn.Valid (fun edge => NodeLe modelGraph leRow (valuation edge.1) (valuation edge.2)) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with initial | variables
  · rcases List.mem_append.mp initial with seeds | constructors
    · obtain ⟨edge, originalMember, rfl⟩ := List.mem_map.mp seeds
      exact model.2 edge originalMember
    · obtain ⟨edge, _, ruleMember⟩ := List.mem_flatMap.mp constructors
      cases found : NestedValueSolver.inspect (graph edge.1) (graph edge.2) with
      | none => simp [NestedValueSolver.constructorRules, found] at ruleMember
      | some requirements =>
          simp only [NestedValueSolver.constructorRules, found] at ruleMember
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp ruleMember
          have parentSubtype : NodeLe modelGraph leRow (valuation edge.1) (valuation edge.2) :=
            premises edge (by simp [NestedValueSolver.childRule])
          have valid := inspect_sound leRow rowRefl rowTrans graph modelGraph valuation model.1 edge parentSubtype
          rw [found] at valid
          exact valid.1 child childMember
  · obtain ⟨pivot, _, ruleMember⟩ := List.mem_flatMap.mp variables
    cases isVariable : graph pivot with
    | var =>
        simp only [NestedValueSolver.variableRules, isVariable] at ruleMember
        obtain ⟨edge, _, rfl⟩ := List.mem_map.mp ruleMember
        exact nodeLe_trans (premises (edge.1, pivot) (by simp [NestedValueSolver.flowRule]))
          (premises (pivot, edge.2) (by simp [NestedValueSolver.flowRule]))
    | _ => simp [NestedValueSolver.variableRules, isVariable] at ruleMember

theorem saturate_preserves (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row State) (valuation : Fin n → State)
    (model : Models leRow graph constraints modelGraph valuation) :
    Models leRow graph (NestedValueSolver.saturate graph constraints) modelGraph valuation :=
  ⟨model.1, FiniteHorn.saturate_preserves _ _ _
    (rules_valid leRow rowRefl rowTrans graph constraints modelGraph valuation model)⟩

/-- Every original model and its entire recursive graph are preserved by
saturation, without imposing a depth bound on that model. -/
theorem saturate_models_iff (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row State) (valuation : Fin n → State) :
    Models leRow graph (NestedValueSolver.saturate graph constraints) modelGraph valuation ↔
      Models leRow graph constraints modelGraph valuation := by
  constructor
  · intro model
    exact ⟨model.1, fun edge member => model.2 edge (NestedValueSolver.saturate_contains graph constraints member)⟩
  · exact saturate_preserves leRow rowRefl rowTrans graph constraints modelGraph valuation

theorem consistent_of_models (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row State) (valuation : Fin n → State)
    (model : Models leRow graph cache modelGraph valuation) :
    NestedValueSolver.consistent rowCheck graph cache = true := by
  apply List.all_eq_true.mpr
  intro edge member
  have valid := inspect_sound leRow rowRefl rowTrans graph modelGraph valuation model.1 edge (model.2 edge member)
  cases found : NestedValueSolver.inspect (graph edge.1) (graph edge.2) with
  | none => simp [found, InspectionHolds] at valid
  | some requirements =>
      rw [found] at valid
      apply List.all_eq_true.mpr
      intro row member
      exact (rowExact row.1 row.2).mpr (valid.2 row member)

/-- Rejection excludes a supplied arbitrary regular model. Its state type
is unrestricted, so the result includes every finite regular graph. -/
theorem solve_rejects_model (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (rejected : NestedValueSolver.solve rowCheck graph constraints = none)
    (modelGraph : Graph Row State) (valuation : Fin n → State) :
    ¬ Models leRow graph constraints modelGraph valuation := by
  intro model
  have accepted := consistent_of_models rowCheck leRow rowRefl rowTrans rowExact graph _ modelGraph valuation
    (saturate_preserves leRow rowRefl rowTrans graph constraints modelGraph valuation model)
  simp only [NestedValueSolver.solve, accepted, ↓reduceIte] at rejected
  cases rejected

theorem solve_rejects (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (rejected : NestedValueSolver.solve rowCheck graph constraints = none) :
    ¬ ∃ (modelGraph : Graph Row State) (valuation : Fin n → State),
      Models leRow graph constraints modelGraph valuation := by
  rintro ⟨modelGraph, valuation, model⟩
  exact solve_rejects_model rowCheck leRow rowRefl rowTrans rowExact graph constraints rejected modelGraph valuation model

theorem solve_rejects_finite (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (rejected : NestedValueSolver.solve rowCheck graph constraints = none) :
    ¬ ∃ (size : Nat) (modelGraph : FiniteGraph Row size) (valuation : Fin n → Fin size),
      Models leRow graph constraints modelGraph valuation := by
  rintro ⟨size, modelGraph, valuation, model⟩
  exact solve_rejects_model rowCheck leRow rowRefl rowTrans rowExact graph constraints rejected modelGraph valuation model


theorem old_models_preserved (leRow : Row → Row → Prop)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row State) (valuation : Fin n → State)
    (model : RegularNestedModels.Models leRow graph constraints modelGraph valuation) :
    Models leRow graph constraints modelGraph valuation := by
  constructor
  · intro index rigid
    exact ⟨ProducerContextualRegular.structural_subtype_preserved (leRow := leRow) rowTrans
        (model.1 index rigid).1,
      ProducerContextualRegular.structural_subtype_preserved (leRow := leRow) rowTrans
        (model.1 index rigid).2⟩
  · intro edge member
    exact ProducerContextualRegular.structural_subtype_preserved (leRow := leRow) rowTrans
      (model.2 edge member)

/-- An actual accepted cache constructs a solution for every arbitrary
regular parameter graph and every parameter layer. These parameters carry
no residual subtype constraints. -/
theorem solve_instantiates_model (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache)
    (parameterGraph : Graph Row State) (parameter : Fin n → Layer Row State) :
    Models leRow graph constraints
      (RegularValueCoalescing.coalesceGraph graph cache parameterGraph parameter) Sum.inl :=
  old_models_preserved leRow rowTrans graph constraints _ _
    (RegularValueCoalescing.solve_instantiates_model rowCheck leRow rowSound
      graph constraints cache solved parameterGraph parameter)

/-- All inputs are covered: rejection is exactly absence of an independent
contextual regular model, including assignments with arbitrary lattice types,
roles and complete arrow observations. There is no success or fuel premise. -/
theorem solve_none_iff (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n)) :
    NestedValueSolver.solve rowCheck graph constraints = none ↔
      ¬ ∃ (ModelState : Type) (model : Graph Row ModelState) (value : Fin n → ModelState),
        Models leRow graph constraints model value := by
  constructor
  · rintro rejected ⟨ModelState, model, value, satisfies⟩
    exact solve_rejects_model rowCheck leRow rowRefl rowTrans rowExact graph constraints
      rejected model value satisfies
  · intro impossible
    cases solved : NestedValueSolver.solve rowCheck graph constraints with
    | none => rfl
    | some cache =>
        exact False.elim (impossible ⟨Fin n ⊕ Unit,
          RegularValueCoalescing.coalesceGraph graph cache (fun _ : Unit => .bottom) (fun _ => .bottom),
          Sum.inl, solve_instantiates_model rowCheck leRow rowTrans
            (fun left right => (rowExact left right).mp) graph constraints cache solved
            (fun _ : Unit => .bottom) (fun _ => .bottom)⟩)

/-- The `Closed` certificate is the constructor/variable obligation cache of
`NestedValueSolver`, not the obstructed all-mask presence cache. Every actual
accepted result has this certificate and the original quadratic capacity. -/
theorem solve_closed_capacity (rowCheck : Row → Row → Bool) (graph : NestedValueSolver.Graph n Row)
    (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache) :
    NestedValueSolver.Closed graph constraints cache ∧
      NestedValueSolver.consistent rowCheck graph cache = true ∧ cache.length ≤ n * n := by
  obtain ⟨closed, consistent⟩ := NestedValueSolver.solve_closed rowCheck graph constraints cache solved
  have same := ((NestedValueSolver.solve_some_iff rowCheck graph constraints cache).mp solved).1
  exact ⟨closed, consistent, same ▸ NestedValueSolver.saturate_capacity graph constraints⟩

end Yulang.ContextualNestedModels
