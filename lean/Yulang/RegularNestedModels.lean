import Yulang.RigidValueLayers

/-!
# Independent regular models of nested subtype constraints

A model supplies a guarded type graph and a value for every constraint node.
Each rigid node agrees, up to mutual semantic subtyping, with its actual
constructor interpretation. Variables remain arbitrary graph-rooted types.
These definitions mention neither saturation nor coalescing.

Finite-depth constructor inversion transfers the solver's obligations to
this recursive semantics. Saturation preserves the entire regular model set,
and rejection excludes every such model. Success and its constructive
principal parameterization belong to the coalescing layer.
-/

namespace Yulang.RegularNestedModels

open RegularValueTypes
open RigidValueLayers (rigidLayer)

universe u v

variable {n : Nat} {Row : Type u} {State : Type v}

def Realizes (graph : NestedValueSolver.Graph n Row) (modelGraph : Graph Row State)
    (leRow : Row → Row → Prop) (valuation : Fin n → State) : Prop :=
  ∀ node, graph node ≠ .var →
    (Subtype modelGraph leRow (modelGraph (valuation node)) ((rigidLayer (graph node)).map valuation) ∧
      Subtype modelGraph leRow ((rigidLayer (graph node)).map valuation) (modelGraph (valuation node)))

def Satisfies (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (constraints : List (NestedValueSolver.Edge n)) (valuation : Fin n → State) : Prop :=
  ∀ edge ∈ constraints, NodeSubtype modelGraph leRow (valuation edge.1) (valuation edge.2)

def Models (leRow : Row → Row → Prop) (graph : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (modelGraph : Graph Row State)
    (valuation : Fin n → State) : Prop :=
  Realizes graph modelGraph leRow valuation ∧ Satisfies modelGraph leRow constraints valuation

def RequirementsHolds (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (valuation : Fin n → State) (requirements : NestedValueSolver.Requirements n Row) : Prop :=
  (∀ child ∈ requirements.types,
    NodeSubtype modelGraph leRow (valuation child.1) (valuation child.2)) ∧
    ∀ row ∈ requirements.rows, leRow row.1 row.2

def InspectionHolds (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (valuation : Fin n → State) : Option (NestedValueSolver.Requirements n Row) → Prop
  | none => False
  | some requirements => RequirementsHolds modelGraph leRow valuation requirements

theorem observe_subtype (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    {left right : State} (subtype : NodeSubtype modelGraph leRow left right) (depth : Nat) :
    StructuralBase.Subtype leRow (observe modelGraph depth left) (observe modelGraph depth right) := by
  cases depth with
  | zero => exact .refl _
  | succ depth => exact subtype depth

/-- One extra observation layer exposes the actual child comparison; no
cyclic assumption is used before crossing its constructor. -/
theorem inspect_sound (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (modelGraph : Graph Row State)
    (valuation : Fin n → State) (realizes : Realizes graph modelGraph leRow valuation)
    (edge : NestedValueSolver.Edge n)
    (subtype : NodeSubtype modelGraph leRow (valuation edge.1) (valuation edge.2)) :
    InspectionHolds modelGraph leRow valuation (NestedValueSolver.inspect (graph edge.1) (graph edge.2)) := by
  by_cases sourceVariable : graph edge.1 = .var
  · simp [sourceVariable, NestedValueSolver.inspect, InspectionHolds, RequirementsHolds]
  by_cases targetVariable : graph edge.2 = .var
  · simp [targetVariable, NestedValueSolver.inspect, InspectionHolds, RequirementsHolds]
  have rigidComparison : Subtype modelGraph leRow
      ((rigidLayer (graph edge.1)).map valuation) ((rigidLayer (graph edge.2)).map valuation) :=
    subtype_trans (realizes edge.1 sourceVariable).2
      (subtype_trans subtype (realizes edge.2 targetVariable).1)
  have finite (depth : Nat) : NestedValueSolver.InspectionHolds leRow
      (fun node => observe modelGraph depth (valuation node))
      (NestedValueSolver.inspect (graph edge.1) (graph edge.2)) := by
    apply NestedValueSolver.inspect_sound leRow rowRefl rowTrans
      (fun node => observe modelGraph depth (valuation node)) (graph edge.1) (graph edge.2)
      (RigidValueLayers.rigidLayer_holds _ _) (RigidValueLayers.rigidLayer_holds _ _)
    simpa only [At, Layer.eval_map] using rigidComparison depth
  cases found : NestedValueSolver.inspect (graph edge.1) (graph edge.2) with
  | none =>
      have impossible := finite 0
      simp only [found, NestedValueSolver.InspectionHolds] at impossible
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
      FiniteHorn.Valid (fun edge => NodeSubtype modelGraph leRow (valuation edge.1) (valuation edge.2)) rule := by
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
          have parentSubtype : NodeSubtype modelGraph leRow (valuation edge.1) (valuation edge.2) :=
            premises edge (by simp [NestedValueSolver.childRule])
          have valid := inspect_sound leRow rowRefl rowTrans graph modelGraph valuation model.1 edge parentSubtype
          rw [found] at valid
          exact valid.1 child childMember
  · obtain ⟨pivot, _, ruleMember⟩ := List.mem_flatMap.mp variables
    cases isVariable : graph pivot with
    | var =>
        simp only [NestedValueSolver.variableRules, isVariable] at ruleMember
        obtain ⟨edge, _, rfl⟩ := List.mem_map.mp ruleMember
        exact node_subtype_trans (premises (edge.1, pivot) (by simp [NestedValueSolver.flowRule]))
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

/-! ## Invariance of independent models under semantic equivalence -/

def Equivalent (modelGraph : Graph Row State) (leRow : Row → Row → Prop)
    (left right : Fin n → State) : Prop :=
  ∀ index, NodeSubtype modelGraph leRow (left index) (right index) ∧
    NodeSubtype modelGraph leRow (right index) (left index)

theorem rigidLayer_map_equivalent (modelGraph : Graph Row State)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (left right : Fin n → State) (equivalent : Equivalent modelGraph leRow left right)
    (node : NestedValueSolver.Node n Row) :
    Subtype modelGraph leRow ((rigidLayer node).map left) ((rigidLayer node).map right) ∧
      Subtype modelGraph leRow ((rigidLayer node).map right) ((rigidLayer node).map left) := by
  have atDepth (depth : Nat) := RigidValueLayers.rigidLayer_eval_equivalent leRow rowRefl
    (fun index => observe modelGraph depth (left index))
    (fun index => observe modelGraph depth (right index))
    (fun index => ⟨observe_subtype modelGraph leRow (equivalent index).1 depth,
      observe_subtype modelGraph leRow (equivalent index).2 depth⟩) node
  constructor
  · intro depth
    simpa only [At, Layer.eval_map] using (atDepth depth).1
  · intro depth
    simpa only [At, Layer.eval_map] using (atDepth depth).2

theorem models_equivalent (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row State) (left right : Fin n → State)
    (model : Models leRow graph constraints modelGraph left)
    (equivalent : Equivalent modelGraph leRow left right) :
    Models leRow graph constraints modelGraph right := by
  constructor
  · intro node rigid
    obtain ⟨forward, backward⟩ := model.1 node rigid
    obtain ⟨rigidForward, rigidBackward⟩ := rigidLayer_map_equivalent modelGraph leRow rowRefl left right equivalent (graph node)
    exact ⟨subtype_trans (equivalent node).2 (subtype_trans forward rigidForward),
      subtype_trans rigidBackward (subtype_trans backward (equivalent node).1)⟩
  · intro edge member
    exact node_subtype_trans (equivalent edge.1).2
      (node_subtype_trans (model.2 edge member) (equivalent edge.2).1)

end Yulang.RegularNestedModels
