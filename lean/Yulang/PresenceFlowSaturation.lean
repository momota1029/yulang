import Yulang.PresenceMaskedCoalescing
import Yulang.FiniteHorn

/-!
# Finite, model-preserving variable-flow saturation for presence graphs

The cache contains only input edges and their consequences by transitivity
through variable nodes. At most `n * n` distinct edges are inserted; callers
provide neither fuel nor a precomputed cache. Every independent input solution
is preserved, including every mask-indexed solution.

For variable-only graphs this is the entire saturation problem: no rigid
constructor inspection remains. Consequently the computed cache is closed,
arbitrary free regular parameters give solutions, and all independent input
solutions are retracted. For graphs containing constructors this module proves
the flow part only. It never infers payload inequalities by decomposing semantic
products or records, since empty payloads can invalidate that inversion.
-/

namespace Yulang.PresenceFlowSaturation

open PresenceRegularCoalescing (Graph Edge Closed coalesceGraph)
open PresenceLayers (Layer)

universe u
variable {n : Nat} {Index : Type u}

def allEdges (n : Nat) : List (Edge n) :=
  (List.finRange n).flatMap fun source => (List.finRange n).map fun target => (source, target)

theorem mem_allEdges (edge : Edge n) : edge ∈ allEdges n := by
  obtain ⟨source, target⟩ := edge
  simp [allEdges]

theorem allEdges_length (n : Nat) : (allEdges n).length = n * n := by
  simp [allEdges, List.length_flatMap, List.map_const', List.sum_replicate_nat]

def seedRule (edge : Edge n) : FiniteHorn.Rule (Edge n) := ⟨[], edge⟩
def flowRule (pivot : Fin n) (edge : Edge n) : FiniteHorn.Rule (Edge n) :=
  ⟨[(edge.1, pivot), (pivot, edge.2)], edge⟩

def variableRules (graph : Graph n) (pivot : Fin n) : List (FiniteHorn.Rule (Edge n)) :=
  match graph pivot with
  | none => (allEdges n).map (flowRule pivot)
  | some _ => []

def rules (graph : Graph n) (constraints : List (Edge n)) : List (FiniteHorn.Rule (Edge n)) :=
  constraints.map seedRule ++ (List.finRange n).flatMap (variableRules graph)

def saturate (graph : Graph n) (constraints : List (Edge n)) : List (Edge n) :=
  FiniteHorn.saturate (rules graph constraints) (allEdges n)

/-- This consequence relation mentions no inference output or semantic
valuation; it records exactly which finite closure rules were used. -/
inductive EdgeConsequence (graph : Graph n) (constraints : List (Edge n)) : Edge n → Prop where
  | input : edge ∈ constraints → EdgeConsequence graph constraints edge
  | through : graph pivot = none →
      EdgeConsequence graph constraints (source, pivot) →
      EdgeConsequence graph constraints (pivot, target) →
      EdgeConsequence graph constraints (source, target)

theorem saturate_nodup (graph : Graph n) (constraints : List (Edge n)) :
    (saturate graph constraints).Nodup := FiniteHorn.saturate_nodup _ _

theorem saturate_capacity (graph : Graph n) (constraints : List (Edge n)) :
    (saturate graph constraints).length ≤ n * n := by
  rw [← allEdges_length]
  exact FiniteHorn.saturate_length_le _ _ mem_allEdges

private theorem seedRule_mem (graph : Graph n) (constraints : List (Edge n))
    {edge : Edge n} (member : edge ∈ constraints) : seedRule edge ∈ rules graph constraints :=
  List.mem_append_left _ (List.mem_map.mpr ⟨edge, member, rfl⟩)

private theorem flowRule_mem (graph : Graph n) (constraints : List (Edge n))
    (pivot : Fin n) (isVariable : graph pivot = none) (edge : Edge n) :
    flowRule pivot edge ∈ rules graph constraints := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pivot, by simp, ?_⟩
  simp only [variableRules, isVariable]
  exact List.mem_map.mpr ⟨edge, mem_allEdges edge, rfl⟩

theorem saturate_contains (graph : Graph n) (constraints : List (Edge n))
    {edge : Edge n} (member : edge ∈ constraints) : edge ∈ saturate graph constraints := by
  apply FiniteHorn.saturate_closed _ _ mem_allEdges
  exact ⟨seedRule edge, seedRule_mem graph constraints member, rfl, by simp [seedRule]⟩

theorem saturate_variable_closed (graph : Graph n) (constraints : List (Edge n))
    (pivot : Fin n) (isVariable : graph pivot = none) (source target : Fin n)
    (lower : (source, pivot) ∈ saturate graph constraints)
    (upper : (pivot, target) ∈ saturate graph constraints) :
    (source, target) ∈ saturate graph constraints := by
  apply FiniteHorn.saturate_closed _ _ mem_allEdges
  refine ⟨flowRule pivot (source, target), flowRule_mem graph constraints pivot isVariable _, rfl, ?_⟩
  simpa [flowRule, saturate] using And.intro lower upper

private theorem rules_consequences (graph : Graph n) (constraints : List (Edge n)) :
    ∀ rule ∈ rules graph constraints, FiniteHorn.Valid (EdgeConsequence graph constraints) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with initial | flows
  · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp initial
    exact .input present
  · obtain ⟨pivot, _, member⟩ := List.mem_flatMap.mp flows
    cases isVariable : graph pivot with
    | none =>
        simp only [variableRules, isVariable] at member
        obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
        exact .through isVariable
          (premises (edge.1, pivot) (by simp [flowRule]))
          (premises (pivot, edge.2) (by simp [flowRule]))
    | some layer => simp [variableRules, isVariable] at member

theorem saturate_consequence (graph : Graph n) (constraints : List (Edge n)) :
    ∀ edge ∈ saturate graph constraints, EdgeConsequence graph constraints edge :=
  FiniteHorn.saturate_preserves _ _ _ (rules_consequences graph constraints)

/-- Membership is exactly finite derivability, including paths of arbitrary
length and cycles. The `n * n` bound is a finite-state capacity, not a cutoff. -/
theorem saturate_exact (graph : Graph n) (constraints : List (Edge n)) (edge : Edge n) :
    edge ∈ saturate graph constraints ↔ EdgeConsequence graph constraints edge := by
  constructor
  · exact saturate_consequence graph constraints edge
  · intro derived
    induction derived with
    | input member => exact saturate_contains graph constraints member
    | @through pivot source target isVariable _ _ lower upper =>
        exact saturate_variable_closed graph constraints pivot isVariable source target lower upper

theorem EdgeConsequence.sound {graph : Graph n} {constraints : List (Edge n)} {edge : Edge n}
    (derived : EdgeConsequence graph constraints edge) (holds : Edge n → Prop)
    (initial : ∀ edge ∈ constraints, holds edge)
    (transitive : ∀ source middle target, holds (source, middle) → holds (middle, target) → holds (source, target)) :
    holds edge := by
  induction derived with
  | input member => exact initial _ member
  | through _ _ _ lower upper => exact transitive _ _ _ lower upper

theorem saturate_preserves (graph : Graph n) (constraints : List (Edge n)) (holds : Edge n → Prop)
    (initial : ∀ edge ∈ constraints, holds edge)
    (transitive : ∀ source middle target, holds (source, middle) → holds (middle, target) → holds (source, target)) :
    ∀ edge ∈ saturate graph constraints, holds edge :=
  fun edge member => (saturate_consequence graph constraints edge member).sound holds initial transitive

/-- All independent unmasked regular input solutions survive saturation. -/
theorem saturate_models_iff (graph : Graph n) (constraints : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index) :
    PresenceRegularCoalescing.Models graph (saturate graph constraints) original value ↔
      PresenceRegularCoalescing.Models graph constraints original value := by
  constructor
  · intro model
    exact ⟨model.1, fun edge member => model.2 edge (saturate_contains graph constraints member)⟩
  · intro model
    refine ⟨model.1, saturate_preserves graph constraints _ model.2 ?_⟩
    intro source middle target first last depth item valid
    exact last depth item (first depth item valid)

/-- Root masks are universally preserved too; no constructor inversion is
performed while deriving new edges. -/
theorem saturate_masked_models_iff (graph : Graph n) (constraints : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index) :
    PresenceMaskedCoalescing.Models graph (saturate graph constraints) original value ↔
      PresenceMaskedCoalescing.Models graph constraints original value := by
  constructor
  · intro model
    exact ⟨model.1, fun edge member => model.2 edge (saturate_contains graph constraints member)⟩
  · intro model
    refine ⟨model.1, saturate_preserves graph constraints _ model.2 ?_⟩
    intro source middle target first last depth hidden item valid
    exact last depth hidden item (first depth hidden item valid)

/-- The actual finite flow cache, rather than a hypothesized cache, retracts
every independent input solution. This direction holds even with constructors;
arbitrary-parameter satisfaction still needs their closure certificates. -/
theorem coalesce_saturated_retraction (graph : Graph n) (constraints : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index)
    (model : PresenceMaskedCoalescing.Models graph constraints original value) :
    ∀ index,
      PresenceMaskedCoalescing.NodeSubtype
        (coalesceGraph graph (saturate graph constraints) original (fun index => original (value index)))
        (.inl index) (.inr (value index)) ∧
      PresenceMaskedCoalescing.NodeSubtype
        (coalesceGraph graph (saturate graph constraints) original (fun index => original (value index)))
        (.inr (value index)) (.inl index) :=
  PresenceMaskedCoalescing.coalesceGraph_retraction graph (saturate graph constraints) original value
    ((saturate_masked_models_iff graph constraints original value).mpr model)

/-- A purely syntactic fragment: all stored nodes are variables, and every
finite edge list is admitted. No solution or successful solve is a premise. -/
def VariableOnly (graph : Graph n) : Prop := ∀ index, graph index = none

theorem variable_saturate_closed (graph : Graph n) (variables : VariableOnly graph)
    (constraints : List (Edge n)) : Closed graph constraints (saturate graph constraints) where
  inputs := fun _ member => saturate_contains graph constraints member
  propagate := saturate_variable_closed graph constraints
  rigid := by
    intro source target left right first _ _
    rw [variables source] at first
    cases first

/-- Variable-only flow problems are solved for every free parameter graph
and every parameter layer, without an oracle, fuel or a supplied closed cache. -/
theorem variable_coalesce_satisfies (graph : Graph n) (variables : VariableOnly graph)
    (constraints : List (Edge n)) (parameterGraph : PresenceRegularObservations.Graph Index)
    (parameter : Fin n → Layer Index) :
    PresenceMaskedCoalescing.Models graph constraints
      (coalesceGraph graph (saturate graph constraints) parameterGraph parameter) Sum.inl :=
  PresenceMaskedCoalescing.coalesceGraph_satisfies graph constraints (saturate graph constraints)
    (variable_saturate_closed graph variables constraints) parameterGraph parameter

theorem variable_satisfiable (graph : Graph n) (variables : VariableOnly graph) (constraints : List (Edge n)) :
    ∃ original : PresenceRegularObservations.Graph (Fin n ⊕ Unit),
      PresenceMaskedCoalescing.Models graph constraints original Sum.inl :=
  ⟨coalesceGraph graph (saturate graph constraints) (fun _ : Unit => .bottom) (fun _ => .top),
    variable_coalesce_satisfies graph variables constraints _ _⟩

/-- The computed shared-parameter family is exactly the full independent
solution family of every variable-only graph. No successful solve, supplied
cache, fuel, concrete solution or restricted parameter catalogue is a premise. -/
theorem variable_models_exact (graph : Graph n) (variables : VariableOnly graph)
    (constraints : List (Edge n)) (original : PresenceRegularObservations.Graph Index)
    (value : Fin n → Index) :
    PresenceMaskedCoalescing.Models graph constraints original value ↔
      ∃ parameter : Fin n → Layer Index, ∀ index,
        PresenceMaskedCoalescing.NodeSubtype
          (coalesceGraph graph (saturate graph constraints) original parameter)
          (.inl index) (.inr (value index)) ∧
        PresenceMaskedCoalescing.NodeSubtype
          (coalesceGraph graph (saturate graph constraints) original parameter)
          (.inr (value index)) (.inl index) := by
  constructor
  · intro model
    exact ⟨fun index => original (value index), coalesce_saturated_retraction graph constraints original value model⟩
  · rintro ⟨parameter, equivalent⟩
    have generated := variable_coalesce_satisfies graph variables constraints original parameter
    constructor
    · intro index layer rigid
      rw [variables index] at rigid
      cases rigid
    · intro edge member depth hidden item valid
      have source := (PresenceMaskedCoalescing.parameter_embedding graph (saturate graph constraints)
        original parameter depth hidden (value edge.1) item).mpr valid
      have target := (equivalent edge.2).1 depth hidden item
        (generated.2 edge member depth hidden item ((equivalent edge.1).2 depth hidden item source))
      exact (PresenceMaskedCoalescing.parameter_embedding graph (saturate graph constraints)
        original parameter depth hidden (value edge.2) item).mp target

end Yulang.PresenceFlowSaturation
