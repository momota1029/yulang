import Yulang.PresenceFlowSaturation

/-!
# Exact coalescing for one-sided bounds on recursive presence constructors

The graph may contain every existing presence constructor, arbitrary recursive
payload references, and shared variables. The input edges are syntactically
one-sided: either every target is a variable, or every source is a variable.
This excludes a path from a rigid lower bound through variables to a rigid
upper bound, so the computed flow cache is closed without constructor inversion.

The results quantify all independent mask-indexed input solutions and all free
regular parameter graphs. No cache, successful solver, semantic consistency,
fuel, or solution witness is a premise. This is not the two-sided branching
solver: it does not classify conflicts between distinct rigid endpoints.
-/

namespace Yulang.PresenceConstructorBounds

open PresenceLayers (Layer)
open PresenceRegularCoalescing (Graph Edge Closed coalesceGraph)
open PresenceMaskedCoalescing (Models Realizes NodeSubtype observeMasked)
open PresenceFlowSaturation (saturate)
open PresenceRegularObservations (observe)
open SourceDataRuntime (Value)

universe u v
variable {n : Nat} {Index : Type u} {Target : Type v}

/-- Lower bounds and variable flow; no edge targets a rigid node. -/
def LowerOnly (graph : Graph n) (constraints : List (Edge n)) : Prop :=
  ∀ edge ∈ constraints, graph edge.2 = none

/-- Upper bounds and variable flow; no edge starts at a rigid node. -/
def UpperOnly (graph : Graph n) (constraints : List (Edge n)) : Prop :=
  ∀ edge ∈ constraints, graph edge.1 = none

/-- A syntactic input condition, independent of the saturation output. -/
def OneSided (graph : Graph n) (constraints : List (Edge n)) : Prop :=
  LowerOnly graph constraints ∨ UpperOnly graph constraints

instance (graph : Graph n) (constraints : List (Edge n)) :
    Decidable (LowerOnly graph constraints) := inferInstanceAs
  (Decidable (∀ edge ∈ constraints, graph edge.2 = none))

instance (graph : Graph n) (constraints : List (Edge n)) :
    Decidable (UpperOnly graph constraints) := inferInstanceAs
  (Decidable (∀ edge ∈ constraints, graph edge.1 = none))

instance (graph : Graph n) (constraints : List (Edge n)) :
    Decidable (OneSided graph constraints) := inferInstanceAs
  (Decidable (LowerOnly graph constraints ∨ UpperOnly graph constraints))

theorem lower_saturate (graph : Graph n) (constraints : List (Edge n))
    (oneSided : LowerOnly graph constraints) : LowerOnly graph (saturate graph constraints) := by
  intro edge member
  have derived := PresenceFlowSaturation.saturate_consequence graph constraints edge member
  clear member
  induction derived with
  | input member => exact oneSided _ member
  | through _ _ _ _ last => exact last

theorem upper_saturate (graph : Graph n) (constraints : List (Edge n))
    (oneSided : UpperOnly graph constraints) : UpperOnly graph (saturate graph constraints) := by
  intro edge member
  have derived := PresenceFlowSaturation.saturate_consequence graph constraints edge member
  clear member
  induction derived with
  | input member => exact oneSided _ member
  | through _ _ _ first _ => exact first

/-- The actual computed finite cache is closed for every one-sided problem,
including graphs with cyclic constructor payloads. -/
theorem saturate_closed (graph : Graph n) (constraints : List (Edge n))
    (oneSided : OneSided graph constraints) : Closed graph constraints (saturate graph constraints) where
  inputs := fun _ member => PresenceFlowSaturation.saturate_contains graph constraints member
  propagate := PresenceFlowSaturation.saturate_variable_closed graph constraints
  rigid := by
    intro source target left right first last member
    rcases oneSided with lower | upper
    · have impossible := lower_saturate graph constraints lower (source, target) member
      rw [last] at impossible
      cases impossible
    · have impossible := upper_saturate graph constraints upper (source, target) member
      rw [first] at impossible
      cases impossible

/-- Every free regular parameter graph and every free root layer assignment
produce an independent all-mask solution of every one-sided input. -/
theorem coalesce_satisfies (graph : Graph n) (constraints : List (Edge n))
    (oneSided : OneSided graph constraints)
    (parameterGraph : PresenceRegularObservations.Graph Index)
    (parameter : Fin n → Layer Index) :
    Models graph constraints
      (coalesceGraph graph (saturate graph constraints) parameterGraph parameter) Sum.inl :=
  PresenceMaskedCoalescing.coalesceGraph_satisfies graph constraints (saturate graph constraints)
    (saturate_closed graph constraints oneSided) parameterGraph parameter

/-- Independent constructor equations and input inequalities are invariant
under pointwise equivalence at all depths and outer masks. -/
theorem models_transport (graph : Graph n) (constraints : List (Edge n))
    (source : PresenceRegularObservations.Graph Index)
    (target : PresenceRegularObservations.Graph Target)
    (sourceValue : Fin n → Index) (targetValue : Fin n → Target)
    (same : ∀ index depth hidden item,
      observeMasked source depth hidden (sourceValue index) item ↔
        observeMasked target depth hidden (targetValue index) item)
    (model : Models graph constraints source sourceValue) :
    Models graph constraints target targetValue := by
  constructor
  · intro index layer rigid depth hidden item
    rw [← same index (depth + 1) hidden item, model.1 index layer rigid depth hidden item]
    apply Layer.meaning_congr
    intro child value
    simpa only [PresenceMaskedCoalescing.observeMasked_nil] using same child depth [] value
  · intro edge member depth hidden item valid
    exact (same edge.2 depth hidden item).mp
      (model.2 edge member depth hidden item ((same edge.1 depth hidden item).mpr valid))

/-- One-sided problems always have an independently checked regular model.
This is a theorem for all inputs of the syntactic fragment, not a condition
used to restrict that fragment. -/
theorem satisfiable (graph : Graph n) (constraints : List (Edge n))
    (oneSided : OneSided graph constraints) :
    ∃ original : PresenceRegularObservations.Graph (Fin n ⊕ Unit),
      Models graph constraints original Sum.inl :=
  ⟨coalesceGraph graph (saturate graph constraints) (fun _ : Unit => .bottom) (fun _ => .top),
    coalesce_satisfies graph constraints oneSided _ _⟩

/-- For every one-sided finite problem and every independent regular slot
assignment, satisfying the original problem is equivalent to membership in
the full coalesced free-parameter family. Every original slot is compared in
both directions at every depth and mask. -/
theorem models_exact (graph : Graph n) (constraints : List (Edge n))
    (oneSided : OneSided graph constraints)
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index) :
    Models graph constraints original value ↔
      ∃ parameter : Fin n → Layer Index, ∀ index,
        NodeSubtype (coalesceGraph graph (saturate graph constraints) original parameter)
          (.inl index) (.inr (value index)) ∧
        NodeSubtype (coalesceGraph graph (saturate graph constraints) original parameter)
          (.inr (value index)) (.inl index) := by
  constructor
  · intro model
    exact ⟨fun index => original (value index),
      PresenceFlowSaturation.coalesce_saturated_retraction graph constraints original value model⟩
  · rintro ⟨parameter, equivalent⟩
    apply models_transport graph constraints
      (coalesceGraph graph (saturate graph constraints) original parameter) original Sum.inl value
    · intro index depth hidden item
      have embedded := PresenceMaskedCoalescing.parameter_embedding graph (saturate graph constraints)
        original parameter depth hidden (value index) item
      exact ⟨fun valid => embedded.mp ((equivalent index).1 depth hidden item valid),
        fun valid => (equivalent index).2 depth hidden item (embedded.mpr valid)⟩
    · exact coalesce_satisfies graph constraints oneSided original parameter

namespace Examples

/-- A recursive pair/record payload with a lower bound on its free node. -/
def recursiveLower : Graph 3 := fun index =>
  if index = 0 then none else if index = 1 then some (.pair 0 2)
  else some (.required 7 0)

theorem recursive_lower_oneSided : OneSided recursiveLower [(1, 0), (2, 0)] := by
  apply Or.inl
  intro edge member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem recursive_lower_closed :
    Closed recursiveLower [(1, 0), (2, 0)] (saturate recursiveLower [(1, 0), (2, 0)]) :=
  saturate_closed _ _ recursive_lower_oneSided

theorem recursive_lower_all_parameters (parameterGraph : PresenceRegularObservations.Graph Index)
    (parameter : Fin 3 → Layer Index) :
    Models recursiveLower [(1, 0), (2, 0)]
      (coalesceGraph recursiveLower (saturate recursiveLower [(1, 0), (2, 0)]) parameterGraph parameter) Sum.inl :=
  coalesce_satisfies _ _ recursive_lower_oneSided parameterGraph parameter

end Examples

end Yulang.PresenceConstructorBounds
