import Yulang.PresenceBoundCoalescing
import Yulang.PresenceRegularObservations

/-!
# Guarded regular coalescing of presence demands

The constructor graph distinguishes unconstrained variables from finite
presence layers. A closed cache carries finite, one-layer derivations between
its rigid endpoints. Those derivations are sound for arbitrary child predicates;
they are not hypotheses that a regular solution exists. Coalescing then works
for every external regular parameter graph and every parameter layer.

The independent-solution retraction uses the same observation depth for external
parameters and generated nodes. It recovers every original slot, including shared
slots. Equal recovered children can be placed under the same arbitrary masked
output-layer context. This does not recover separately masked original slot
roots; that stronger statement requires mask-indexed solution hypotheses.
No least-solution assumption or finite catalogue of parameters is used.

This module does not compute a closed cache. Completeness of a finite presence
inspector, unguarded open-tail references, functions and rows remain separate
obligations. The proof certificates below are sound, not asserted complete.
-/

namespace Yulang.PresenceRegularCoalescing

open PresenceLayers (Layer)
open PresenceDataTypes (Ty Le)
open PresenceRegularObservations (observe)
open LayerBoundTemplates (Constraint Problem Reaches)
open SourceDataRuntime (Value)

universe u v
variable {n : Nat}

abbrev Edge (n : Nat) := Fin n × Fin n
abbrev Graph (n : Nat) := Fin n → Option (Layer (Fin n))

/-- Finite one-layer certificates. Child obligations refer to the cache;
the rules retain optionality, absence and the whole lattice expression. -/
inductive Derives (cache : List (Edge n)) : Layer (Fin n) → Layer (Fin n) → Prop where
  | refl (layer) : Derives cache layer layer
  | bottom (layer) : Derives cache .bottom layer
  | top (layer) : Derives cache layer .top
  | trans : Derives cache left middle → Derives cache middle right → Derives cache left right
  | unionLeft (left right) : Derives cache left (.union left right)
  | unionRight (left right) : Derives cache right (.union left right)
  | unionElim : Derives cache left target → Derives cache right target →
      Derives cache (.union left right) target
  | interLeft (left right) : Derives cache (.inter left right) left
  | interRight (left right) : Derives cache (.inter left right) right
  | interIntro : Derives cache source left → Derives cache source right →
      Derives cache source (.inter left right)
  | pair : (first, first') ∈ cache → (last, last') ∈ cache →
      Derives cache (.pair first last) (.pair first' last')
  | variant : (first, last) ∈ cache → Derives cache (.variant label first) (.variant label last)
  | required : (first, last) ∈ cache → Derives cache (.required label first) (.required label last)
  | optional : (first, last) ∈ cache → Derives cache (.optional label first) (.optional label last)
  | requiredOptional (label payload) : Derives cache (.required label payload) (.optional label payload)
  | lacksOptional (label payload) : Derives cache (.lacks label) (.optional label payload)
  | requiredRecords (label payload) : Derives cache (.required label payload) .records
  | optionalRecords (label payload) : Derives cache (.optional label payload) .records
  | lacksRecords (label) : Derives cache (.lacks label) .records
  | optionalSplit (label payload) :
      Derives cache (.optional label payload) (.union (.lacks label) (.required label payload))

theorem Derives.sound {cache : List (Edge n)} {left right : Layer (Fin n)}
    (derivation : Derives cache left right) (assignment : Fin n → Ty)
    (children : ∀ edge ∈ cache, Le (assignment edge.1) (assignment edge.2)) :
    Le (left.denote assignment) (right.denote assignment) := by
  induction derivation with
  | refl => exact PresenceDataTypes.le_refl _
  | bottom => exact fun _ valid => False.elim valid
  | top => exact fun _ _ => trivial
  | trans _ _ first last => exact PresenceDataTypes.le_trans first last
  | unionLeft => exact fun _ valid => Or.inl valid
  | unionRight => exact fun _ valid => Or.inr valid
  | unionElim _ _ first last => exact fun item valid => valid.elim (first item) (last item)
  | interLeft => exact fun _ valid => valid.1
  | interRight => exact fun _ valid => valid.2
  | interIntro _ _ first last => exact fun item valid => ⟨first item valid, last item valid⟩
  | pair first last =>
      intro item valid
      cases item with
      | pair a b => exact ⟨children _ first _ valid.1, children _ last _ valid.2⟩
      | _ => cases valid
  | variant child =>
      intro item valid
      cases item with
      | variant label payload => exact ⟨valid.1, children _ child _ valid.2⟩
      | _ => cases valid
  | required child =>
      rintro item ⟨record, payload, found, valid⟩
      exact ⟨record, payload, found, children _ child _ valid⟩
  | optional child =>
      rintro item ⟨record, valid⟩
      exact ⟨record, fun payload found => children _ child _ (valid payload found)⟩
  | requiredOptional => exact PresenceDataTypes.required_optional _ _
  | lacksOptional => exact PresenceDataTypes.lacks_optional _ _
  | requiredRecords | optionalRecords | lacksRecords => exact fun _ valid => valid.1
  | optionalSplit label payload =>
      rintro item ⟨record, valid⟩
      cases found : PresenceDataTypes.lookup label item with
      | none => exact Or.inl ⟨record, found⟩
      | some value => exact Or.inr ⟨record, value, found, valid value found⟩

/-- Closure is a finite, checkable certificate form. No semantic regular
valuation or arbitrary-parameter satisfaction property occurs in its fields. -/
structure Closed (graph : Graph n) (constraints cache : List (Edge n)) : Prop where
  inputs : ∀ edge ∈ constraints, edge ∈ cache
  propagate : ∀ middle, graph middle = none → ∀ source target,
    (source, middle) ∈ cache → (middle, target) ∈ cache → (source, target) ∈ cache
  rigid : ∀ source target left right, graph source = some left → graph target = some right →
    (source, target) ∈ cache → Derives cache left right

def edgeTemplate (graph : Graph n) (edge : Edge n) : Constraint n (Layer (Fin n)) :=
  match graph edge.1, graph edge.2 with
  | none, none => .flow edge.1 edge.2
  | none, some right => .upper edge.1 right
  | some left, none => .lower left edge.2
  | some left, some right => .check left right

def template (graph : Graph n) (cache : List (Edge n)) : Problem n (Layer (Fin n)) :=
  cache.map (edgeTemplate graph)

theorem mem_template_flow (graph : Graph n) (cache : List (Edge n)) (source target : Fin n) :
    .flow source target ∈ template graph cache ↔
      (source, target) ∈ cache ∧ graph source = none ∧ graph target = none := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    cases left : graph a <;> cases right : graph b <;> simp only [edgeTemplate, left, right] at same
    · obtain ⟨rfl, rfl⟩ := Constraint.flow.inj same
      exact ⟨present, left, right⟩
    all_goals cases same
  · rintro ⟨present, left, right⟩
    exact List.mem_map.mpr ⟨(source, target), present, by simp [edgeTemplate, left, right]⟩

theorem mem_template_lower (graph : Graph n) (cache : List (Edge n))
    (bound : Layer (Fin n)) (target : Fin n) :
    .lower bound target ∈ template graph cache ↔
      ∃ source, (source, target) ∈ cache ∧ graph source = some bound ∧ graph target = none := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    cases left : graph a <;> cases right : graph b <;> simp only [edgeTemplate, left, right] at same
    case some.none layer =>
      obtain ⟨rfl, rfl⟩ := Constraint.lower.inj same
      exact ⟨a, present, left, right⟩
    all_goals cases same
  · rintro ⟨source, present, left, right⟩
    exact List.mem_map.mpr ⟨(source, target), present, by simp [edgeTemplate, left, right]⟩

theorem mem_template_upper (graph : Graph n) (cache : List (Edge n))
    (source : Fin n) (bound : Layer (Fin n)) :
    .upper source bound ∈ template graph cache ↔
      ∃ target, (source, target) ∈ cache ∧ graph source = none ∧ graph target = some bound := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    cases left : graph a <;> cases right : graph b <;> simp only [edgeTemplate, left, right] at same
    case none.some layer =>
      obtain ⟨rfl, rfl⟩ := Constraint.upper.inj same
      exact ⟨b, present, left, right⟩
    all_goals cases same
  · rintro ⟨target, present, left, right⟩
    exact List.mem_map.mpr ⟨(source, target), present, by simp [edgeTemplate, left, right]⟩

theorem mem_template_check (graph : Graph n) (cache : List (Edge n))
    (left right : Layer (Fin n)) :
    .check left right ∈ template graph cache ↔
      ∃ source target, (source, target) ∈ cache ∧ graph source = some left ∧ graph target = some right := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    cases source : graph a <;> cases target : graph b <;> simp only [edgeTemplate, source, target] at same
    case some.some first last =>
      obtain ⟨rfl, rfl⟩ := Constraint.check.inj same
      exact ⟨a, b, present, source, target⟩
    all_goals cases same
  · rintro ⟨source, target, present, first, last⟩
    exact List.mem_map.mpr ⟨(source, target), present, by simp [edgeTemplate, first, last]⟩

private theorem mem_successors (problem : Problem n (Layer (Fin n))) (source target : Fin n) :
    target ∈ LayerBoundTemplates.successors problem source ↔ .flow source target ∈ problem := by
  have same := LayerBoundTemplates.successors_instantiateWith
    (fun _ : Layer (Fin n) => (StructuralBase.Ty.bottom : StructuralBase.Ty Unit)) problem source
  rw [← same, ValueBounds.mem_successors, LayerBoundTemplates.mem_instantiateWith_flow]

theorem path_propagates (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache) {start target : Fin n}
    (path : Reaches (template graph cache) start target) :
    ∀ source, (source, start) ∈ cache → (source, target) ∈ cache := by
  induction path with
  | nil => exact fun _ present => present
  | @cons start middle target edge _ ih =>
      obtain ⟨present, variableNode, _⟩ := (mem_template_flow graph cache start middle).mp
        ((mem_successors _ start middle).mp edge)
      exact fun source lower => ih source (closed.propagate start variableNode source middle lower present)

theorem lower_models (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache) (assignment : Fin n → Ty)
    (children : ∀ edge ∈ cache, Le (assignment edge.1) (assignment edge.2)) :
    PresenceBoundCoalescing.Models (fun layer => layer.denote assignment) (template graph cache)
      (PresenceBoundCoalescing.lower (fun layer => layer.denote assignment) (template graph cache)) := by
  intro constraint member
  cases constraint with
  | lower bound target => exact PresenceBoundCoalescing.lower_lower _ _ bound target member
  | flow source target => exact PresenceBoundCoalescing.lower_flow _ _ source target member
  | upper source bound =>
      obtain ⟨target, upperEdge, variableNode, rigid⟩ := (mem_template_upper graph cache source bound).mp member
      rintro value ⟨lower, lowerMember, valid⟩
      obtain ⟨start, seed, path⟩ :=
        (PresenceBoundCoalescing.mem_lowerBounds (template graph cache) source lower).mp lowerMember
      obtain ⟨origin, lowerEdge, originRigid, _⟩ := (mem_template_lower graph cache lower start).mp seed
      have propagated := path_propagates graph constraints cache closed path origin lowerEdge
      exact (closed.rigid origin target lower bound originRigid rigid
        (closed.propagate source variableNode origin target propagated upperEdge)).sound assignment children value valid
  | check left right =>
      obtain ⟨source, target, edge, first, last⟩ := (mem_template_check graph cache left right).mp member
      exact (closed.rigid source target left right first last edge).sound assignment children

def nodeValues (graph : Graph n) (assignment variables : Fin n → Ty) (index : Fin n) : Ty :=
  match graph index with
  | none => variables index
  | some layer => layer.denote assignment

theorem template_models_edges (graph : Graph n) (cache : List (Edge n))
    (assignment variables : Fin n → Ty)
    (model : PresenceBoundCoalescing.Models (fun layer => layer.denote assignment)
      (template graph cache) variables) :
    ∀ edge ∈ cache, Le (nodeValues graph assignment variables edge.1)
      (nodeValues graph assignment variables edge.2) := by
  intro edge present
  have valid := model _ (List.mem_map.mpr ⟨edge, present, rfl⟩)
  cases left : graph edge.1 <;> cases right : graph edge.2 <;>
    simpa only [edgeTemplate, left, right, PresenceBoundCoalescing.Holds, nodeValues] using valid

theorem template_models_of_edges (graph : Graph n) (cache : List (Edge n))
    (assignment value : Fin n → Ty)
    (realizes : ∀ index layer, graph index = some layer → ∀ item,
      layer.denote assignment item ↔ value index item)
    (edges : ∀ edge ∈ cache, Le (value edge.1) (value edge.2)) :
    PresenceBoundCoalescing.Models (fun layer => layer.denote assignment)
      (template graph cache) value := by
  intro constraint member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  cases left : graph edge.1 <;> cases right : graph edge.2 <;>
    simp only [edgeTemplate, left, right, PresenceBoundCoalescing.Holds]
  · exact edges edge present
  · intro item valid
    exact (realizes edge.2 _ right item).mpr (edges edge present item valid)
  · intro item valid
    exact edges edge present item ((realizes edge.1 _ left item).mp valid)
  · intro item valid
    exact (realizes edge.2 _ right item).mpr
      (edges edge present item ((realizes edge.1 _ left item).mp valid))

private theorem joinMapped_exact {Bound : Type u} {Index : Type v}
    (body : Bound → Layer Index) (assignment : Index → Ty) (hidden : List Nat)
    (bounds : List Bound) (item : Value) :
    (PresenceBoundCoalescing.joinLayers (bounds.map body)).meaning assignment hidden item ↔
      ∃ bound ∈ bounds, (body bound).meaning assignment hidden item := by
  induction bounds with
  | nil => simp [PresenceBoundCoalescing.joinLayers, Layer.meaning, PresenceDataTypes.never]
  | cons bound rest ih =>
      simp [PresenceBoundCoalescing.joinLayers, Layer.meaning, PresenceDataTypes.union, ih]

private theorem meetMapped_exact {Bound : Type u} {Index : Type v}
    (body : Bound → Layer Index) (assignment : Index → Ty) (hidden : List Nat)
    (bounds : List Bound) (item : Value) :
    (PresenceBoundCoalescing.meetLayers (bounds.map body)).meaning assignment hidden item ↔
      ∀ bound ∈ bounds, (body bound).meaning assignment hidden item := by
  induction bounds with
  | nil => simp [PresenceBoundCoalescing.meetLayers, Layer.meaning, PresenceDataTypes.any]
  | cons bound rest ih =>
      simp [PresenceBoundCoalescing.meetLayers, Layer.meaning, PresenceDataTypes.inter, ih]

/-- Keep the finite topology fixed while embedding bounds and parameters into
the same graph. External parameters are not unfolded or truncated here. -/
def expandLayer {Bound : Type u} {Index : Type v} (problem : Problem n Bound)
    (body : Bound → Layer Index) (parameters : Fin n → Layer Index) (target : Fin n) : Layer Index :=
  .union (PresenceBoundCoalescing.joinLayers ((LayerBoundTemplates.lowerBounds problem target).map body))
    (PresenceBoundCoalescing.joinLayers ((LayerBoundTemplates.ancestors problem target).map fun source =>
      .inter (parameters source)
        (PresenceBoundCoalescing.meetLayers ((LayerBoundTemplates.upperBounds problem source).map body))))

theorem expandLayer_exact {Bound : Type u} {Index : Type v} (problem : Problem n Bound)
    (body : Bound → Layer Index) (parameters : Fin n → Layer Index)
    (assignment : Index → Ty) (hidden : List Nat) (target : Fin n) (item : Value) :
    (expandLayer problem body parameters target).meaning assignment hidden item ↔
      PresenceBoundCoalescing.expand (fun bound => (body bound).meaning assignment hidden) problem
        (fun index => (parameters index).meaning assignment hidden) target item := by
  simp [expandLayer, Layer.meaning, PresenceDataTypes.union, PresenceDataTypes.inter,
    joinMapped_exact, meetMapped_exact, LayerBoundTemplates.mem_ancestors,
    PresenceBoundCoalescing.expand, PresenceBoundCoalescing.lower, PresenceBoundCoalescing.upper]

variable {ParameterState : Type u}

def coalesceGraph (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) : PresenceRegularObservations.Graph (Fin n ⊕ ParameterState)
  | .inl index =>
      match graph index with
      | none => expandLayer (template graph cache) (Layer.map Sum.inl)
          (fun index => (parameter index).map Sum.inr) index
      | some layer => layer.map Sum.inl
  | .inr state => (parameterGraph state).map Sum.inr

theorem coalesceGraph_eval (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) (assignment : Fin n ⊕ ParameterState → Ty)
    (index : Fin n) (item : Value) :
    (coalesceGraph graph cache parameterGraph parameter (.inl index)).denote assignment item ↔
      nodeValues graph (fun child => assignment (.inl child))
        (PresenceBoundCoalescing.expand
          (fun layer => layer.denote (fun child => assignment (.inl child))) (template graph cache)
          (fun child => (parameter child).denote (fun state => assignment (.inr state)))) index item := by
  cases shape : graph index with
  | none =>
      simpa only [coalesceGraph, nodeValues, shape, Layer.meaning_map, Layer.denote] using
        (expandLayer_exact (template graph cache) (Layer.map Sum.inl)
          (fun child => (parameter child).map Sum.inr) assignment [] index item)
  | some layer => simp only [coalesceGraph, nodeValues, shape, Layer.denote_map]

theorem parameter_embedding (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) (depth : Nat) (state : ParameterState) (item : Value) :
    observe (coalesceGraph graph cache parameterGraph parameter) depth (.inr state) item ↔
      observe parameterGraph depth state item :=
  PresenceRegularObservations.observe_morphism parameterGraph _ Sum.inr (fun _ => rfl) depth state item

theorem coalesceGraph_rigid (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) (index : Fin n) (layer : Layer (Fin n))
    (rigid : graph index = some layer) :
    coalesceGraph graph cache parameterGraph parameter (.inl index) = layer.map Sum.inl := by
  simp only [coalesceGraph, rigid]

def NodeSubtype {Index : Type u} (graph : PresenceRegularObservations.Graph Index)
    (left right : Index) : Prop :=
  PresenceRegularObservations.DataSubtype graph (graph left) (graph right)

/-- Constructor equations are independent all-depth observations, not an
equation saying that a node is the result of coalescing itself. -/
def Realizes {Index : Type u} (graph : Graph n) (original : PresenceRegularObservations.Graph Index)
    (value : Fin n → Index) : Prop :=
  ∀ index layer, graph index = some layer → ∀ depth item,
    observe original (depth + 1) (value index) item ↔
      layer.denote (fun child => observe original depth (value child)) item

def Models {Index : Type u} (graph : Graph n) (constraints : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index) : Prop :=
  Realizes graph original value ∧ ∀ edge ∈ constraints, NodeSubtype original (value edge.1) (value edge.2)

theorem coalesceGraph_realizes (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) :
    Realizes graph (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  intro index layer rigid depth item
  simp only [observe, coalesceGraph_rigid graph cache parameterGraph parameter index layer rigid,
    Layer.denote_map]

theorem coalesceGraph_edges_step (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache)
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) (depth : Nat)
    (children : ∀ edge ∈ cache, Le
      (observe (coalesceGraph graph cache parameterGraph parameter) depth (.inl edge.1))
      (observe (coalesceGraph graph cache parameterGraph parameter) depth (.inl edge.2))) :
    ∀ edge ∈ cache, Le
      (observe (coalesceGraph graph cache parameterGraph parameter) (depth + 1) (.inl edge.1))
      (observe (coalesceGraph graph cache parameterGraph parameter) (depth + 1) (.inl edge.2)) := by
  let generated := coalesceGraph graph cache parameterGraph parameter
  let assignment := fun child => observe generated depth (.inl child)
  let parameters := fun child => (parameter child).denote (fun state => observe generated depth (.inr state))
  have flat := PresenceBoundCoalescing.expand_satisfies
    (lower_models graph constraints cache closed assignment children) parameters
  have edges := template_models_edges graph cache assignment _ flat
  intro edge member item valid
  exact (coalesceGraph_eval graph cache parameterGraph parameter (observe generated depth) edge.2 item).mpr
    (edges edge member item
      ((coalesceGraph_eval graph cache parameterGraph parameter (observe generated depth) edge.1 item).mp valid))

/-- Every free regular parameter graph and every parameter layer yield a
model of the cache. No independent solution is assumed. -/
theorem coalesceGraph_satisfies_cache (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache)
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) :
    Models graph cache (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  refine ⟨coalesceGraph_realizes graph cache parameterGraph parameter, ?_⟩
  have allDepths : ∀ depth, ∀ edge ∈ cache, Le
      (observe (coalesceGraph graph cache parameterGraph parameter) depth (.inl edge.1))
      (observe (coalesceGraph graph cache parameterGraph parameter) depth (.inl edge.2)) := by
    intro depth
    induction depth with
    | zero => exact fun _ _ _ valid => False.elim valid
    | succ depth ih => exact coalesceGraph_edges_step graph constraints cache closed parameterGraph parameter depth ih
  exact fun edge member depth => allDepths (depth + 1) edge member

/-- The original constructor equations and input constraints are satisfied
for every free parameter assignment after a closed cache is supplied. -/
theorem coalesceGraph_satisfies (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache)
    (parameterGraph : PresenceRegularObservations.Graph ParameterState)
    (parameter : Fin n → Layer ParameterState) :
    Models graph constraints (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  have model := coalesceGraph_satisfies_cache graph constraints cache closed parameterGraph parameter
  exact ⟨model.1, fun edge member => model.2 edge (closed.inputs edge member)⟩

/-- Substituting an independent solution for the parameters recovers every
original observation. No closure certificate is required for this direction;
the independent solution must satisfy the cache, not only the input list. -/
theorem coalesceGraph_retract_at (graph : Graph n) (cache : List (Edge n))
    (original : PresenceRegularObservations.Graph ParameterState) (value : Fin n → ParameterState)
    (realizes : Realizes graph original value)
    (edges : ∀ edge ∈ cache, NodeSubtype original (value edge.1) (value edge.2)) (depth : Nat) :
    ∀ index item,
      observe (coalesceGraph graph cache original (fun index => original (value index))) depth (.inl index) item ↔
        observe original depth (value index) item := by
  induction depth with
  | zero => exact fun _ _ => Iff.rfl
  | succ depth ih =>
      let generated := coalesceGraph graph cache original (fun index => original (value index))
      let child := fun index => observe generated depth (.inl index)
      let originalChild := fun index => observe original depth (value index)
      let current := fun index => observe original (depth + 1) (value index)
      have rigidEquivalent : ∀ index layer, graph index = some layer → ∀ item,
          layer.denote child item ↔ current index item := by
        intro index layer rigid item
        exact (Layer.meaning_congr child originalChild ih [] layer item).trans
          (realizes index layer rigid depth item).symm
      have currentEdges : ∀ edge ∈ cache, Le (current edge.1) (current edge.2) :=
        fun edge member => edges edge member depth
      have flatModel := template_models_of_edges graph cache child current rigidEquivalent currentEdges
      have parameterEq : (fun index => (original (value index)).denote
          (fun state => observe generated depth (.inr state))) = current := by
        funext index item
        apply propext
        exact Layer.meaning_congr _ _
          (parameter_embedding graph cache original (fun index => original (value index)) depth)
          [] (original (value index)) item
      intro index item
      change (generated (.inl index)).denote (observe generated depth) item ↔ current index item
      rw [coalesceGraph_eval]
      cases shape : graph index with
      | none =>
          simp only [nodeValues, shape]
          rw [parameterEq]
          exact PresenceBoundCoalescing.expand_retraction flatModel index item
      | some layer =>
          simp only [nodeValues, shape]
          exact rigidEquivalent index layer shape item

/-- Every independent cached solution is recovered in both data-subtype
directions at every original slot. Shared references use the same parameter
graph and are never copied into independently chosen payload parameters. -/
theorem coalesceGraph_retraction (graph : Graph n) (cache : List (Edge n))
    (original : PresenceRegularObservations.Graph ParameterState) (value : Fin n → ParameterState)
    (model : Models graph cache original value) :
    ∀ index,
      NodeSubtype (coalesceGraph graph cache original (fun index => original (value index)))
        (.inl index) (.inr (value index)) ∧
      NodeSubtype (coalesceGraph graph cache original (fun index => original (value index)))
        (.inr (value index)) (.inl index) := by
  intro index
  constructor <;> intro depth item valid
  · exact (parameter_embedding graph cache original (fun index => original (value index))
      (depth + 1) (value index) item).mpr
        ((coalesceGraph_retract_at graph cache original value model.1 model.2
          (depth + 1) index item).mp valid)
  · exact (coalesceGraph_retract_at graph cache original value model.1 model.2
      (depth + 1) index item).mpr
        ((parameter_embedding graph cache original (fun index => original (value index))
          (depth + 1) (value index) item).mp valid)

/-- Recovered children may be placed under the same finite output layer and
mask on both sides. This is context congruence; it does not compare the mask
of a generated slot's own root with the mask of its independent source root.
Unmasked `Models` alone is insufficient for that stronger claim. -/
theorem coalesceGraph_mask_retraction (graph : Graph n) (cache : List (Edge n))
    (original : PresenceRegularObservations.Graph ParameterState) (value : Fin n → ParameterState)
    (model : Models graph cache original value) (depth : Nat) (hidden : List Nat)
    (layer : Layer (Fin n)) (item : Value) :
    (layer.map Sum.inl).meaning
        (observe (coalesceGraph graph cache original (fun index => original (value index))) depth)
        hidden item ↔
      (layer.map value).meaning (observe original depth) hidden item := by
  simp only [Layer.meaning_map]
  exact Layer.meaning_congr _ _
    (coalesceGraph_retract_at graph cache original value model.1 model.2 depth) hidden layer item

end Yulang.PresenceRegularCoalescing
