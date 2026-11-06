import Yulang.LayerBoundTemplates
import Yulang.RigidValueLayers
import Yulang.RegularNestedModels

/-!
# Constructing regular solutions of nested value constraints

Variable-only paths are compiled to finite lattice layers. Constructor children
remain guarded graph references, so negative occurrences do not require a
monotone least fixed point. Every free parameter is a shared regular type graph,
grafted into the result at the same observation depth as the generated graph.

The construction uses the all-solution expansion from `ValueBoundSchemes` at
each finite observation. It is distinct from a single least solution and from
the signed least-fixed-point semantics of effect rows.
-/

namespace Yulang.RegularValueCoalescing

open RegularValueTypes
open RigidValueLayers (rigidLayer)


universe u v

variable {n : Nat} {Row : Type u} {ParameterState : Type v}

def isVar : NestedValueSolver.Node n Row → Bool
  | .var => true
  | _ => false

@[simp] theorem isVar_iff (node : NestedValueSolver.Node n Row) : isVar node = true ↔ node = .var := by
  cases node <;> simp [isVar]

/-- Only variable-to-variable edges contribute to the flat flow topology. -/
def edgeTemplate (graph : NestedValueSolver.Graph n Row) (edge : NestedValueSolver.Edge n) :
    LayerBoundTemplates.Constraint n (Layer Row (Fin n)) :=
  if isVar (graph edge.1) then
    if isVar (graph edge.2) then .flow edge.1 edge.2
    else .upper edge.1 (rigidLayer (graph edge.2))
  else
    if isVar (graph edge.2) then .lower (rigidLayer (graph edge.1)) edge.2
    else .check (rigidLayer (graph edge.1)) (rigidLayer (graph edge.2))

def template (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n)) :
    LayerBoundTemplates.Problem n (Layer Row (Fin n)) := cache.map (edgeTemplate graph)

theorem mem_template_flow (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (source target : Fin n) :
    .flow source target ∈ template graph cache ↔
      (source, target) ∈ cache ∧ graph source = .var ∧ graph target = .var := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    simp only [edgeTemplate] at same
    split at same
    · rename_i left
      split at same
      · rename_i right
        obtain ⟨rfl, rfl⟩ := LayerBoundTemplates.Constraint.flow.inj same
        exact ⟨present, (isVar_iff _).mp left, (isVar_iff _).mp right⟩
      · cases same
    · split at same <;> cases same
  · rintro ⟨present, left, right⟩
    exact List.mem_map.mpr ⟨(source, target), present,
      by simp [edgeTemplate, left, right, isVar]⟩

theorem mem_template_lower (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (bound : Layer Row (Fin n)) (target : Fin n) :
    .lower bound target ∈ template graph cache ↔
      ∃ source, (source, target) ∈ cache ∧ graph source ≠ .var ∧
        graph target = .var ∧ rigidLayer (graph source) = bound := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    simp only [edgeTemplate] at same
    split at same
    · split at same <;> cases same
    · rename_i left
      split at same
      · rename_i right
        obtain ⟨boundEqual, rfl⟩ := LayerBoundTemplates.Constraint.lower.inj same
        exact ⟨a, present, fun equal => left ((isVar_iff _).mpr equal),
          (isVar_iff _).mp right, boundEqual⟩
      · cases same
  · rintro ⟨source, present, left, right, rfl⟩
    exact List.mem_map.mpr ⟨(source, target), present,
      by simp [edgeTemplate, right, isVar]⟩

theorem mem_template_upper (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (source : Fin n) (bound : Layer Row (Fin n)) :
    .upper source bound ∈ template graph cache ↔
      ∃ target, (source, target) ∈ cache ∧ graph source = .var ∧
        graph target ≠ .var ∧ rigidLayer (graph target) = bound := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    simp only [edgeTemplate] at same
    split at same
    · rename_i left
      split at same
      · cases same
      · rename_i right
        obtain ⟨rfl, boundEqual⟩ := LayerBoundTemplates.Constraint.upper.inj same
        exact ⟨b, present, (isVar_iff _).mp left,
          fun equal => right ((isVar_iff _).mpr equal), boundEqual⟩
    · split at same <;> cases same
  · rintro ⟨target, present, left, right, rfl⟩
    exact List.mem_map.mpr ⟨(source, target), present,
      by simp [edgeTemplate, left, isVar]⟩

theorem mem_template_check (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (left right : Layer Row (Fin n)) :
    .check left right ∈ template graph cache ↔
      ∃ source target, (source, target) ∈ cache ∧ graph source ≠ .var ∧
        graph target ≠ .var ∧ rigidLayer (graph source) = left ∧
        rigidLayer (graph target) = right := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, present, same⟩ := List.mem_map.mp member
    simp only [edgeTemplate] at same
    split at same
    · split at same <;> cases same
    · rename_i leftRigid
      split at same
      · cases same
      · rename_i rightRigid
        obtain ⟨leftEqual, rightEqual⟩ := LayerBoundTemplates.Constraint.check.inj same
        exact ⟨a, b, present, fun equal => leftRigid ((isVar_iff _).mpr equal),
          fun equal => rightRigid ((isVar_iff _).mpr equal), leftEqual, rightEqual⟩
  · rintro ⟨source, target, present, leftRigid, rightRigid, rfl, rfl⟩
    exact List.mem_map.mpr ⟨(source, target), present,
      by simp [edgeTemplate, isVar]⟩

/-- A lower bound traversing a flat flow path is already present in a cache
closed under variable propagation. No constructor transitivity is assumed. -/
theorem path_propagates (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (closed : NestedValueSolver.Closed graph constraints cache) (assignment : Fin n → StructuralBase.Ty Row)
    {start target : Fin n}
    (path : ValueBounds.Reaches (LayerBoundTemplates.instantiateProblem assignment (template graph cache)) start target) :
    ∀ source, (source, start) ∈ cache → (source, target) ∈ cache := by
  induction path with
  | nil => exact fun _ present => present
  | @cons start middle target edge _ ih =>
      intro source lower
      have flow := (ValueBounds.mem_successors _ start middle).mp edge
      have original := (LayerBoundTemplates.mem_instantiateProblem_flow assignment _ start middle).mp flow
      obtain ⟨present, varShape, _⟩ := (mem_template_flow graph cache start middle).mp original
      exact ih source (closed.2.2 start varShape source middle lower present)

/-- Rigid-pair consistency is the sole semantic premise needed by the flat
scheme at one observation depth. -/
theorem least_models (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (closed : NestedValueSolver.Closed graph constraints cache) (assignment : Fin n → StructuralBase.Ty Row)
    (leRow : Row → Row → Prop)
    (rigidOrdered : ∀ source target, (source, target) ∈ cache →
      graph source ≠ .var → graph target ≠ .var →
      StructuralBase.Subtype leRow ((rigidLayer (graph source)).eval assignment)
        ((rigidLayer (graph target)).eval assignment)) :
    ValueBounds.Models leRow (LayerBoundTemplates.instantiateProblem assignment (template graph cache))
      (ValueBounds.least (LayerBoundTemplates.instantiateProblem assignment (template graph cache))) := by
  intro constraint member
  cases constraint with
  | lower bound target => exact ValueBounds.least_lower leRow _ bound target member
  | flow source target => exact ValueBounds.least_flow leRow _ source target member
  | upper source bound =>
      obtain ⟨upper, upperMember, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_upper assignment _ source bound).mp member
      obtain ⟨target, edge, varShape, rigid, rfl⟩ :=
        (mem_template_upper graph cache source upper).mp upperMember
      apply (ValueBounds.joinTypes_le_iff leRow _ _).mpr
      intro lower contributes
      obtain ⟨start, seed, path⟩ := (ValueBounds.mem_lowerTypes _ source lower).mp contributes
      obtain ⟨lowerLayer, lowerMember, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_lower assignment _ lower start).mp seed
      obtain ⟨origin, lowerEdge, originRigid, _, rfl⟩ :=
        (mem_template_lower graph cache lowerLayer start).mp lowerMember
      have propagated := path_propagates graph constraints cache closed assignment path origin lowerEdge
      exact rigidOrdered origin target (closed.2.2 source varShape origin target propagated edge)
        originRigid rigid
  | check left right =>
      obtain ⟨leftLayer, rightLayer, original, rfl, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_check assignment _ left right).mp member
      obtain ⟨source, target, edge, leftRigid, rightRigid, rfl, rfl⟩ :=
        (mem_template_check graph cache leftLayer rightLayer).mp original
      exact rigidOrdered source target edge leftRigid rightRigid

/-- Reassemble a node valuation from the flat variable assignments and the
rigid constructor observations. -/
def nodeValues (graph : NestedValueSolver.Graph n Row) (assignment variables : Fin n → StructuralBase.Ty Row) :
    Fin n → StructuralBase.Ty Row := fun index =>
  if isVar (graph index) then variables index else (rigidLayer (graph index)).eval assignment

theorem template_models_edges (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (assignment variables : Fin n → StructuralBase.Ty Row) (leRow : Row → Row → Prop)
    (model : ValueBounds.Models leRow (LayerBoundTemplates.instantiateProblem assignment (template graph cache)) variables) :
    ∀ edge ∈ cache, NestedValueSolver.Edge.Holds leRow (nodeValues graph assignment variables) edge := by
  intro edge present
  have holds := model _ (List.mem_map.mpr
    ⟨edgeTemplate graph edge, List.mem_map.mpr ⟨edge, present, rfl⟩, rfl⟩)
  unfold NestedValueSolver.Edge.Holds nodeValues
  by_cases left : isVar (graph edge.1) = true
  · by_cases right : isVar (graph edge.2) = true
    · simpa [edgeTemplate, left, right, LayerBoundTemplates.Constraint.instantiateWith, ValueBounds.Constraint.Holds] using holds
    · simpa [edgeTemplate, left, right, LayerBoundTemplates.Constraint.instantiateWith, ValueBounds.Constraint.Holds] using holds
  · by_cases right : isVar (graph edge.2) = true
    · simpa [edgeTemplate, left, right, LayerBoundTemplates.Constraint.instantiateWith, ValueBounds.Constraint.Holds] using holds
    · simpa [edgeTemplate, left, right, LayerBoundTemplates.Constraint.instantiateWith, ValueBounds.Constraint.Holds] using holds

/-- A finite regular scheme. The original node identities remain shared in
both variances, and free-parameter graphs are grafted without truncation. -/
def coalesceGraph (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState) :
    Graph Row (Fin n ⊕ ParameterState)
  | .inl index =>
      if isVar (graph index) then
        LayerBoundTemplates.expandLayer (LayerBoundTemplates.mapBounds (Layer.map Sum.inl) (template graph cache))
          (fun index => (parameter index).map Sum.inr) index
      else (rigidLayer (graph index)).map Sum.inl
  | .inr index => (parameterGraph index).map Sum.inr

theorem coalesceGraph_eval (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState)
    (assignment : Fin n ⊕ ParameterState → StructuralBase.Ty Row) (index : Fin n) :
    (coalesceGraph graph cache parameterGraph parameter (.inl index)).eval assignment =
      nodeValues graph (fun i => assignment (.inl i))
        (ValueBoundSchemes.expand (LayerBoundTemplates.instantiateProblem (fun i => assignment (.inl i)) (template graph cache))
          (fun i => (parameter i).eval (fun state => assignment (.inr state)))) index := by
  simp only [coalesceGraph, nodeValues]
  split
  · rw [LayerBoundTemplates.expandLayer_eval]
    simp only [LayerBoundTemplates.instantiateProblem, LayerBoundTemplates.instantiateWith_mapBounds, Layer.eval_map,
      Function.comp_def]
  · exact Layer.eval_map _ _ _

theorem parameter_embedding (graph : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState)
    (depth : Nat) (state : ParameterState) :
    observe (coalesceGraph graph cache parameterGraph parameter) depth (.inr state) =
      observe parameterGraph depth state :=
  observe_morphism _ Sum.inr (fun _ => rfl) depth state

theorem coalesceGraph_rigid (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n))
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState)
    (index : Fin n) (rigid : graph index ≠ .var) :
    coalesceGraph graph cache parameterGraph parameter (.inl index) =
      (rigidLayer (graph index)).map Sum.inl := by
  simp [coalesceGraph, rigid]

/-- Constructor obligations from the previous observation depth establish
consistency of this depth's flat bounds. Arbitrary parameter values then work. -/
theorem coalesceGraph_edges_step (graph : NestedValueSolver.Graph n Row)
    (constraints cache : List (NestedValueSolver.Edge n))
    (closed : NestedValueSolver.Closed graph constraints cache)
    (leRow : Row → Row → Prop) (rowCheck : Row → Row → Bool)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (consistent : NestedValueSolver.consistent rowCheck graph cache = true)
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState)
    (depth : Nat)
    (children : ∀ edge ∈ cache, StructuralBase.Subtype leRow
      (observe (coalesceGraph graph cache parameterGraph parameter) depth (.inl edge.1))
      (observe (coalesceGraph graph cache parameterGraph parameter) depth (.inl edge.2))) :
    ∀ edge ∈ cache, At (coalesceGraph graph cache parameterGraph parameter) leRow depth
      (coalesceGraph graph cache parameterGraph parameter (.inl edge.1))
      (coalesceGraph graph cache parameterGraph parameter (.inl edge.2)) := by
  let child := fun index => observe (coalesceGraph graph cache parameterGraph parameter)
    depth (.inl index)
  let parameterValue := fun index => (parameter index).eval
    (fun state => observe (coalesceGraph graph cache parameterGraph parameter) depth (.inr state))
  have rigidOrdered : ∀ source target, (source, target) ∈ cache →
      graph source ≠ .var → graph target ≠ .var →
      StructuralBase.Subtype leRow ((rigidLayer (graph source)).eval child)
        ((rigidLayer (graph target)).eval child) := by
    intro source target present sourceRigid targetRigid
    obtain ⟨requirements, found, rows⟩ :=
      NestedValueSolver.consistent_inspect rowCheck graph cache consistent present
    apply RigidValueLayers.inspect_complete leRow child (graph source) (graph target)
      sourceRigid targetRigid requirements found
    constructor
    · intro edge member
      exact children edge (closed.2.1 (source, target) present requirements found edge member)
    · intro row member
      exact rowSound row.1 row.2 (rows row member)
  have flatModel := ValueBoundSchemes.expand_models
    (least_models graph constraints cache closed child leRow rigidOrdered) parameterValue
  have allEdges := template_models_edges graph cache child _ leRow flatModel
  intro edge present
  unfold At
  rw [coalesceGraph_eval, coalesceGraph_eval]
  exact allEdges edge present

/-- A successful saturated cache constructs a genuine regular solution for
every free parameter graph. No model-existence assumption is supplied. -/
theorem coalesceGraph_satisfies (graph : NestedValueSolver.Graph n Row)
    (constraints cache : List (NestedValueSolver.Edge n))
    (closed : NestedValueSolver.Closed graph constraints cache)
    (leRow : Row → Row → Prop) (rowCheck : Row → Row → Bool)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (consistent : NestedValueSolver.consistent rowCheck graph cache = true)
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState) :
    ∀ edge ∈ cache, NodeSubtype (coalesceGraph graph cache parameterGraph parameter) leRow
      (.inl edge.1) (.inl edge.2) := by
  suffices allDepths : ∀ depth, ∀ edge ∈ cache,
      At (coalesceGraph graph cache parameterGraph parameter) leRow depth
        (coalesceGraph graph cache parameterGraph parameter (.inl edge.1))
        (coalesceGraph graph cache parameterGraph parameter (.inl edge.2)) by
    exact fun edge present depth => allDepths depth edge present
  intro depth
  induction depth with
  | zero =>
      apply coalesceGraph_edges_step graph constraints cache closed leRow rowCheck rowSound consistent
        parameterGraph parameter 0
      exact fun _ _ => .refl _
  | succ depth ih =>
      exact coalesceGraph_edges_step graph constraints cache closed leRow rowCheck rowSound consistent
        parameterGraph parameter (depth + 1) ih

/-- Equivalent rigid observations allow an existing solution to serve as the
flat valuation even when recursive children have a different representation. -/
theorem template_models_of_edges (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (assignment value : Fin n → StructuralBase.Ty Row)
    (leRow : Row → Row → Prop)
    (rigidEquivalent : ∀ index, graph index ≠ .var →
      ValueBoundSchemes.Equivalent leRow ((rigidLayer (graph index)).eval assignment) (value index))
    (edges : ∀ edge ∈ cache, NestedValueSolver.Edge.Holds leRow value edge) :
    ValueBounds.Models leRow (LayerBoundTemplates.instantiateProblem assignment (template graph cache))
      value := by
  intro constraint member
  cases constraint with
  | lower bound target =>
      obtain ⟨layer, original, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_lower assignment _ bound target).mp member
      obtain ⟨source, present, rigid, _, rfl⟩ :=
        (mem_template_lower graph cache layer target).mp original
      exact .trans (rigidEquivalent source rigid).1 (edges (source, target) present)
  | flow source target =>
      have original := (LayerBoundTemplates.mem_instantiateProblem_flow assignment _ source target).mp member
      exact edges (source, target) ((mem_template_flow graph cache source target).mp original).1
  | upper source bound =>
      obtain ⟨layer, original, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_upper assignment _ source bound).mp member
      obtain ⟨target, present, _, rigid, rfl⟩ :=
        (mem_template_upper graph cache source layer).mp original
      exact .trans (edges (source, target) present) (rigidEquivalent target rigid).2
  | check left right =>
      obtain ⟨leftLayer, rightLayer, original, rfl, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_check assignment _ left right).mp member
      obtain ⟨source, target, present, leftRigid, rightRigid, rfl, rfl⟩ :=
        (mem_template_check graph cache leftLayer rightLayer).mp original
      exact .trans (rigidEquivalent source leftRigid).1
        (.trans (edges (source, target) present) (rigidEquivalent target rightRigid).2)

/-- Substituting an arbitrary original regular solution for the parameters
recovers all of its observations. This is a retraction, not a leastness claim. -/
theorem coalesceGraph_retract_at (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (original : Graph Row ParameterState) (value : Fin n → ParameterState)
    (realizes : ∀ index, graph index ≠ .var →
      (Subtype original leRow (original (value index)) ((rigidLayer (graph index)).map value) ∧
        Subtype original leRow ((rigidLayer (graph index)).map value) (original (value index))))
    (edges : ∀ edge ∈ cache, NodeSubtype original leRow (value edge.1) (value edge.2))
    (depth : Nat) :
    ∀ index, ValueBoundSchemes.Equivalent leRow
      (observe (coalesceGraph graph cache original (fun index => original (value index))) depth (.inl index))
      (observe original depth (value index)) := by
  induction depth with
  | zero => exact fun _ => ⟨.refl _, .refl _⟩
  | succ depth ih =>
      let generated := coalesceGraph graph cache original (fun index => original (value index))
      let child := fun index => observe generated depth (.inl index)
      let originalChild := fun index => observe original depth (value index)
      let current := fun index => observe original (depth + 1) (value index)
      have rigidEquivalent : ∀ index, graph index ≠ .var →
          ValueBoundSchemes.Equivalent leRow ((rigidLayer (graph index)).eval child) (current index) := by
        intro index rigid
        have childEquivalent := RigidValueLayers.rigidLayer_eval_equivalent leRow rowRefl
          child originalChild ih (graph index)
        have forward := (realizes index rigid).1 depth
        have backward := (realizes index rigid).2 depth
        simp only [At, Layer.eval_map] at forward backward
        exact ⟨.trans childEquivalent.1 backward, .trans forward childEquivalent.2⟩
      have currentEdges : ∀ edge ∈ cache, NestedValueSolver.Edge.Holds leRow current edge :=
        fun edge present => edges edge present depth
      have flatModel := template_models_of_edges graph cache child current leRow rigidEquivalent currentEdges
      have parameterEq :
          (fun index => (original (value index)).eval
            (fun state => observe generated depth (.inr state))) = current := by
        funext index
        change Layer.eval (fun state => observe generated depth (.inr state)) (original (value index)) =
          Layer.eval (observe original depth) (original (value index))
        congr 1
        funext state
        exact parameter_embedding graph cache original (fun index => original (value index)) depth state
      intro index
      change ValueBoundSchemes.Equivalent leRow
        ((generated (.inl index)).eval (observe generated depth)) (current index)
      rw [coalesceGraph_eval]
      by_cases isVariable : isVar (graph index) = true
      · simp only [nodeValues, isVariable, ↓reduceIte]
        rw [parameterEq]
        exact ValueBoundSchemes.expand_equivalent flatModel index
      · simp only [nodeValues, isVariable]
        exact rigidEquivalent index (fun equal => isVariable ((isVar_iff _).mpr equal))

/-- The complete regular value at each original node is recovered, including
all negative occurrences and all shared parameter correlations. -/
theorem coalesceGraph_retraction (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (original : Graph Row ParameterState) (value : Fin n → ParameterState)
    (realizes : ∀ index, graph index ≠ .var →
      (Subtype original leRow (original (value index)) ((rigidLayer (graph index)).map value) ∧
        Subtype original leRow ((rigidLayer (graph index)).map value) (original (value index))))
    (edges : ∀ edge ∈ cache, NodeSubtype original leRow (value edge.1) (value edge.2)) :
    ∀ index,
      NodeSubtype (coalesceGraph graph cache original (fun index => original (value index))) leRow
        (.inl index) (.inr (value index)) ∧
      NodeSubtype (coalesceGraph graph cache original (fun index => original (value index))) leRow
        (.inr (value index)) (.inl index) := by
  intro index
  constructor <;> intro depth
  · have comparison := (coalesceGraph_retract_at graph cache leRow rowRefl original value realizes edges
      (depth + 1) index).1
    change StructuralBase.Subtype leRow
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inl index))
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inr (value index)))
    rw [parameter_embedding]
    exact comparison
  · have comparison := (coalesceGraph_retract_at graph cache leRow rowRefl original value realizes edges
      (depth + 1) index).2
    change StructuralBase.Subtype leRow
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inr (value index)))
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inl index))
    rw [parameter_embedding]
    exact comparison

/-- The arbitrary-parameter construction realizes the original rigid nodes
and satisfies the original constraints, not merely its own expanded syntax. -/
theorem solve_instantiates_model (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache)
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState) :
    RegularNestedModels.Models leRow graph constraints
      (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  obtain ⟨closed, consistent⟩ := NestedValueSolver.solve_closed rowCheck graph constraints cache solved
  constructor
  · intro index rigid
    rw [coalesceGraph_rigid graph cache parameterGraph parameter index rigid]
    exact ⟨subtype_refl _, subtype_refl _⟩
  · intro edge present
    exact coalesceGraph_satisfies graph constraints cache closed leRow rowCheck rowSound consistent
      parameterGraph parameter edge (closed.1 edge present)

/-- Grafting a parameter graph preserves and reflects independent models. -/
theorem parameter_models_iff (graph : NestedValueSolver.Graph n Row)
    (constraints cache : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState)
    (value : Fin n → ParameterState) :
    RegularNestedModels.Models leRow graph constraints
      (coalesceGraph graph cache parameterGraph parameter) (fun index => Sum.inr (value index)) ↔
    RegularNestedModels.Models leRow graph constraints parameterGraph value := by
  let generated := coalesceGraph graph cache parameterGraph parameter
  have commutes : ∀ state, (parameterGraph state).map Sum.inr = generated (.inr state) := fun _ => rfl
  have realization : RegularNestedModels.Realizes graph generated leRow (fun index => Sum.inr (value index)) ↔
      RegularNestedModels.Realizes graph parameterGraph leRow value := by
    unfold RegularNestedModels.Realizes
    apply forall_congr'
    intro index
    apply imp_congr_right
    intro _
    change (Subtype generated leRow ((parameterGraph (value index)).map Sum.inr)
        ((rigidLayer (graph index)).map (fun i => Sum.inr (value i))) ∧
      Subtype generated leRow ((rigidLayer (graph index)).map (fun i => Sum.inr (value i)))
        ((parameterGraph (value index)).map Sum.inr)) ↔ _
    rw [← Layer.map_comp value Sum.inr]
    rw [subtype_morphism generated Sum.inr commutes, subtype_morphism generated Sum.inr commutes]
  have satisfaction : RegularNestedModels.Satisfies generated leRow constraints (fun index => Sum.inr (value index)) ↔
      RegularNestedModels.Satisfies parameterGraph leRow constraints value := by
    unfold RegularNestedModels.Satisfies
    apply forall_congr'
    intro edge
    apply imp_congr_right
    intro _
    exact subtype_morphism generated Sum.inr commutes _ _
  exact and_congr realization satisfaction

/-- Exactness over *all* regular assignments: a model is an instance of the
computed unconstrained scheme exactly when it satisfies the original problem.
The right-hand side asks only for shared free parameters and semantic equality;
it does not retain the input constraints as an instantiation side condition. -/
theorem solve_models_exact (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache)
    (original : Graph Row ParameterState) (value : Fin n → ParameterState) :
    RegularNestedModels.Models leRow graph constraints original value ↔
      ∃ parameter : Fin n → Layer Row ParameterState,
        RegularNestedModels.Equivalent (coalesceGraph graph cache original parameter) leRow
          Sum.inl (fun index => Sum.inr (value index)) := by
  constructor
  · intro model
    have saturated := RegularNestedModels.saturate_preserves leRow rowRefl rowTrans
      graph constraints original value model
    have cacheEqual := ((NestedValueSolver.solve_some_iff rowCheck graph constraints cache).mp solved).1
    rw [← cacheEqual] at saturated
    exact ⟨fun index => original (value index),
      coalesceGraph_retraction graph cache leRow rowRefl original value saturated.1 saturated.2⟩
  · rintro ⟨parameter, equivalent⟩
    have generatedModel := solve_instantiates_model rowCheck leRow
      (fun left right => (rowExact left right).mp) graph constraints cache solved original parameter
    have transferred := RegularNestedModels.models_equivalent leRow rowRefl graph constraints
      (coalesceGraph graph cache original parameter) Sum.inl (fun index => Sum.inr (value index))
      generatedModel equivalent
    exact (parameter_models_iff graph constraints cache leRow original parameter value).mp transferred

/-- The executable solver decides existence of an independently defined
recursive model. Failure is not a budget exhaustion result. -/
theorem solve_none_iff (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n)) :
    NestedValueSolver.solve rowCheck graph constraints = none ↔
      ¬ ∃ (ModelState : Type) (model : Graph Row ModelState) (value : Fin n → ModelState),
        RegularNestedModels.Models leRow graph constraints model value := by
  constructor
  · rintro rejected ⟨ModelState, model, value, satisfies⟩
    exact RegularNestedModels.solve_rejects_model rowCheck leRow rowRefl rowTrans rowExact
      graph constraints rejected model value satisfies
  · intro impossible
    cases result : NestedValueSolver.solve rowCheck graph constraints with
    | none => rfl
    | some cache =>
        let parameterGraph : Graph Row Unit := fun _ => .bottom
        let parameter : Fin n → Layer Row Unit := fun _ => .bottom
        exact False.elim (impossible ⟨Fin n ⊕ Unit,
          coalesceGraph graph cache parameterGraph parameter, Sum.inl,
          solve_instantiates_model rowCheck leRow (fun left right => (rowExact left right).mp)
            graph constraints cache result parameterGraph parameter⟩)

/-- An instance of the original existentially constrained output. The target
graph is embedded unchanged into a common model graph so no shared unfolding
depth or comparison is lost when models have different state sets. -/
def ConstrainedInstance (graph : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (root : Fin n) (leRow : Row → Row → Prop)
    (targetGraph : Graph Row ParameterState) (target : Layer Row ParameterState) : Prop :=
  ∃ (ModelState : Type v) (model : Graph Row ModelState) (value : Fin n → ModelState)
    (embed : ParameterState → ModelState),
    (∀ state, (targetGraph state).map embed = model (embed state)) ∧
    RegularNestedModels.Models leRow graph constraints model value ∧
    Subtype model leRow (model (value root)) (target.map embed)

/-- An instance of the output scheme. Parameters are arbitrary graph-rooted
types; there are no residual inequality constraints at instantiation. -/
def SchemeInstance (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (root : Fin n) (leRow : Row → Row → Prop)
    (targetGraph : Graph Row ParameterState) (target : Layer Row ParameterState) : Prop :=
  ∃ (FreeState : Type v) (freeGraph : Graph Row FreeState)
    (parameter : Fin n → Layer Row FreeState) (embed : ParameterState → FreeState),
    (∀ state, (targetGraph state).map embed = freeGraph (embed state)) ∧
    Subtype (coalesceGraph graph cache freeGraph parameter) leRow
      (coalesceGraph graph cache freeGraph parameter (.inl root))
      (target.map (fun state => Sum.inr (embed state)))

/-- Principal-output exactness, including subsumption, for the whole nested
constraint problem. This quantifies over the original independent models and
all regular free-parameter instances; no output-polarity restriction is used. -/
theorem solve_instances_exact (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache)
    (root : Fin n) (targetGraph : Graph Row ParameterState) (target : Layer Row ParameterState) :
    ConstrainedInstance graph constraints root leRow targetGraph target ↔
      SchemeInstance graph cache root leRow targetGraph target := by
  constructor
  · rintro ⟨ModelState, model, value, embed, embedding, satisfies, below⟩
    obtain ⟨parameter, equivalent⟩ := (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
      graph constraints cache solved model value).mp satisfies
    refine ⟨ModelState, model, parameter, embed, embedding, ?_⟩
    have lifted := (subtype_morphism (coalesceGraph graph cache model parameter) Sum.inr
      (fun _ => rfl) (model (value root)) (target.map embed)).mpr below
    have result := subtype_trans (equivalent root).1 lifted
    simpa only [Layer.map_comp] using result
  · rintro ⟨FreeState, freeGraph, parameter, embed, embedding, below⟩
    refine ⟨Fin n ⊕ FreeState, coalesceGraph graph cache freeGraph parameter, Sum.inl,
      (fun state => Sum.inr (embed state)), ?_, ?_, below⟩
    · intro state
      rw [← Layer.map_comp embed Sum.inr, embedding state]
      rfl
    · exact solve_instantiates_model rowCheck leRow (fun left right => (rowExact left right).mp)
        graph constraints cache solved freeGraph parameter

end Yulang.RegularValueCoalescing
