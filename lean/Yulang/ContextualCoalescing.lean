import Yulang.ContextualValueBounds
import Yulang.ContextualNestedModels

/-!
# Full contextual retraction of the actual regular coalescer

The executable graph and free-parameter scheme are the existing
`RegularValueCoalescing.coalesceGraph`. Its retraction now covers every
independent contextual model, not only old structural solutions. At each
constructor depth, the proof uses full contextual constructor congruence and
`ContextualValueBounds.expand_equivalent` for the same finite lattice template.
The given model itself supplies the shared parameters, including correlations
across positive and negative occurrences. No depth/fuel bound is imposed.
-/

namespace Yulang.ContextualCoalescing

open RegularValueTypes
open RegularValueCoalescing
open RigidValueLayers (rigidLayer recordLayer)

universe u v w
variable {n : Nat} {Row : Type u} {ParameterState : Type v}

private theorem recordLayer_eval_equivalent (leRow : Row → Row → Prop)
    (left right : Fin n → StructuralBase.Ty Row)
    (equivalent : ∀ index, ProducerContextual.ProducerEq leRow (left index) (right index))
    (fields : List (Nat × Fin n)) :
    ProducerContextual.ProducerEq leRow ((recordLayer fields).eval left) ((recordLayer fields).eval right) := by
  induction fields with
  | nil => exact ProducerContextual.producerEq_refl _
  | cons field rest ih =>
      obtain ⟨label, index⟩ := field
      exact ProducerContextual.producerEq_record label (equivalent index) ih

theorem rigidLayer_eval_equivalent (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (left right : Fin n → StructuralBase.Ty Row)
    (equivalent : ∀ index, ProducerContextual.ProducerEq leRow (left index) (right index))
    (node : NestedValueSolver.Node n Row) :
    ProducerContextual.ProducerEq leRow ((rigidLayer node).eval left) ((rigidLayer node).eval right) := by
  cases node with
  | var | bottom | top | base => exact ProducerContextual.producerEq_refl _
  | pair a b => exact ProducerContextual.producerEq_pair (equivalent a) (equivalent b)
  | variant label payload => exact ProducerContextual.producerEq_variant label (equivalent payload)
  | arrow input inputRow output outputRow =>
      exact ProducerContextual.producerEq_arrow (leRow := leRow) rowRefl rowTrans inputRow outputRow
        (equivalent input) (equivalent output)
  | record fields => exact recordLayer_eval_equivalent leRow left right equivalent fields

/-- Equivalent rigid observations allow an existing solution to serve as the
flat valuation even when recursive children have a different representation. -/
theorem template_models_of_edges (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (assignment value : Fin n → StructuralBase.Ty Row)
    (leRow : Row → Row → Prop)
    (rigidEquivalent : ∀ index, graph index ≠ .var →
      ProducerContextual.ProducerEq leRow ((rigidLayer (graph index)).eval assignment) (value index))
    (edges : ∀ edge ∈ cache, ProducerContextual.ProducerLe leRow (value edge.1) (value edge.2)) :
    ContextualValueBounds.Models leRow (LayerBoundTemplates.instantiateProblem assignment (template graph cache))
      value := by
  intro constraint member
  cases constraint with
  | lower bound target =>
      obtain ⟨layer, original, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_lower assignment _ bound target).mp member
      obtain ⟨source, present, rigid, _, rfl⟩ :=
        (mem_template_lower graph cache layer target).mp original
      exact ProducerContextual.producerLe_trans (rigidEquivalent source rigid).1 (edges (source, target) present)
  | flow source target =>
      have original := (LayerBoundTemplates.mem_instantiateProblem_flow assignment _ source target).mp member
      exact edges (source, target) ((mem_template_flow graph cache source target).mp original).1
  | upper source bound =>
      obtain ⟨layer, original, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_upper assignment _ source bound).mp member
      obtain ⟨target, present, _, rigid, rfl⟩ :=
        (mem_template_upper graph cache source layer).mp original
      exact ProducerContextual.producerLe_trans (edges (source, target) present) (rigidEquivalent target rigid).2
  | check left right =>
      obtain ⟨leftLayer, rightLayer, original, rfl, rfl⟩ :=
        (LayerBoundTemplates.mem_instantiateProblem_check assignment _ left right).mp member
      obtain ⟨source, target, present, leftRigid, rightRigid, rfl, rfl⟩ :=
        (mem_template_check graph cache leftLayer rightLayer).mp original
      exact ProducerContextual.producerLe_trans (rigidEquivalent source leftRigid).1
        (ProducerContextual.producerLe_trans (edges (source, target) present) (rigidEquivalent target rightRigid).2)

/-- Substituting an arbitrary original regular solution for the parameters
recovers all of its observations. This is a retraction, not a leastness claim. -/
theorem coalesceGraph_retract_at (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (original : Graph Row ParameterState) (value : Fin n → ParameterState)
    (realizes : ∀ index, graph index ≠ .var →
      (ProducerContextualRegular.ProducerLe original leRow (original (value index)) ((rigidLayer (graph index)).map value) ∧
        ProducerContextualRegular.ProducerLe original leRow ((rigidLayer (graph index)).map value) (original (value index))))
    (edges : ∀ edge ∈ cache, ContextualNestedModels.NodeLe original leRow (value edge.1) (value edge.2))
    (depth : Nat) :
    ∀ index, ProducerContextual.ProducerEq leRow
      (observe (coalesceGraph graph cache original (fun index => original (value index))) depth (.inl index))
      (observe original depth (value index)) := by
  induction depth with
  | zero => exact fun _ => ⟨ProducerContextual.producerLe_refl _, ProducerContextual.producerLe_refl _⟩
  | succ depth ih =>
      let generated := coalesceGraph graph cache original (fun index => original (value index))
      let child := fun index => observe generated depth (.inl index)
      let originalChild := fun index => observe original depth (value index)
      let current := fun index => observe original (depth + 1) (value index)
      have rigidEquivalent : ∀ index, graph index ≠ .var →
          ProducerContextual.ProducerEq leRow ((rigidLayer (graph index)).eval child) (current index) := by
        intro index rigid
        have childEquivalent := rigidLayer_eval_equivalent leRow rowRefl rowTrans
          child originalChild ih (graph index)
        have forward := (realizes index rigid).1 depth
        have backward := (realizes index rigid).2 depth
        simp only [Layer.eval_map] at forward backward
        exact ⟨ProducerContextual.producerLe_trans childEquivalent.1 backward, ProducerContextual.producerLe_trans forward childEquivalent.2⟩
      have currentEdges : ∀ edge ∈ cache, ProducerContextual.ProducerLe leRow (current edge.1) (current edge.2) :=
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
      change ProducerContextual.ProducerEq leRow
        ((generated (.inl index)).eval (observe generated depth)) (current index)
      rw [coalesceGraph_eval]
      by_cases isVariable : isVar (graph index) = true
      · simp only [nodeValues, isVariable, ↓reduceIte]
        rw [parameterEq]
        exact ContextualValueBounds.expand_equivalent flatModel index
      · simp only [nodeValues, isVariable]
        exact rigidEquivalent index (fun equal => isVariable ((isVar_iff _).mpr equal))

/-- The complete regular value at each original node is recovered, including
all negative occurrences and all shared parameter correlations. -/
theorem coalesceGraph_retraction (graph : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (original : Graph Row ParameterState) (value : Fin n → ParameterState)
    (realizes : ∀ index, graph index ≠ .var →
      (ProducerContextualRegular.ProducerLe original leRow (original (value index)) ((rigidLayer (graph index)).map value) ∧
        ProducerContextualRegular.ProducerLe original leRow ((rigidLayer (graph index)).map value) (original (value index))))
    (edges : ∀ edge ∈ cache, ContextualNestedModels.NodeLe original leRow (value edge.1) (value edge.2)) :
    ∀ index,
      ContextualNestedModels.NodeLe (coalesceGraph graph cache original (fun index => original (value index))) leRow
        (.inl index) (.inr (value index)) ∧
      ContextualNestedModels.NodeLe (coalesceGraph graph cache original (fun index => original (value index))) leRow
        (.inr (value index)) (.inl index) := by
  intro index
  constructor <;> intro depth
  · have comparison := (coalesceGraph_retract_at graph cache leRow rowRefl rowTrans original value realizes edges
      (depth + 1) index).1
    change ProducerContextual.ProducerLe leRow
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inl index))
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inr (value index)))
    rw [parameter_embedding]
    exact comparison
  · have comparison := (coalesceGraph_retract_at graph cache leRow rowRefl rowTrans original value realizes edges
      (depth + 1) index).2
    change ProducerContextual.ProducerLe leRow
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inr (value index)))
      (observe (coalesceGraph graph cache original (fun index => original (value index)))
        (depth + 1) (.inl index))
    rw [parameter_embedding]
    exact comparison


def Equivalent (modelGraph : Graph Row ParameterState) (leRow : Row → Row → Prop)
    (left right : Fin n → ParameterState) : Prop :=
  ∀ index, ContextualNestedModels.NodeLe modelGraph leRow (left index) (right index) ∧
    ContextualNestedModels.NodeLe modelGraph leRow (right index) (left index)

theorem rigidLayer_map_equivalent (modelGraph : Graph Row ParameterState)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (left right : Fin n → ParameterState) (equivalent : Equivalent modelGraph leRow left right)
    (node : NestedValueSolver.Node n Row) :
    ProducerContextualRegular.ProducerEq modelGraph leRow
      ((rigidLayer node).map left) ((rigidLayer node).map right) := by
  have atDepth (depth : Nat) := rigidLayer_eval_equivalent leRow rowRefl rowTrans
    (fun index => observe modelGraph depth (left index))
    (fun index => observe modelGraph depth (right index))
    (fun index => ⟨ContextualNestedModels.observe_subtype modelGraph leRow (equivalent index).1 depth,
      ContextualNestedModels.observe_subtype modelGraph leRow (equivalent index).2 depth⟩) node
  constructor
  · intro depth
    simpa only [Layer.eval_map] using (atDepth depth).1
  · intro depth
    simpa only [Layer.eval_map] using (atDepth depth).2

theorem models_equivalent (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (modelGraph : Graph Row ParameterState) (left right : Fin n → ParameterState)
    (model : ContextualNestedModels.Models leRow graph constraints modelGraph left)
    (equivalent : Equivalent modelGraph leRow left right) :
    ContextualNestedModels.Models leRow graph constraints modelGraph right := by
  constructor
  · intro node rigid
    obtain ⟨forward, backward⟩ := model.1 node rigid
    obtain ⟨rigidForward, rigidBackward⟩ :=
      rigidLayer_map_equivalent modelGraph leRow rowRefl rowTrans left right equivalent (graph node)
    exact ⟨ProducerContextualRegular.producerLe_trans (equivalent node).2
        (ProducerContextualRegular.producerLe_trans forward rigidForward),
      ProducerContextualRegular.producerLe_trans rigidBackward
        (ProducerContextualRegular.producerLe_trans backward (equivalent node).1)⟩
  · intro edge member
    exact ContextualNestedModels.nodeLe_trans (equivalent edge.1).2
      (ContextualNestedModels.nodeLe_trans (model.2 edge member) (equivalent edge.2).1)

/-- Pure graph morphisms preserve every finite observation literally, so they
also preserve and reflect all contextual ranks and environments. -/
theorem producerLe_morphism {Target : Type w}
    (source : Graph Row ParameterState) (target : Graph Row Target) (leRow : Row → Row → Prop)
    (rename : ParameterState → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (left right : Layer Row ParameterState) :
    ProducerContextualRegular.ProducerLe target leRow (left.map rename) (right.map rename) ↔
      ProducerContextualRegular.ProducerLe source leRow left right := by
  unfold ProducerContextualRegular.ProducerLe
  simp only [eval_morphism target rename commutes]

theorem nodeLe_morphism {Target : Type w}
    (source : Graph Row ParameterState) (target : Graph Row Target) (leRow : Row → Row → Prop)
    (rename : ParameterState → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (left right : ParameterState) :
    ContextualNestedModels.NodeLe target leRow (rename left) (rename right) ↔
      ContextualNestedModels.NodeLe source leRow left right := by
  unfold ContextualNestedModels.NodeLe
  rw [← commutes left, ← commutes right]
  exact producerLe_morphism source target leRow rename commutes _ _

/-- Grafting parameters preserves and reflects their independent models;
no injectivity or finite-graph assumption is needed. -/
theorem parameter_models_iff (graph : NestedValueSolver.Graph n Row)
    (constraints cache : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (parameterGraph : Graph Row ParameterState) (parameter : Fin n → Layer Row ParameterState)
    (value : Fin n → ParameterState) :
    ContextualNestedModels.Models leRow graph constraints
      (coalesceGraph graph cache parameterGraph parameter) (fun index => Sum.inr (value index)) ↔
      ContextualNestedModels.Models leRow graph constraints parameterGraph value := by
  let generated := coalesceGraph graph cache parameterGraph parameter
  have commutes : ∀ state, (parameterGraph state).map Sum.inr = generated (.inr state) := fun _ => rfl
  have realization : ContextualNestedModels.Realizes graph generated leRow (fun index => Sum.inr (value index)) ↔
      ContextualNestedModels.Realizes graph parameterGraph leRow value := by
    unfold ContextualNestedModels.Realizes
    apply forall_congr'
    intro index
    apply imp_congr_right
    intro _
    change (ProducerContextualRegular.ProducerLe generated leRow ((parameterGraph (value index)).map Sum.inr)
        ((rigidLayer (graph index)).map (fun i => Sum.inr (value i))) ∧
      ProducerContextualRegular.ProducerLe generated leRow ((rigidLayer (graph index)).map (fun i => Sum.inr (value i)))
        ((parameterGraph (value index)).map Sum.inr)) ↔ _
    rw [← Layer.map_comp value Sum.inr]
    rw [producerLe_morphism parameterGraph generated leRow Sum.inr commutes,
      producerLe_morphism parameterGraph generated leRow Sum.inr commutes]
  have satisfaction : ContextualNestedModels.Satisfies generated leRow constraints (fun index => Sum.inr (value index)) ↔
      ContextualNestedModels.Satisfies parameterGraph leRow constraints value := by
    unfold ContextualNestedModels.Satisfies
    apply forall_congr'
    intro edge
    apply imp_congr_right
    intro _
    exact nodeLe_morphism parameterGraph generated leRow Sum.inr commutes _ _
  exact and_congr realization satisfaction

/-- The actual computed cache represents every independent contextual model
by unrestricted shared parameters, and every such parameter instance is a
model. The right side retains no bound or satisfiability predicate. -/
theorem solve_models_exact (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache)
    (original : Graph Row ParameterState) (value : Fin n → ParameterState) :
    ContextualNestedModels.Models leRow graph constraints original value ↔
      ∃ parameter : Fin n → Layer Row ParameterState,
        Equivalent (coalesceGraph graph cache original parameter) leRow
          Sum.inl (fun index => Sum.inr (value index)) := by
  constructor
  · intro model
    have saturated := ContextualNestedModels.saturate_preserves leRow rowRefl rowTrans
      graph constraints original value model
    have cacheEqual := ((NestedValueSolver.solve_some_iff rowCheck graph constraints cache).mp solved).1
    rw [← cacheEqual] at saturated
    exact ⟨fun index => original (value index),
      coalesceGraph_retraction graph cache leRow rowRefl rowTrans original value saturated.1 saturated.2⟩
  · rintro ⟨parameter, equivalent⟩
    have generatedModel := ContextualNestedModels.solve_instantiates_model rowCheck leRow rowTrans
      (fun left right => (rowExact left right).mp) graph constraints cache solved original parameter
    have transferred := models_equivalent leRow rowRefl rowTrans graph constraints
      (coalesceGraph graph cache original parameter) Sum.inl (fun index => Sum.inr (value index))
      generatedModel equivalent
    exact (parameter_models_iff graph constraints cache leRow original parameter value).mp transferred

/-- All-input principal family exactness. The solver result is computed and
existentially returned; callers supply no successful solve, fuel, cache or model
witness as a theorem premise. Original models remain independently defined. -/
theorem models_exact (rowCheck : Row → Row → Bool)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (original : Graph Row ParameterState) (value : Fin n → ParameterState) :
    ContextualNestedModels.Models leRow graph constraints original value ↔
      ∃ cache, NestedValueSolver.solve rowCheck graph constraints = some cache ∧
        ∃ parameter : Fin n → Layer Row ParameterState,
          Equivalent (coalesceGraph graph cache original parameter) leRow
            Sum.inl (fun index => Sum.inr (value index)) := by
  constructor
  · intro model
    have saturated := ContextualNestedModels.saturate_preserves leRow rowRefl rowTrans
      graph constraints original value model
    have consistent := ContextualNestedModels.consistent_of_models rowCheck leRow rowRefl rowTrans rowExact
      graph _ original value saturated
    have solved : NestedValueSolver.solve rowCheck graph constraints =
        some (NestedValueSolver.saturate graph constraints) := by
      simp [NestedValueSolver.solve, consistent]
    exact ⟨NestedValueSolver.saturate graph constraints, solved,
      (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact graph constraints _ solved original value).mp model⟩
  · rintro ⟨cache, solved, parameters, equivalent⟩
    exact (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact graph constraints cache solved
      original value).mpr ⟨parameters, equivalent⟩

end Yulang.ContextualCoalescing
