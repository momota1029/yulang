import Yulang.PresenceRegularCoalescing

/-!
# A mask-indexed observational model for guarded presence coalescing

Unmasked data equivalence does not determine a layer's masked meaning:
`required l never` and `bottom` are both empty before masking, but only the
former becomes `records` when `l` is hidden. Consequently unmasked independent
solutions do not support a root-mask retraction theorem.

This module states a separate candidate observational refinement. Every root
comparison and constructor equation is quantified over every outer mask.
Payload children are still observed without a mask, as specified by
`PresenceLayers.Layer.meaning`. Existing unmasked definitions are unchanged.

The same finite cache certificates construct models in this stronger sense,
and every independent model in this stronger sense is recovered at every root,
depth and mask. Selecting this refinement as a language model, producing complete
cache certificates, unguarded open tails, functions and rows remain separate
obligations. The extra mask-indexed premises are explicit, not inferred from
unmasked data equivalence.
-/

namespace Yulang.PresenceMaskedCoalescing

open PresenceLayers (Layer)
open PresenceDataTypes (Ty Le)
open PresenceRegularObservations (observe)
open PresenceRegularCoalescing (Graph Edge Closed Derives coalesceGraph)
open SourceDataRuntime (Value)

universe u
variable {n : Nat} {Index : Type u}

def observeMasked (graph : PresenceRegularObservations.Graph Index) : Nat → List Nat → Index → Ty
  | 0, _, _ => PresenceDataTypes.never
  | depth + 1, hidden, state => (graph state).meaning (observe graph depth) hidden

theorem observeMasked_nil (graph : PresenceRegularObservations.Graph Index) (depth : Nat) (state : Index) :
    observeMasked graph depth [] state = observe graph depth state := by
  cases depth <;> rfl

def NodeSubtype (graph : PresenceRegularObservations.Graph Index) (left right : Index) : Prop :=
  ∀ depth hidden, Le (observeMasked graph depth hidden left) (observeMasked graph depth hidden right)

def Realizes (graph : Graph n) (original : PresenceRegularObservations.Graph Index)
    (value : Fin n → Index) : Prop :=
  ∀ index layer, graph index = some layer → ∀ depth hidden item,
    observeMasked original (depth + 1) hidden (value index) item ↔
      layer.meaning (fun child => observe original depth (value child)) hidden item

def Models (graph : Graph n) (constraints : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index) : Prop :=
  Realizes graph original value ∧ ∀ edge ∈ constraints, NodeSubtype original (value edge.1) (value edge.2)

theorem Models.unmasked {graph : Graph n} {constraints : List (Edge n)}
    {original : PresenceRegularObservations.Graph Index} {value : Fin n → Index}
    (model : Models graph constraints original value) :
    PresenceRegularCoalescing.Models graph constraints original value := by
  constructor
  · intro index layer rigid depth item
    exact model.1 index layer rigid depth [] item
  · intro edge member depth item valid
    exact model.2 edge member (depth + 1) [] item valid

/-- Every current finite derivation is sound under every root mask. The
cache's child obligations remain unmasked because payloads start unmasked. -/
theorem derives_mask_sound {cache : List (Edge n)} {left right : Layer (Fin n)}
    (derivation : Derives cache left right) (assignment : Fin n → Ty)
    (children : ∀ edge ∈ cache, Le (assignment edge.1) (assignment edge.2)) (hidden : List Nat) :
    Le (left.meaning assignment hidden) (right.meaning assignment hidden) := by
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
  | @required first last label child =>
      by_cases masked : label ∈ hidden
      · simpa only [Layer.meaning, masked, ↓reduceIte] using (PresenceDataTypes.le_refl PresenceDataTypes.records)
      · simp only [Layer.meaning, masked, ↓reduceIte]
        rintro item ⟨record, payload, found, valid⟩
        exact ⟨record, payload, found, children _ child _ valid⟩
  | @optional first last label child =>
      by_cases masked : label ∈ hidden
      · simpa only [Layer.meaning, masked, ↓reduceIte] using (PresenceDataTypes.le_refl PresenceDataTypes.records)
      · simp only [Layer.meaning, masked, ↓reduceIte]
        rintro item ⟨record, valid⟩
        exact ⟨record, fun payload found => children _ child _ (valid payload found)⟩
  | requiredOptional label payload =>
      by_cases masked : label ∈ hidden
      · simpa only [Layer.meaning, masked, ↓reduceIte] using (PresenceDataTypes.le_refl PresenceDataTypes.records)
      · simpa only [Layer.meaning, masked, ↓reduceIte] using PresenceDataTypes.required_optional label (assignment payload)
  | lacksOptional label payload =>
      by_cases masked : label ∈ hidden
      · simpa only [Layer.meaning, masked, ↓reduceIte] using (PresenceDataTypes.le_refl PresenceDataTypes.records)
      · simpa only [Layer.meaning, masked, ↓reduceIte] using PresenceDataTypes.lacks_optional label (assignment payload)
  | requiredRecords label payload | optionalRecords label payload =>
      by_cases masked : label ∈ hidden
      · simpa only [Layer.meaning, masked, ↓reduceIte] using (PresenceDataTypes.le_refl PresenceDataTypes.records)
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact fun _ valid => valid.1
  | lacksRecords label =>
      by_cases masked : label ∈ hidden
      · simpa only [Layer.meaning, masked, ↓reduceIte] using (PresenceDataTypes.le_refl PresenceDataTypes.records)
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact fun _ valid => valid.1
  | optionalSplit label payload =>
      by_cases masked : label ∈ hidden
      · simp only [Layer.meaning, masked, ↓reduceIte]
        exact fun _ valid => Or.inl valid
      · simp only [Layer.meaning, masked, ↓reduceIte]
        rintro item ⟨record, valid⟩
        cases found : PresenceDataTypes.lookup label item with
        | none => exact Or.inl ⟨record, found⟩
        | some value => exact Or.inr ⟨record, value, found, valid value found⟩

open PresenceRegularCoalescing (template)

theorem lower_models_mask (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache) (assignment : Fin n → Ty)
    (children : ∀ edge ∈ cache, Le (assignment edge.1) (assignment edge.2)) (hidden : List Nat) :
    PresenceBoundCoalescing.Models (fun layer => layer.meaning assignment hidden) (template graph cache)
      (PresenceBoundCoalescing.lower (fun layer => layer.meaning assignment hidden) (template graph cache)) := by
  intro constraint member
  cases constraint with
  | lower bound target => exact PresenceBoundCoalescing.lower_lower _ _ bound target member
  | flow source target => exact PresenceBoundCoalescing.lower_flow _ _ source target member
  | upper source bound =>
      obtain ⟨target, upperEdge, variableNode, rigid⟩ :=
        (PresenceRegularCoalescing.mem_template_upper graph cache source bound).mp member
      rintro value ⟨lower, lowerMember, valid⟩
      obtain ⟨start, seed, path⟩ :=
        (PresenceBoundCoalescing.mem_lowerBounds (template graph cache) source lower).mp lowerMember
      obtain ⟨origin, lowerEdge, originRigid, _⟩ :=
        (PresenceRegularCoalescing.mem_template_lower graph cache lower start).mp seed
      have propagated := PresenceRegularCoalescing.path_propagates graph constraints cache closed path origin lowerEdge
      exact derives_mask_sound (closed.rigid origin target lower bound originRigid rigid
        (closed.propagate source variableNode origin target propagated upperEdge)) assignment children hidden value valid
  | check left right =>
      obtain ⟨source, target, edge, first, last⟩ :=
        (PresenceRegularCoalescing.mem_template_check graph cache left right).mp member
      exact derives_mask_sound (closed.rigid source target left right first last edge) assignment children hidden

def nodeValues (graph : Graph n) (assignment variables : Fin n → Ty) (hidden : List Nat) (index : Fin n) : Ty :=
  match graph index with
  | none => variables index
  | some layer => layer.meaning assignment hidden

theorem template_models_edges (graph : Graph n) (cache : List (Edge n))
    (assignment variables : Fin n → Ty) (hidden : List Nat)
    (model : PresenceBoundCoalescing.Models (fun layer => layer.meaning assignment hidden)
      (template graph cache) variables) :
    ∀ edge ∈ cache, Le (nodeValues graph assignment variables hidden edge.1)
      (nodeValues graph assignment variables hidden edge.2) := by
  intro edge present
  have valid := model _ (List.mem_map.mpr ⟨edge, present, rfl⟩)
  cases left : graph edge.1 <;> cases right : graph edge.2 <;>
    simpa only [PresenceRegularCoalescing.edgeTemplate, left, right, PresenceBoundCoalescing.Holds, nodeValues] using valid

theorem template_models_of_edges (graph : Graph n) (cache : List (Edge n))
    (assignment value : Fin n → Ty) (hidden : List Nat)
    (realizes : ∀ index layer, graph index = some layer → ∀ item,
      layer.meaning assignment hidden item ↔ value index item)
    (edges : ∀ edge ∈ cache, Le (value edge.1) (value edge.2)) :
    PresenceBoundCoalescing.Models (fun layer => layer.meaning assignment hidden)
      (template graph cache) value := by
  intro constraint member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  cases left : graph edge.1 <;> cases right : graph edge.2 <;>
    simp only [PresenceRegularCoalescing.edgeTemplate, left, right, PresenceBoundCoalescing.Holds]
  · exact edges edge present
  · intro item valid
    exact (realizes edge.2 _ right item).mpr (edges edge present item valid)
  · intro item valid
    exact edges edge present item ((realizes edge.1 _ left item).mp valid)
  · intro item valid
    exact (realizes edge.2 _ right item).mpr
      (edges edge present item ((realizes edge.1 _ left item).mp valid))

theorem coalesceGraph_eval_mask (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph Index)
    (parameter : Fin n → Layer Index) (assignment : Fin n ⊕ Index → Ty)
    (hidden : List Nat) (index : Fin n) (item : Value) :
    (coalesceGraph graph cache parameterGraph parameter (.inl index)).meaning assignment hidden item ↔
      nodeValues graph (fun child => assignment (.inl child))
        (PresenceBoundCoalescing.expand
          (fun layer => layer.meaning (fun child => assignment (.inl child)) hidden) (template graph cache)
          (fun child => (parameter child).meaning (fun state => assignment (.inr state)) hidden)) hidden index item := by
  cases shape : graph index with
  | none =>
      simpa only [coalesceGraph, nodeValues, shape, Layer.meaning_map] using
        (PresenceRegularCoalescing.expandLayer_exact (template graph cache) (Layer.map Sum.inl)
          (fun child => (parameter child).map Sum.inr) assignment hidden index item)
  | some layer => simp only [coalesceGraph, nodeValues, shape, Layer.meaning_map]

theorem parameter_embedding (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph Index)
    (parameter : Fin n → Layer Index) (depth : Nat) (hidden : List Nat) (state : Index) (item : Value) :
    observeMasked (coalesceGraph graph cache parameterGraph parameter) depth hidden (.inr state) item ↔
      observeMasked parameterGraph depth hidden state item := by
  cases depth with
  | zero => rfl
  | succ depth =>
      simp only [observeMasked, coalesceGraph, Layer.meaning_map]
      exact Layer.meaning_congr _ _
        (PresenceRegularCoalescing.parameter_embedding graph cache parameterGraph parameter depth)
        hidden (parameterGraph state) item

theorem coalesceGraph_realizes (graph : Graph n) (cache : List (Edge n))
    (parameterGraph : PresenceRegularObservations.Graph Index) (parameter : Fin n → Layer Index) :
    Realizes graph (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  intro index layer rigid depth hidden item
  simp only [observeMasked,
    PresenceRegularCoalescing.coalesceGraph_rigid graph cache parameterGraph parameter index layer rigid,
    Layer.meaning_map]

/-- A finite closed cache constructs a solution uniformly for every root
mask, with arbitrary external parameter graphs and parameter layers. -/
theorem coalesceGraph_satisfies_cache (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache)
    (parameterGraph : PresenceRegularObservations.Graph Index) (parameter : Fin n → Layer Index) :
    Models graph cache (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  refine ⟨coalesceGraph_realizes graph cache parameterGraph parameter, ?_⟩
  have ordinary := PresenceRegularCoalescing.coalesceGraph_satisfies_cache
    graph constraints cache closed parameterGraph parameter
  intro edge member depth hidden
  cases depth with
  | zero => exact fun _ valid => False.elim valid
  | succ depth =>
      let generated := coalesceGraph graph cache parameterGraph parameter
      let assignment := fun child => observe generated depth (.inl child)
      let parameters := fun child => (parameter child).meaning (fun state => observe generated depth (.inr state)) hidden
      have children : ∀ child ∈ cache, Le (assignment child.1) (assignment child.2) := by
        cases depth with
        | zero => exact fun _ _ _ valid => False.elim valid
        | succ depth => exact fun child present => ordinary.2 child present depth
      have flat := PresenceBoundCoalescing.expand_satisfies
        (lower_models_mask graph constraints cache closed assignment children hidden) parameters
      have edges := template_models_edges graph cache assignment _ hidden flat
      intro item valid
      exact (coalesceGraph_eval_mask graph cache parameterGraph parameter (observe generated depth) hidden edge.2 item).mpr
        (edges edge member item
          ((coalesceGraph_eval_mask graph cache parameterGraph parameter (observe generated depth) hidden edge.1 item).mp valid))

theorem coalesceGraph_satisfies (graph : Graph n) (constraints cache : List (Edge n))
    (closed : Closed graph constraints cache)
    (parameterGraph : PresenceRegularObservations.Graph Index) (parameter : Fin n → Layer Index) :
    Models graph constraints (coalesceGraph graph cache parameterGraph parameter) Sum.inl := by
  have model := coalesceGraph_satisfies_cache graph constraints cache closed parameterGraph parameter
  exact ⟨model.1, fun edge member => model.2 edge (closed.inputs edge member)⟩

/-- An independent mask-indexed cached solution is recovered at each actual
root, for every depth and mask. This premise is strictly stronger than the
unmasked `PresenceRegularCoalescing.Models` premise. -/
theorem coalesceGraph_retract_at (graph : Graph n) (cache : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index)
    (model : Models graph cache original value) (depth : Nat) (hidden : List Nat) :
    ∀ index item,
      observeMasked (coalesceGraph graph cache original (fun index => original (value index))) depth hidden (.inl index) item ↔
        observeMasked original depth hidden (value index) item := by
  cases depth with
  | zero => exact fun _ _ => Iff.rfl
  | succ depth =>
      let generated := coalesceGraph graph cache original (fun index => original (value index))
      let child := fun index => observe generated depth (.inl index)
      let originalChild := fun index => observe original depth (value index)
      let current := fun index => observeMasked original (depth + 1) hidden (value index)
      have childExact := PresenceRegularCoalescing.coalesceGraph_retract_at graph cache original value
        model.unmasked.1 model.unmasked.2 depth
      have rigidEquivalent : ∀ index layer, graph index = some layer → ∀ item,
          layer.meaning child hidden item ↔ current index item := by
        intro index layer rigid item
        exact (Layer.meaning_congr child originalChild childExact hidden layer item).trans
          (model.1 index layer rigid depth hidden item).symm
      have currentEdges : ∀ edge ∈ cache, Le (current edge.1) (current edge.2) :=
        fun edge member => model.2 edge member (depth + 1) hidden
      have flatModel := template_models_of_edges graph cache child current hidden rigidEquivalent currentEdges
      have parameterEq : (fun index => (original (value index)).meaning
          (fun state => observe generated depth (.inr state)) hidden) = current := by
        funext index item
        apply propext
        exact Layer.meaning_congr _ _
          (PresenceRegularCoalescing.parameter_embedding graph cache original
            (fun index => original (value index)) depth)
          hidden (original (value index)) item
      intro index item
      change (generated (.inl index)).meaning (observe generated depth) hidden item ↔ current index item
      rw [coalesceGraph_eval_mask]
      cases shape : graph index with
      | none =>
          simp only [nodeValues, shape]
          rw [parameterEq]
          exact PresenceBoundCoalescing.expand_retraction flatModel index item
      | some layer =>
          simp only [nodeValues, shape]
          exact rigidEquivalent index layer shape item

/-- The retraction holds in both directions of the mask-indexed subtype,
at every original slot. All parameters are the same shared independent graph. -/
theorem coalesceGraph_retraction (graph : Graph n) (cache : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index)
    (model : Models graph cache original value) :
    ∀ index,
      NodeSubtype (coalesceGraph graph cache original (fun index => original (value index)))
        (.inl index) (.inr (value index)) ∧
      NodeSubtype (coalesceGraph graph cache original (fun index => original (value index)))
        (.inr (value index)) (.inl index) := by
  intro index
  constructor <;> intro depth hidden item valid
  · exact (parameter_embedding graph cache original (fun index => original (value index))
      depth hidden (value index) item).mpr
        ((coalesceGraph_retract_at graph cache original value model depth hidden index item).mp valid)
  · exact (coalesceGraph_retract_at graph cache original value model depth hidden index item).mpr
        ((parameter_embedding graph cache original (fun index => original (value index))
          depth hidden (value index) item).mp valid)

/-- This compares masks of the two actual root layers, rather than applying
one common outer masked context to two unmasked-equivalent slot assignments. -/
theorem coalesceGraph_root_mask_retraction (graph : Graph n) (cache : List (Edge n))
    (original : PresenceRegularObservations.Graph Index) (value : Fin n → Index)
    (model : Models graph cache original value) (index : Fin n) (depth : Nat) (hidden : List Nat) (item : Value) :
    ((coalesceGraph graph cache original (fun index => original (value index)) (.inl index)).mask hidden).denote
        (observe (coalesceGraph graph cache original (fun index => original (value index))) depth) item ↔
      ((original (value index)).mask hidden).denote (observe original depth) item := by
  rw [Layer.mask_exact, Layer.mask_exact]
  exact coalesceGraph_retract_at graph cache original value model (depth + 1) hidden index item

end Yulang.PresenceMaskedCoalescing
