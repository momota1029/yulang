import Yulang.OpenRecordConstraintGraph
import Yulang.ShadowRegularInferenceModel
import Yulang.PresenceRegularLegacyBridge

/-!
# Depth-preserving transport of open-tail constructor equations

An open constraint node has two different sorts of reference. Pair, variant,
field payload and arrow references cross a constructor; a record tail and a
lattice child remain at the current outer observation depth. `nodeLayer`
implements that distinction by inserting the tail's defining layer rather
than putting the tail behind a new graph-state reference.

The interpretation below transports independent assignments; it does not
compute them. It works for every finite open constraint graph and every
possibly cyclic regular assignment graph. Constructor equations and all
constraints are preserved and reflected by arbitrary graph morphisms, with
no injectivity, acyclicity, solver-success or depth-cutoff premise. The full
structural observation retains both arrow children and both rows. Masked
data observations are an additional corollary, not the function model.

The finite comparison is an explicit parameter. In particular these lemmas
neither replace the requested demand-defined order by data inclusion nor
assert completeness of the old structural relation. Semantic constructor
equations use comparison in both directions; literal equality of regular
syntax is stronger and is not reflected from observations.

Still needed for the principal solver: construct regular assignments for
arbitrary accepted graphs with unguarded tail dependencies, then prove their
arbitrary-parameter soundness and retraction. Transporting a supplied
independent assignment does not discharge that construction.
-/

namespace Yulang.PresenceOpenTailTransport

open Inference
open RegularValueTypes (Layer Graph observe)
open OpenRecordConstraintGraph (Node Edge)

universe u v w

variable {Row : Type u} {State : Type v} {Target : Type w} {m n : Nat}

/-- Lattice children and the full tail are spliced at the same layer.
Only actual constructor payloads become guarded state references. -/
def nodeLayer (graph : Graph Row State) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → State) (rows : Fin m → Row) (value : Fin n → State) :
    Node m n → Layer Row State
  | .input index => graph (input index)
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (graph (value first)) (graph (value last))
  | .inter first last => .inter (graph (value first)) (graph (value last))
  | .pair first last => .pair (value first) (value last)
  | .emptyRecord => .emptyRecord
  | .recordExtend label head tail => .record label (value head) (graph (value tail))
  | .variant label payload => .variant label (value payload)
  | .arrow inputValue inputRow outputValue outputRow =>
      .arrow (value inputValue) (TypeConstraintGraph.rowEval empty join rows inputRow)
        (value outputValue) (TypeConstraintGraph.rowEval empty join rows outputRow)

/-- At outer depth `depth + 1`, the payload is observed at `depth`,
whereas the open tail is observed at the unchanged `depth + 1`. -/
theorem record_observe (graph : Graph Row State) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → State) (rows : Fin m → Row) (value : Fin n → State)
    (label : Nat) (head tail : Fin n) (depth : Nat) :
    (nodeLayer graph empty join input rows value (.recordExtend label head tail)).eval
        (observe graph depth) =
      .record label (observe graph depth (value head)) (observe graph (depth + 1) (value tail)) := rfl

theorem union_observe (graph : Graph Row State) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → State) (rows : Fin m → Row) (value : Fin n → State)
    (first last : Fin n) (depth : Nat) :
    (nodeLayer graph empty join input rows value (.union first last)).eval (observe graph depth) =
      .union (observe graph (depth + 1) (value first))
        (observe graph (depth + 1) (value last)) := rfl

/-- Arrow observations retain both rows and both guarded value children. -/
theorem arrow_observe (graph : Graph Row State) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → State) (rows : Fin m → Row) (value : Fin n → State)
    (arg result : Fin n) (argRow resultRow : RowTerm (Fin m)) (depth : Nat) :
    (nodeLayer graph empty join input rows value (.arrow arg argRow result resultRow)).eval
        (observe graph depth) =
      .arrow (observe graph depth (value arg)) (TypeConstraintGraph.rowEval empty join rows argRow)
        (observe graph depth (value result)) (TypeConstraintGraph.rowEval empty join rows resultRow) := rfl

/-- Exact layer transport, including arbitrary open tails. No state is
duplicated or replaced by a fresh parameter. -/
theorem nodeLayer_map (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (value : Fin n → State) (node : Node m n) :
    (nodeLayer source empty join input rows value node).map rename =
      nodeLayer target empty join (rename ∘ input) rows (rename ∘ value) node := by
  cases node <;> simp only [nodeLayer, Layer.map, Function.comp_apply, commutes]

/-- Every finite structural observation agrees exactly, before applying
any particular subtype relation or any data projection. -/
theorem node_observe_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (value : Fin n → State) (node : Node m n) (depth : Nat) :
    (nodeLayer target empty join (rename ∘ input) rows (rename ∘ value) node).eval
        (observe target depth) =
      (nodeLayer source empty join input rows value node).eval (observe source depth) := by
  rw [← nodeLayer_map source target rename commutes]
  exact RegularValueTypes.eval_morphism target rename commutes depth _

/-- All-depth comparison is independent of graph syntax and of any solver.
The caller supplies the finite comparison, for example a demand comparison. -/
def LayerLe (graph : Graph Row State) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (left right : Layer Row State) : Prop :=
  ∀ depth, compare (left.eval (observe graph depth)) (right.eval (observe graph depth))

def LayerEq (graph : Graph Row State) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (left right : Layer Row State) : Prop :=
  LayerLe graph compare left right ∧ LayerLe graph compare right left

def Realizes (graph : Graph Row State) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (nodes : OpenRecordConstraintGraph.Graph m n) (value : Fin n → State) : Prop :=
  ∀ index, LayerEq graph compare (graph (value index))
    (nodeLayer graph empty join input rows value (nodes index))

def Satisfies (graph : Graph Row State)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (constraints : List (Edge n)) (value : Fin n → State) : Prop :=
  ∀ edge ∈ constraints, LayerLe graph compare (graph (value edge.1)) (graph (value edge.2))

def Models (graph : Graph Row State) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (nodes : OpenRecordConstraintGraph.Graph m n)
    (constraints : List (Edge n)) (value : Fin n → State) : Prop :=
  Realizes graph compare empty join input rows nodes value ∧
    Satisfies graph compare constraints value

theorem layerLe_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (left right : Layer Row State) :
    LayerLe target compare (left.map rename) (right.map rename) ↔
      LayerLe source compare left right := by
  simp only [LayerLe, RegularValueTypes.eval_morphism target rename commutes]

theorem layerEq_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (left right : Layer Row State) :
    LayerEq target compare (left.map rename) (right.map rename) ↔
      LayerEq source compare left right := by
  simp only [LayerEq, layerLe_morphism source target rename commutes]

/-- Constructor equations are preserved and reflected for every original
slot assignment, including sharing and cycles. -/
theorem realizes_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (nodes : OpenRecordConstraintGraph.Graph m n) (value : Fin n → State) :
    Realizes target compare empty join (rename ∘ input) rows nodes (rename ∘ value) ↔
      Realizes source compare empty join input rows nodes value := by
  unfold Realizes
  apply forall_congr'
  intro index
  rw [Function.comp_apply, ← commutes, ← nodeLayer_map source target rename commutes]
  exact layerEq_morphism source target rename commutes compare _ _

theorem satisfies_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (constraints : List (Edge n)) (value : Fin n → State) :
    Satisfies target compare constraints (rename ∘ value) ↔
      Satisfies source compare constraints value := by
  unfold Satisfies
  apply forall_congr'
  intro edge
  apply forall_congr'
  intro _
  simp only [Function.comp_apply, ← commutes,
    layerLe_morphism source target rename commutes]

/-- Open-tail constraints and all semantic constructor equations survive
the same graph embedding. The statement quantifies over all finite input
graphs and independent assignments, not only accepted solver branches. -/
theorem models_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (nodes : OpenRecordConstraintGraph.Graph m n)
    (constraints : List (Edge n)) (value : Fin n → State) :
    Models target compare empty join (rename ∘ input) rows nodes constraints (rename ∘ value) ↔
      Models source compare empty join input rows nodes constraints value :=
  and_congr (realizes_morphism source target rename commutes compare empty join input rows nodes value)
    (satisfies_morphism source target rename commutes compare constraints value)

/-! ## Masked observations do not spend the tail's depth -/

/-- This is an observation refinement used for transport, not a proposed
replacement for the producer-to-demand order. -/
def MaskedCompare (left right : StructuralBase.Ty Row) : Prop :=
  ∀ hidden, PresenceDataTypes.Le (PresenceLegacyBridge.translate left hidden)
    (PresenceLegacyBridge.translate right hidden)

theorem node_masked_observe_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (value : Fin n → State) (node : Node m n)
    (depth : Nat) (hidden : List Nat) (item : SourceDataRuntime.Value) :
    PresenceLegacyBridge.translate
        ((nodeLayer target empty join (rename ∘ input) rows (rename ∘ value) node).eval
          (observe target depth)) hidden item ↔
      PresenceLegacyBridge.translate
        ((nodeLayer source empty join input rows value node).eval (observe source depth))
          hidden item := by
  rw [node_observe_morphism source target rename commutes]

/-- Masking a record passes the enlarged mask to the tail at the same
outer depth. The guarded payload starts unmasked one level below. -/
theorem record_mask_depth (graph : Graph Row State) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → State) (rows : Fin m → Row) (value : Fin n → State)
    (label : Nat) (head tail : Fin n) (depth : Nat) (hidden : List Nat)
    (item : SourceDataRuntime.Value) :
    PresenceLegacyBridge.translate
        ((nodeLayer graph empty join input rows value (.recordExtend label head tail)).eval
          (observe graph depth)) hidden item ↔
      ((if label ∈ hidden then PresenceDataTypes.records
          else PresenceDataTypes.required label
            (PresenceLegacyBridge.translate (observe graph depth (value head)) [])) item ∧
        PresenceLegacyBridge.translate (observe graph (depth + 1) (value tail))
          (label :: hidden) item) := Iff.rfl

theorem masked_models_morphism (source : Graph Row State) (target : Graph Row Target)
    (rename : State → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (empty : Row) (join : Row → Row → Row) (input : Fin m → State)
    (rows : Fin m → Row) (nodes : OpenRecordConstraintGraph.Graph m n)
    (constraints : List (Edge n)) (value : Fin n → State) :
    Models target MaskedCompare empty join (rename ∘ input) rows nodes constraints (rename ∘ value) ↔
      Models source MaskedCompare empty join input rows nodes constraints value :=
  models_morphism source target rename commutes MaskedCompare empty join input rows nodes constraints value

/-! ## Connection to the actual compiler's regular assignments -/

/-- This model records only the choice of finite comparison. Its constructors
and rows are exactly those of the existing full regular carrier. -/
def observationModel (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop) : Inference.Model :=
  { RegularInferenceModel.model Row empty join leRow with
    subTy := LayerLe (RegularInferenceModel.graph Row) compare }

/-- `nodeLayer` is the interpretation of the actual open constraint node,
including the complete tail, in the existing common regular carrier. -/
theorem nodeLayer_eval (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (value : Fin n → RegularInferenceModel.Ty Row) (node : Node m n) :
    nodeLayer (RegularInferenceModel.graph Row) empty join
        (RegularInferenceModel.State.node ∘ input) rows (RegularInferenceModel.State.node ∘ value) node =
      node.eval (observationModel empty join leRow compare) input rows value := by
  cases node <;> rfl

/-- Semantic realization is independent of the representation of a regular
value. Literal compiler realization implies it, but is not equated with it. -/
def SemanticRealizes (model : Inference.Model) (input : Fin m → model.Ty)
    (rows : Fin m → model.Row) (nodes : OpenRecordConstraintGraph.Graph m n)
    (value : Fin n → model.Ty) : Prop :=
  ∀ index, model.subTy (value index) ((nodes index).eval model input rows value) ∧
    model.subTy ((nodes index).eval model input rows value) (value index)

theorem semanticRealizes_exact (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (nodes : OpenRecordConstraintGraph.Graph m n) (value : Fin n → RegularInferenceModel.Ty Row) :
    Realizes (RegularInferenceModel.graph Row) compare empty join
        (RegularInferenceModel.State.node ∘ input) rows nodes
        (RegularInferenceModel.State.node ∘ value) ↔
      SemanticRealizes (observationModel empty join leRow compare) input rows nodes value := by
  unfold Realizes SemanticRealizes
  apply forall_congr'
  intro index
  simp only [Function.comp_apply, RegularInferenceModel.graph_node,
    nodeLayer_eval empty join leRow compare, LayerEq]
  rfl

theorem satisfies_exact (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (constraints : List (Edge n)) (value : Fin n → RegularInferenceModel.Ty Row) :
    Satisfies (RegularInferenceModel.graph Row) compare constraints
        (RegularInferenceModel.State.node ∘ value) ↔
      OpenRecordConstraintGraph.Satisfies (observationModel empty join leRow compare)
        constraints value := Iff.rfl

/-- The original raw equations suffice; no syntactic injectivity of finite
observations is assumed in the reverse direction. -/
theorem semanticRealizes_of_eq (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (compareRefl : ∀ type, compare type type)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (nodes : OpenRecordConstraintGraph.Graph m n) (value : Fin n → RegularInferenceModel.Ty Row)
    (realized : OpenRecordConstraintGraph.Realizes (observationModel empty join leRow compare)
      input rows nodes value) :
    SemanticRealizes (observationModel empty join leRow compare) input rows nodes value := by
  intro index
  change LayerEq (RegularInferenceModel.graph Row) compare (value index)
    ((nodes index).eval (observationModel empty join leRow compare) input rows value)
  rw [realized index]
  exact ⟨fun _ => compareRefl _, fun _ => compareRefl _⟩

/-- The total source-constraint compiler's extension satisfies every
constructor equation at every finite depth. Open tails are expanded at the
same depth without any restriction on the original input assignment. -/
theorem compile_extend_observe_exact (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (problem : ConstraintProblems.Problem m) (input : Fin m → RegularInferenceModel.Ty Row)
    (rows : Fin m → Row) (index : Fin (OpenRecordConstraintGraph.compile problem).size) (depth : Nat) :
    let model := observationModel empty join leRow compare
    let compiled := OpenRecordConstraintGraph.compile problem
    let value := compiled.extend model input rows
    (value index).eval (observe (RegularInferenceModel.graph Row) depth) =
      (nodeLayer (RegularInferenceModel.graph Row) empty join
        (RegularInferenceModel.State.node ∘ input) rows (RegularInferenceModel.State.node ∘ value)
        (compiled.graph index)).eval (observe (RegularInferenceModel.graph Row) depth) := by
  dsimp only
  have first := congrArg (fun layer => layer.eval (observe (RegularInferenceModel.graph Row) depth))
    (OpenRecordConstraintGraph.compile_realizes (observationModel empty join leRow compare)
      problem input rows index)
  have last := nodeLayer_eval empty join leRow compare input rows
    ((OpenRecordConstraintGraph.compile problem).extend
      (observationModel empty join leRow compare) input rows)
    ((OpenRecordConstraintGraph.compile problem).graph index)
  exact first.trans (congrArg
    (fun layer => layer.eval (observe (RegularInferenceModel.graph Row) depth)) last).symm

/-- All constraints, including row constraints, are preserved and reflected
on the actual total compiler extension of every original assignment. This is
assignment transport, not construction of an arbitrary-parameter solution. -/
theorem compile_extend_models_exact (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (compareRefl : ∀ type, compare type type) (problem : ConstraintProblems.Problem m)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row) :
    let model := observationModel empty join leRow compare
    let compiled := OpenRecordConstraintGraph.compile problem
    let value := compiled.extend model input rows
    (Models (RegularInferenceModel.graph Row) compare empty join
        (RegularInferenceModel.State.node ∘ input) rows compiled.graph compiled.constraints
        (RegularInferenceModel.State.node ∘ value) ∧
      ConstraintProblems.RowHolds model rows compiled.rows) ↔ problem.Holds model input rows := by
  dsimp only
  let model := observationModel empty join leRow compare
  let compiled := OpenRecordConstraintGraph.compile problem
  let value := compiled.extend model input rows
  have realized := OpenRecordConstraintGraph.compile_realizes model problem input rows
  have semantic : Realizes (RegularInferenceModel.graph Row) compare empty join
      (RegularInferenceModel.State.node ∘ input) rows compiled.graph
      (RegularInferenceModel.State.node ∘ value) :=
    (semanticRealizes_exact empty join leRow compare input rows compiled.graph value).mpr
      (semanticRealizes_of_eq empty join leRow compare compareRefl input rows compiled.graph value realized)
  change (Models _ _ _ _ _ _ _ _ _ ∧ _) ↔ _
  unfold Models
  rw [and_iff_right semantic]
  change (OpenRecordConstraintGraph.Satisfies model compiled.constraints value ∧
      ConstraintProblems.RowHolds model rows compiled.rows) ↔ problem.Holds model input rows
  have compiledExact := OpenRecordConstraintGraph.compile_extend_exact model problem input rows
  have restricts := OpenRecordConstraintGraph.compile_restrict_extend model problem input rows
  change (OpenRecordConstraintGraph.Realizes model (compiled.restrict value) rows compiled.graph value ∧
    OpenRecordConstraintGraph.Satisfies model compiled.constraints value ∧
    ConstraintProblems.RowHolds model rows compiled.rows) ↔ problem.Holds model input rows at compiledExact
  rw [restricts, and_iff_right realized] at compiledExact
  exact compiledExact

/-! ## Finite blocks preserve the same-depth tail interpretation -/

theorem block_models_exact {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ RegularInferenceModel.State Row))
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (empty : Row) (join : Row → Row → Row)
    (input : Fin m → Fin size ⊕ RegularInferenceModel.State Row) (rows : Fin m → Row)
    (nodes : OpenRecordConstraintGraph.Graph m n) (constraints : List (Edge n))
    (value : Fin n → Fin size ⊕ RegularInferenceModel.State Row) :
    Models (RegularInferenceModel.graph Row) compare empty join
        (RegularInferenceModel.blockRef body ∘ input) rows nodes constraints
        (RegularInferenceModel.blockRef body ∘ value) ↔
      Models (RegularInferenceModel.blockGraph body) compare empty join input rows nodes constraints value :=
  models_morphism (RegularInferenceModel.blockGraph body) (RegularInferenceModel.graph Row)
    (RegularInferenceModel.blockRef body) (RegularInferenceModel.block_morphism body)
    compare empty join input rows nodes constraints value

theorem finite_models_exact {size : Nat} (source : RegularValueTypes.FiniteGraph Row size)
    (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (empty : Row) (join : Row → Row → Row) (input : Fin m → Fin size) (rows : Fin m → Row)
    (nodes : OpenRecordConstraintGraph.Graph m n) (constraints : List (Edge n))
    (value : Fin n → Fin size) :
    Models (RegularInferenceModel.graph Row) compare empty join
        (RegularInferenceModel.finiteRef source ∘ input) rows nodes constraints
        (RegularInferenceModel.finiteRef source ∘ value) ↔
      Models source compare empty join input rows nodes constraints value :=
  models_morphism source (RegularInferenceModel.graph Row)
    (RegularInferenceModel.finiteRef source) (RegularInferenceModel.finite_morphism source)
    compare empty join input rows nodes constraints value

namespace Examples

def graph : Graph Unit Bool
  | false => .base .int
  | true => .emptyRecord

def values : Fin 2 → Bool := fun index => index.val = 1

/-- The very first layer already contains the entire empty tail.
A uniform decrement of both children would put `bottom` in its place. -/
theorem open_tail_at_depth_zero :
    (nodeLayer graph () (fun _ _ => ()) (fun index : Fin 0 => nomatch index)
      (fun _ => ()) values (.recordExtend 7 0 1)).eval (observe graph 0) =
      StructuralBase.Ty.record 7 .bottom .emptyRecord := rfl

theorem masked_open_tail_survives :
    PresenceLegacyBridge.translate
      ((nodeLayer graph () (fun _ _ => ()) (fun index : Fin 0 => nomatch index)
        (fun _ => ()) values (.recordExtend 7 0 1)).eval (observe graph 0))
      [7] (.record .nil) := by
  simp [open_tail_at_depth_zero, PresenceLegacyBridge.translate,
    PresenceDataTypes.inter, PresenceDataTypes.records]

/-- Spending a payload step at the tail loses a valid masked observation. -/
theorem naive_guarded_tail_loses_masked_observation :
    ¬ PresenceLegacyBridge.translate
      (StructuralBase.Ty.record (RowType := Unit) 7 .bottom .bottom) [7] (.record .nil) := by
  simp [PresenceLegacyBridge.translate, PresenceDataTypes.inter, PresenceDataTypes.never]

/-- Even at depth zero, an arrow is retained as an arrow with its row labels. -/
theorem arrow_is_not_empty_projection :
    (nodeLayer graph () (fun _ _ => ()) (fun index : Fin 0 => nomatch index)
      (fun _ => ()) values (.arrow 0 .empty 1 .empty)).eval (observe graph 0) ≠
      StructuralBase.Ty.bottom := by
  intro impossible
  cases impossible

end Examples

end Yulang.PresenceOpenTailTransport
