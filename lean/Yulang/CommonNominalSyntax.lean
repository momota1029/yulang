import Yulang.CommonNominalFinite
import Yulang.RegularInferenceModel

/-!
# Finite layers and closed regular blocks for the common carrier

Payload references consume a constructor depth. Record tails, default sources,
unions, intersections and masks stay at the current depth. A block contains
finite syntax and natural-number references; out-of-range references denote
bottom. Closing a block preserves its independent recursive interpretation.

The legacy state constructor is a structural embedding of existing finite
regular syntax, not a solver result or a semantic certificate. It lets old
graphs be reused without duplicating their shared state trees.
-/

namespace Yulang.CommonNominalSyntax

open Inference (Base)

universe u v w z

inductive Layer (Row : Type u) (Index : Type v) where
  | base : Base → Layer Row Index
  | bottom : Layer Row Index
  | top : Layer Row Index
  | union : Layer Row Index → Layer Row Index → Layer Row Index
  | inter : Layer Row Index → Layer Row Index → Layer Row Index
  | pair : Index → Index → Layer Row Index
  | emptyRecord : Layer Row Index
  | exactEmpty : Layer Row Index
  | record : Nat → Index → Layer Row Index → Layer Row Index
  | recordDefault : Nat → Layer Row Index → Index → Layer Row Index
  | variant : Nat → Index → Layer Row Index
  | arrow : Index → Row → Index → Row → Layer Row Index
  | mask : List Nat → Layer Row Index → Layer Row Index
  | nominal : Nat → List (Index ⊕ Row) → Layer Row Index

namespace Layer

variable {Row : Type u} {Index : Type v}

def map {Target : Type w} (rename : Index → Target) : Layer Row Index → Layer Row Target
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (map rename first) (map rename last)
  | .inter first last => .inter (map rename first) (map rename last)
  | .pair first last => .pair (rename first) (rename last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label head tail => .record label (rename head) (map rename tail)
  | .recordDefault label source fallback => .recordDefault label (map rename source) (rename fallback)
  | .variant label payload => .variant label (rename payload)
  | .arrow arg argRow result resultRow => .arrow (rename arg) argRow (rename result) resultRow
  | .mask hidden source => .mask hidden (map rename source)
  | .nominal name arguments => .nominal name (arguments.map (Sum.map rename id))

@[simp] theorem map_id (layer : Layer Row Index) : layer.map id = layer := by
  induction layer <;> simp [map, *]
  case nominal name arguments =>
    congr 1
    apply List.map_id

@[simp] theorem map_comp {Middle : Type w} {Target : Type z}
    (first : Index → Middle) (last : Middle → Target) (layer : Layer Row Index) :
    (layer.map first).map last = layer.map (last ∘ first) := by
  induction layer <;> simp [map, Function.comp_def, *, List.map_map]
  case nominal name arguments =>
    congr 1
    apply List.map_congr_left
    intro argument _
    cases argument <;> rfl

def evalAt (depth : Nat) (assignment : Index → CommonNominalFinite.Ty Row) : Layer Row Index → CommonNominalFinite.Ty Row
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (evalAt depth assignment first) (evalAt depth assignment last)
  | .inter first last => .inter (evalAt depth assignment first) (evalAt depth assignment last)
  | .pair first last => .pair (assignment first) (assignment last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label head tail => .record label (assignment head) (evalAt depth assignment tail)
  | .recordDefault label source fallback =>
      match depth with
      | 0 => .record label .bottom (evalAt 0 assignment source)
      | _ + 1 => .recordDefault label (evalAt depth assignment source) (assignment fallback)
  | .variant label payload => .variant label (assignment payload)
  | .arrow arg argRow result resultRow => .arrow (assignment arg) argRow (assignment result) resultRow
  | .mask hidden source => .mask hidden (evalAt depth assignment source)
  | .nominal name arguments => .nominal name (arguments.map (Sum.map assignment id))

@[simp] theorem evalAt_map (depth : Nat) {Target : Type w} (rename : Index → Target)
    (assignment : Target → CommonNominalFinite.Ty Row) (layer : Layer Row Index) :
    (layer.map rename).evalAt depth assignment = layer.evalAt depth (assignment ∘ rename) := by
  induction layer <;> simp [map, evalAt, Function.comp_def, *]
  case recordDefault => cases depth <;> simp_all [Function.comp_def]
  case nominal name arguments =>
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro argument _
    cases argument <;> rfl

end Layer

abbrev Graph (Row : Type u) (Index : Type v) := Index → Layer Row Index

def observe (source : Graph Row Index) : Nat → Index → CommonNominalFinite.Ty Row
  | 0, _ => .bottom
  | depth + 1, index => (source index).evalAt depth (observe source depth)

theorem observe_morphism (source : Graph Row Index) (target : Graph Row Target)
    (rename : Index → Target)
    (commutes : ∀ index, (source index).map rename = target (rename index))
    (depth : Nat) (index : Index) :
    observe target depth (rename index) = observe source depth index := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih =>
      simp only [observe, ← commutes, Layer.evalAt_map]
      congr 1
      funext child
      exact ih child

theorem eval_morphism (source : Graph Row Index) (target : Graph Row Target)
    (rename : Index → Target)
    (commutes : ∀ index, (source index).map rename = target (rename index))
    (depth : Nat) (layer : Layer Row Index) :
    (layer.map rename).evalAt depth (observe target depth) = layer.evalAt depth (observe source depth) := by
  rw [Layer.evalAt_map]
  congr 1
  funext child
  exact observe_morphism source target rename commutes depth child

def ofOldLayer : RegularValueTypes.Layer Row Index → Layer Row Index
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (ofOldLayer first) (ofOldLayer last)
  | .inter first last => .inter (ofOldLayer first) (ofOldLayer last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .record label payload rest => .record label payload (ofOldLayer rest)
  | .variant label payload => .variant label payload
  | .arrow arg argRow result resultRow => .arrow arg argRow result resultRow

inductive State (Row : Type u) where
  | node : Layer Row (State Row) → State Row
  | block : List (Layer Row (Nat ⊕ State Row)) → Nat → State Row
  | legacy : RegularInferenceModel.State Row → State Row

abbrev Ty (Row : Type u) := Layer Row (State Row)

def rawRef {Row : Type u} (body : List (Layer Row (Nat ⊕ State Row))) : Nat ⊕ State Row → State Row :=
  Sum.elim (State.block body) id

def graph (Row : Type u) : Graph Row (State Row)
  | .node layer => layer
  | .block body root => (body[root]?.getD .bottom).map (rawRef body)
  | .legacy state => (ofOldLayer (RegularInferenceModel.graph Row state)).map State.legacy

@[simp] theorem graph_node {Row : Type u} (layer : Ty Row) : graph Row (.node layer) = layer := rfl

def blockBody {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) : List (Layer Row (Nat ⊕ State Row)) :=
  List.ofFn fun index => (body index).map (Sum.map Fin.val id)

def closeBlock {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) (root : Fin size) : State Row :=
  .block (blockBody body) root.val

def blockRef {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) : Fin size ⊕ State Row → State Row :=
  Sum.elim (closeBlock body) id

@[simp] theorem graph_closeBlock {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) (root : Fin size) :
    graph Row (closeBlock body root) = (body root).map (blockRef body) := by
  simp only [closeBlock, graph, blockBody, List.getElem?_ofFn, root.isLt, ↓reduceDIte,
    Option.getD_some, Layer.map_comp]
  congr 1
  funext index
  cases index <;> rfl

def blockGraph {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) : Graph Row (Fin size ⊕ State Row)
  | .inl index => body index
  | .inr state => (graph Row state).map Sum.inr

theorem block_morphism {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) (state : Fin size ⊕ State Row) :
    (blockGraph body state).map (blockRef body) = graph Row (blockRef body state) := by
  cases state with
  | inl index => exact (graph_closeBlock body index).symm
  | inr state =>
      simp only [blockGraph, Layer.map_comp]
      change (graph Row state).map id = graph Row state
      exact Layer.map_id _

theorem block_observe_exact {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (depth : Nat) (state : Fin size ⊕ State Row) :
    observe (graph Row) depth (blockRef body state) = observe (blockGraph body) depth state :=
  observe_morphism (blockGraph body) (graph Row) (blockRef body) (block_morphism body) depth state

def embedOld {Row : Type u} (type : RegularInferenceModel.Ty Row) : Ty Row :=
  (ofOldLayer type).map State.legacy

end Yulang.CommonNominalSyntax
