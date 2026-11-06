import Yulang.CorePresenceGenerationModel

/-!
# A regular representation for the complete presence-generation signature

This is a representation construction over an explicitly supplied finite
`PresenceGeneration.Model`, not the missing concrete demand/function model.
Every operation of that interface is retained, including exact emptiness,
required fields, whole-record default images, arrows and both effect rows.

Record tails and the record source of a default remain in the same finite
outer layer. Field values and default fallback values are guarded payload
references. Finite block closure preserves every observation in every finite
interpretation of the signature; no semantics is chosen for the interface
operations by this file. In particular the `recordDefault` operation is
passed the entire source and fallback values and is not replaced by the
union of a single field's payloads.
-/

namespace Yulang.PresenceOpenTailSignature

open Core.PresenceGeneration (Model)
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
  | required : Nat → Index → Layer Row Index
  | record : Nat → Index → Layer Row Index → Layer Row Index
  | recordDefault : Nat → Layer Row Index → Index → Layer Row Index
  | variant : Nat → Index → Layer Row Index
  | arrow : Index → Row → Index → Row → Layer Row Index

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
  | .required label payload => .required label (rename payload)
  | .record label head tail => .record label (rename head) (map rename tail)
  | .recordDefault label source fallback => .recordDefault label (map rename source) (rename fallback)
  | .variant label payload => .variant label (rename payload)
  | .arrow arg argRow result resultRow => .arrow (rename arg) argRow (rename result) resultRow

@[simp] theorem map_id (layer : Layer Row Index) : layer.map id = layer := by
  induction layer <;> simp [map, *]

@[simp] theorem map_comp {Middle : Type w} {Target : Type z}
    (first : Index → Middle) (last : Middle → Target) (layer : Layer Row Index) :
    (layer.map first).map last = layer.map (last ∘ first) := by
  induction layer <;> simp [map, Function.comp_def, *]

def eval (finite : Model) (assignment : Index → finite.Ty) : Layer finite.Row Index → finite.Ty
  | .base scalar => finite.base scalar
  | .bottom => finite.bottom
  | .top => finite.top
  | .union first last => finite.union (eval finite assignment first) (eval finite assignment last)
  | .inter first last => finite.inter (eval finite assignment first) (eval finite assignment last)
  | .pair first last => finite.pair (assignment first) (assignment last)
  | .emptyRecord => finite.emptyRecord
  | .exactEmpty => finite.exactEmpty
  | .required label payload => finite.required label (assignment payload)
  | .record label head tail => finite.record label (assignment head) (eval finite assignment tail)
  | .recordDefault label source fallback =>
      finite.recordDefault label (eval finite assignment source) (assignment fallback)
  | .variant label payload => finite.variant label (assignment payload)
  | .arrow arg argRow result resultRow => finite.arrow (assignment arg) argRow (assignment result) resultRow

@[simp] theorem eval_map {Target : Type w} (finite : Model) (rename : Index → Target)
    (assignment : Target → finite.Ty) (layer : Layer finite.Row Index) :
    (layer.map rename).eval finite assignment = layer.eval finite (assignment ∘ rename) := by
  induction layer <;> simp [map, eval, Function.comp_def, *]

end Layer

abbrev Graph (Row : Type u) (Index : Type v) := Index → Layer Row Index

def observe (finite : Model) (source : Graph finite.Row Index) : Nat → Index → finite.Ty
  | 0, _ => finite.bottom
  | depth + 1, index => (source index).eval finite (observe finite source depth)

theorem observe_morphism (finite : Model) (source : Graph finite.Row Index)
    (target : Graph finite.Row Target) (rename : Index → Target)
    (commutes : ∀ index, (source index).map rename = target (rename index))
    (depth : Nat) (index : Index) :
    observe finite target depth (rename index) = observe finite source depth index := by
  induction depth generalizing index with
  | zero => rfl
  | succ depth ih =>
      simp only [observe, ← commutes, Layer.eval_map]
      congr 1
      funext child
      exact ih child

theorem eval_morphism (finite : Model) (source : Graph finite.Row Index)
    (target : Graph finite.Row Target) (rename : Index → Target)
    (commutes : ∀ index, (source index).map rename = target (rename index))
    (depth : Nat) (layer : Layer finite.Row Index) :
    (layer.map rename).eval finite (observe finite target depth) =
      layer.eval finite (observe finite source depth) := by
  rw [Layer.eval_map]
  congr 1
  funext child
  exact observe_morphism finite source target rename commutes depth child

inductive State (Row : Type u) where
  | node : Layer Row (State Row) → State Row
  | block : List (Layer Row (Nat ⊕ State Row)) → Nat → State Row

abbrev Ty (Row : Type u) := Layer Row (State Row)

def rawRef {Row : Type u} (body : List (Layer Row (Nat ⊕ State Row))) : Nat ⊕ State Row → State Row :=
  Sum.elim (State.block body) id

def graph (Row : Type u) : Graph Row (State Row)
  | .node layer => layer
  | .block body root => (body[root]?.getD .bottom).map (rawRef body)

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

theorem block_observe_exact (finite : Model) {size : Nat}
    (body : Fin size → Layer finite.Row (Fin size ⊕ State finite.Row))
    (depth : Nat) (state : Fin size ⊕ State finite.Row) :
    observe finite (graph finite.Row) depth (blockRef body state) =
      observe finite (blockGraph body) depth state :=
  observe_morphism finite (blockGraph body) (graph finite.Row) (blockRef body)
    (block_morphism body) depth state

/-- The regular interpretation is parameterized by a finite interpretation
of the complete signature. Establishing that finite interpretation's intended
demand semantics remains a separate obligation. -/
def model (finite : Model) : Model where
  Ty := Ty finite.Row
  Row := finite.Row
  base := .base
  bottom := .bottom
  top := .top
  union := .union
  inter := .inter
  pair := fun first last => .pair (.node first) (.node last)
  emptyRecord := .emptyRecord
  exactEmpty := .exactEmpty
  required := fun label payload => .required label (.node payload)
  record := fun label head tail => .record label (.node head) tail
  recordDefault := fun label source fallback => .recordDefault label source (.node fallback)
  variant := fun label payload => .variant label (.node payload)
  arrow := fun arg argRow result resultRow => .arrow (.node arg) argRow (.node result) resultRow
  empty := finite.empty
  join := finite.join
  subRow := finite.subRow
  subTy := fun left right => ∀ depth, finite.subTy
    (left.eval finite (observe finite (graph finite.Row) depth))
    (right.eval finite (observe finite (graph finite.Row) depth))

/-- The two record constructors remain different in the representation.
This syntactic statement does not assert inequivalence in every finite model. -/
theorem exactEmpty_ne_width (finite : Model) : (model finite).exactEmpty ≠ (model finite).emptyRecord := by
  intro impossible
  cases impossible

/-- Whole-source information is observed at the current outer depth;
fallbacks are field payloads and consume exactly one constructor step. -/
theorem recordDefault_observe (finite : Model) (label : Nat) (source fallback : Ty finite.Row)
    (depth : Nat) :
    ((model finite).recordDefault label source fallback).eval finite
        (observe finite (graph finite.Row) depth) =
      finite.recordDefault label (source.eval finite (observe finite (graph finite.Row) depth))
        (observe finite (graph finite.Row) depth (.node fallback)) := rfl

theorem arrow_observe (finite : Model) (arg result : Ty finite.Row)
    (argRow resultRow : finite.Row) (depth : Nat) :
    ((model finite).arrow arg argRow result resultRow).eval finite
        (observe finite (graph finite.Row) depth) =
      finite.arrow (observe finite (graph finite.Row) depth (.node arg)) argRow
        (observe finite (graph finite.Row) depth (.node result)) resultRow := rfl

end Yulang.PresenceOpenTailSignature
