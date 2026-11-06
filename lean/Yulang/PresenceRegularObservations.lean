import Yulang.PresenceLayers

/-!
# Presence-aware regular data observations and finite block closure

Each finite observation keeps the full Boolean combination of presence
demands. Children are guarded by a pair, variant or present-field lookup;
optional absence can succeed without following its child. Membership has a
terminating executable checker at every observation depth.

Graph renaming and closing a finite simultaneous block preserve and reflect
all such observations, including arbitrary external nodes. `DataSubtype`
below is inclusion of first-order data observations, not the existing
structural subtype relation and not a decision procedure for all depths.
No `SourcePrincipalInference` gate or principal theorem is changed.
-/

namespace Yulang.PresenceRegularObservations

open PresenceLayers
open SourceDataRuntime (Value)

universe u v

abbrev Graph (Index : Type u) := Index → Layer Index

variable {Index : Type u}

def observe (graph : Graph Index) : Nat → Index → PresenceDataTypes.Ty
  | 0, _ => PresenceDataTypes.never
  | depth + 1, state => (graph state).denote (observe graph depth)

def check (graph : Graph Index) : Nat → Index → Value → Bool
  | 0, _, _ => false
  | depth + 1, state, value => (graph state).check (check graph depth) value

theorem check_exact (graph : Graph Index) (depth : Nat) (state : Index) (value : Value) :
    check graph depth state value = true ↔ observe graph depth state value := by
  induction depth generalizing state value with
  | zero => simp [check, observe, PresenceDataTypes.never]
  | succ depth ih => exact Layer.check_exact (check graph depth) (observe graph depth) ih (graph state) value

/-- A structural graph morphism preserves and reflects membership at every
depth; injectivity of the renaming and acyclicity of either graph are unnecessary. -/
theorem observe_morphism {Target : Type v} (source : Graph Index) (target : Graph Target)
    (rename : Index → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (depth : Nat) (state : Index) (value : Value) :
    observe target depth (rename state) value ↔ observe source depth state value := by
  induction depth generalizing state value with
  | zero => rfl
  | succ depth ih =>
      simp only [observe, ← commutes state, Layer.denote_map]
      exact Layer.meaning_congr _ _ ih [] (source state) value

theorem layer_morphism {Target : Type v} (source : Graph Index) (target : Graph Target)
    (rename : Index → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (depth : Nat) (layer : Layer Index) (value : Value) :
    (layer.map rename).denote (observe target depth) value ↔ layer.denote (observe source depth) value := by
  rw [Layer.denote_map]
  exact Layer.meaning_congr _ _ (observe_morphism source target rename commutes depth) [] layer value

def DataSubtype (graph : Graph Index) (left right : Layer Index) : Prop :=
  ∀ depth value, left.denote (observe graph depth) value → right.denote (observe graph depth) value

theorem subtype_morphism {Target : Type v} (source : Graph Index) (target : Graph Target)
    (rename : Index → Target)
    (commutes : ∀ state, (source state).map rename = target (rename state))
    (left right : Layer Index) :
    DataSubtype target (left.map rename) (right.map rename) ↔ DataSubtype source left right := by
  constructor
  · intro below depth value present
    exact (layer_morphism source target rename commutes depth right value).mp
      (below depth value ((layer_morphism source target rename commutes depth left value).mpr present))
  · intro below depth value present
    exact (layer_morphism source target rename commutes depth right value).mpr
      (below depth value ((layer_morphism source target rename commutes depth left value).mp present))

namespace Blocks

/-- A common carrier of finite outer layers and finite recursive blocks.
Natural indices are only the stored representation; `close` accepts `Fin`. -/
inductive State where
  | node : Layer State → State
  | block : List (Layer (Nat ⊕ State)) → Nat → State

abbrev Ty := Layer State

def rawRef (body : List (Layer (Nat ⊕ State))) : Nat ⊕ State → State :=
  Sum.elim (State.block body) id

def graph : Graph State
  | .node layer => layer
  | .block body root => (body[root]?.getD .bottom).map (rawRef body)

def body (source : Fin size → Layer (Fin size ⊕ State)) : List (Layer (Nat ⊕ State)) :=
  List.ofFn fun index => (source index).map (Sum.map Fin.val id)

def close (source : Fin size → Layer (Fin size ⊕ State)) (root : Fin size) : State :=
  .block (body source) root.val

def ref (source : Fin size → Layer (Fin size ⊕ State)) : Fin size ⊕ State → State :=
  Sum.elim (close source) id

theorem unfold_close (source : Fin size → Layer (Fin size ⊕ State)) (root : Fin size) :
    graph (close source root) = (source root).map (ref source) := by
  simp only [close, graph, body, List.getElem?_ofFn, root.isLt, ↓reduceDIte,
    Option.getD_some, Layer.map_comp]
  congr 1
  funext state
  cases state <;> rfl

def openGraph (source : Fin size → Layer (Fin size ⊕ State)) : Graph (Fin size ⊕ State)
  | .inl index => source index
  | .inr state => (graph state).map Sum.inr

theorem closure_morphism (source : Fin size → Layer (Fin size ⊕ State))
    (state : Fin size ⊕ State) :
    (openGraph source state).map (ref source) = graph (ref source state) := by
  cases state with
  | inl index => exact (unfold_close source index).symm
  | inr state =>
      simp only [openGraph, Layer.map_comp]
      change (graph state).map id = graph state
      exact Layer.map_id _

/-- Closing the whole finite block changes its representation only. All
depths, input values and both internal and external roots are quantified. -/
theorem close_observe_exact (source : Fin size → Layer (Fin size ⊕ State))
    (depth : Nat) (state : Fin size ⊕ State) (value : Value) :
    observe graph depth (ref source state) value ↔ observe (openGraph source) depth state value :=
  observe_morphism (openGraph source) graph (ref source) (closure_morphism source) depth state value

theorem close_subtype_exact (source : Fin size → Layer (Fin size ⊕ State))
    (left right : Layer (Fin size ⊕ State)) :
    DataSubtype graph (left.map (ref source)) (right.map (ref source)) ↔
      DataSubtype (openGraph source) left right :=
  subtype_morphism (openGraph source) graph (ref source) (closure_morphism source) left right

end Blocks

end Yulang.PresenceRegularObservations
