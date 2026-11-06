import Yulang.PresenceDataTypes

/-!
# Finite presence layers with unrestricted payload parameters

This is the finite representation step of the presence-inference integration
plan. Required, optional and absent demands are distinct constructors. Union
and intersection retain correlations between different fields; no projection
to a map of independent field bounds is performed. Child references may be
assigned arbitrary predicates, not only exact descriptors or a finite sample
of runtime values.

`check_exact` connects executable membership to the independent predicate
interpretation, assuming exact membership decisions for the child parameters.
`mask_exact` removes only demands on shadowed outer fields; it does not mask
the payload of an unrelated pair, variant or field. The old width type maps
to `records`, never to absence. There is no function or effect interpretation
in this first-order data layer, and no whole-source inference entrypoint.
-/

namespace Yulang.PresenceLayers

open SourceDataRuntime
open Inference (Base)

universe u v w

inductive Layer (State : Type u) where
  | bottom
  | top
  | base : Base → Layer State
  | union : Layer State → Layer State → Layer State
  | inter : Layer State → Layer State → Layer State
  | pair : State → State → Layer State
  | variant : Nat → State → Layer State
  | records
  | required : Nat → State → Layer State
  | optional : Nat → State → Layer State
  | lacks : Nat → Layer State
  deriving Repr, DecidableEq

namespace Layer

variable {State : Type u}

/-- Independently interpreted finite demands. Masking forgets a hidden field's
demand but still requires the input to be a record. Payloads start unmasked. -/
def meaning (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat) :
    Layer State → PresenceDataTypes.Ty
  | .bottom => PresenceDataTypes.never
  | .top => PresenceDataTypes.any
  | .base name => PresenceDataTypes.base name
  | .union left right => PresenceDataTypes.union (meaning assignment hidden left) (meaning assignment hidden right)
  | .inter left right => PresenceDataTypes.inter (meaning assignment hidden left) (meaning assignment hidden right)
  | .pair left right => PresenceDataTypes.pair (assignment left) (assignment right)
  | .variant label payload => PresenceDataTypes.variant label (assignment payload)
  | .records => PresenceDataTypes.records
  | .required label payload => if label ∈ hidden then PresenceDataTypes.records
      else PresenceDataTypes.required label (assignment payload)
  | .optional label payload => if label ∈ hidden then PresenceDataTypes.records
      else PresenceDataTypes.optional label (assignment payload)
  | .lacks label => if label ∈ hidden then PresenceDataTypes.records else PresenceDataTypes.lacks label

def denote (assignment : State → PresenceDataTypes.Ty) : Layer State → PresenceDataTypes.Ty :=
  meaning assignment []

def check (childCheck : State → Value → Bool) : Layer State → Value → Bool
  | .bottom, _ => false
  | .top, _ => true
  | .base expected, .base actual => decide (actual = expected)
  | .base _, _ => false
  | .union left right, value => check childCheck left value || check childCheck right value
  | .inter left right, value => check childCheck left value && check childCheck right value
  | .pair left right, .pair first last => childCheck left first && childCheck right last
  | .pair _ _, _ => false
  | .variant label payload, .variant name value => decide (name = label) && childCheck payload value
  | .variant _ _, _ => false
  | .records, .record _ => true
  | .records, _ => false
  | .required label payload, .record fields =>
      match Fields.lookup label fields with
      | none => false
      | some value => childCheck payload value
  | .required _ _, _ => false
  | .optional label payload, .record fields =>
      match Fields.lookup label fields with
      | none => true
      | some value => childCheck payload value
  | .optional _ _, _ => false
  | .lacks label, .record fields => (Fields.lookup label fields).isNone
  | .lacks _, _ => false

/-- All parameter predicates remain universally quantified. This is exact
membership, not a subtyping decision or sampling of payload inhabitants. -/
theorem check_exact (childCheck : State → Value → Bool)
    (assignment : State → PresenceDataTypes.Ty)
    (childExact : ∀ state value, childCheck state value = true ↔ assignment state value)
    (layer : Layer State) (value : Value) :
    check childCheck layer value = true ↔ denote assignment layer value := by
  induction layer generalizing value with
  | bottom | top => simp [check, denote, meaning, PresenceDataTypes.never, PresenceDataTypes.any]
  | base name =>
      cases value <;> simp [check, denote, meaning, PresenceDataTypes.base, PresenceDataTypes.exact]
  | union left right ihl ihr =>
      simp only [check, Bool.or_eq_true, denote, meaning, PresenceDataTypes.union]
      exact or_congr (ihl value) (ihr value)
  | inter left right ihl ihr =>
      simp only [check, Bool.and_eq_true, denote, meaning, PresenceDataTypes.inter]
      exact and_congr (ihl value) (ihr value)
  | pair left right =>
      cases value <;> simp [check, denote, meaning, PresenceDataTypes.pair, childExact]
  | variant label payload =>
      cases value <;> simp [check, denote, meaning, PresenceDataTypes.variant, childExact]
  | records => cases value <;> simp [check, denote, meaning, PresenceDataTypes.records]
  | required label payload =>
      cases value with
      | record fields =>
          cases found : Fields.lookup label fields <;>
            simp [check, denote, meaning, PresenceDataTypes.required, PresenceDataTypes.records,
              PresenceDataTypes.lookup, found, childExact]
      | base | pair | variant =>
          simp [check, denote, meaning, PresenceDataTypes.required, PresenceDataTypes.records]
  | optional label payload =>
      cases value with
      | record fields =>
          cases found : Fields.lookup label fields <;>
            simp [check, denote, meaning, PresenceDataTypes.optional, PresenceDataTypes.records,
              PresenceDataTypes.lookup, found, childExact]
      | base | pair | variant =>
          simp [check, denote, meaning, PresenceDataTypes.optional, PresenceDataTypes.records]
  | lacks label =>
      cases value with
      | record fields =>
          cases found : Fields.lookup label fields <;>
            simp [check, denote, meaning, PresenceDataTypes.lacks, PresenceDataTypes.records,
              PresenceDataTypes.lookup, found]
      | base | pair | variant =>
          simp [check, denote, meaning, PresenceDataTypes.lacks, PresenceDataTypes.records]

/-- Erase outer demands only. An absent demand behind a winning field is
discarded just as a present demand is; neither constrains the winning value. -/
def mask (hidden : List Nat) : Layer State → Layer State
  | .bottom => .bottom
  | .top => .top
  | .base name => .base name
  | .union left right => .union (mask hidden left) (mask hidden right)
  | .inter left right => .inter (mask hidden left) (mask hidden right)
  | .pair left right => .pair left right
  | .variant label payload => .variant label payload
  | .records => .records
  | .required label payload => if label ∈ hidden then .records else .required label payload
  | .optional label payload => if label ∈ hidden then .records else .optional label payload
  | .lacks label => if label ∈ hidden then .records else .lacks label

theorem mask_exact (assignment : State → PresenceDataTypes.Ty) (hidden : List Nat)
    (layer : Layer State) (value : Value) :
    denote assignment (mask hidden layer) value ↔ meaning assignment hidden layer value := by
  induction layer with
  | union left right ihl ihr =>
      exact or_congr ihl ihr
  | inter left right ihl ihr =>
      exact and_congr ihl ihr
  | required label payload | optional label payload =>
      by_cases present : label ∈ hidden <;> simp [mask, denote, meaning, present]
  | lacks label =>
      by_cases present : label ∈ hidden <;> simp [mask, denote, meaning, present]
  | _ => rfl

@[simp] theorem mask_nil (layer : Layer State) : layer.mask [] = layer := by
  induction layer <;> simp [mask, *]

theorem mask_congr (left right : List Nat) (same : ∀ label, label ∈ left ↔ label ∈ right)
    (layer : Layer State) : layer.mask left = layer.mask right := by
  induction layer <;> simp [mask, *]

theorem mask_append (first last : List Nat) (layer : Layer State) :
    (layer.mask first).mask last = layer.mask (first ++ last) := by
  induction layer with
  | union left right ihl ihr | inter left right ihl ihr => simp [mask, ihl, ihr]
  | required label payload | optional label payload =>
      by_cases a : label ∈ first <;> by_cases b : label ∈ last <;> simp [mask, a, b]
  | lacks label =>
      by_cases a : label ∈ first <;> by_cases b : label ∈ last <;> simp [mask, a, b]
  | _ => rfl

theorem meaning_mask (assignment : State → PresenceDataTypes.Ty)
    (first last : List Nat) (layer : Layer State) (value : Value) :
    meaning assignment last (layer.mask first) value ↔ meaning assignment (first ++ last) layer value := by
  rw [← mask_exact, mask_append, mask_exact]

theorem mask_idempotent (hidden : List Nat) (layer : Layer State) :
    (layer.mask hidden).mask hidden = layer.mask hidden := by
  rw [mask_append]
  apply mask_congr
  intro label
  simp

def map {Target : Type v} (rename : State → Target) : Layer State → Layer Target
  | .bottom => .bottom
  | .top => .top
  | .base name => .base name
  | .union left right => .union (map rename left) (map rename right)
  | .inter left right => .inter (map rename left) (map rename right)
  | .pair left right => .pair (rename left) (rename right)
  | .variant label payload => .variant label (rename payload)
  | .records => .records
  | .required label payload => .required label (rename payload)
  | .optional label payload => .optional label (rename payload)
  | .lacks label => .lacks label

@[simp] theorem map_id (layer : Layer State) : layer.map id = layer := by
  induction layer <;> simp [map, *]

@[simp] theorem map_comp {Middle : Type v} {Target : Type w}
    (first : State → Middle) (last : Middle → Target) (layer : Layer State) :
    (layer.map first).map last = layer.map (fun state => last (first state)) := by
  induction layer <;> simp [map, *]

theorem meaning_map {Target : Type v} (rename : State → Target)
    (assignment : Target → PresenceDataTypes.Ty) (hidden : List Nat) (layer : Layer State) :
    meaning assignment hidden (layer.map rename) = meaning (fun state => assignment (rename state)) hidden layer := by
  induction layer <;> simp [map, meaning, *]

theorem denote_map {Target : Type v} (rename : State → Target)
    (assignment : Target → PresenceDataTypes.Ty) (layer : Layer State) :
    denote assignment (layer.map rename) = denote (fun state => assignment (rename state)) layer :=
  meaning_map rename assignment [] layer

theorem map_mask {Target : Type v} (rename : State → Target)
    (hidden : List Nat) (layer : Layer State) :
    (layer.mask hidden).map rename = (layer.map rename).mask hidden := by
  induction layer with
  | union left right ihl ihr | inter left right ihl ihr => simp [map, mask, ihl, ihr]
  | required label payload | optional label payload =>
      by_cases present : label ∈ hidden <;> simp [map, mask, present]
  | lacks label =>
      by_cases present : label ∈ hidden <;> simp [map, mask, present]
  | _ => rfl

theorem meaning_congr (left right : State → PresenceDataTypes.Ty)
    (same : ∀ state value, left state value ↔ right state value)
    (hidden : List Nat) (layer : Layer State) (value : Value) :
    meaning left hidden layer value ↔ meaning right hidden layer value := by
  have equal : left = right := by
    funext state item
    exact propext (same state item)
  rw [equal]

/-- First-field-wins demand construction, as opposed to a value constructor
image. Its tail may contain arbitrary unions and intersections. -/
def record (label : Nat) (payload : State) (tail : Layer State) : Layer State :=
  .inter (.required label payload) (tail.mask [label])

theorem record_shadow (assignment : State → PresenceDataTypes.Ty)
    (label : Nat) (visible hiddenPayload : State) (tail : Layer State) (value : Value) :
    denote assignment (record label visible (record label hiddenPayload tail)) value ↔
      denote assignment (record label visible tail) value := by
  simp only [record, mask, List.mem_cons_self, ↓reduceIte, mask_idempotent,
    denote, meaning, List.not_mem_nil, ↓reduceIte, PresenceDataTypes.inter]
  change (_ ∧ (PresenceDataTypes.records value ∧ _)) ↔ (_ ∧ _)
  constructor
  · intro valid
    exact ⟨valid.1, valid.2.2⟩
  · intro valid
    exact ⟨valid.1, valid.1.1, valid.2⟩

end Layer

/-! A concrete correlation that independent optional-field bounds lose. -/

def correlated : Layer Base :=
  .union (.inter (.required 0 .int) (.lacks 1))
    (.inter (.lacks 0) (.required 1 .str))

def independentlyOptional : Layer Base :=
  .inter (.optional 0 .int) (.optional 1 .str)

theorem independent_fields_lose_correlation :
    ¬ PresenceDataTypes.Le (Layer.denote PresenceDataTypes.base independentlyOptional)
      (Layer.denote PresenceDataTypes.base correlated) := by
  intro below
  have admitted : Layer.denote PresenceDataTypes.base independentlyOptional
      (.record [(0, .base .int), (1, .base .str)]) := by
    simp [independentlyOptional, Layer.denote, Layer.meaning, PresenceDataTypes.inter,
      PresenceDataTypes.optional, PresenceDataTypes.records, PresenceDataTypes.lookup,
      Fields.lookup, PresenceDataTypes.base, PresenceDataTypes.exact]
  have impossible := below _ admitted
  simp [correlated, Layer.denote, Layer.meaning, PresenceDataTypes.union, PresenceDataTypes.inter,
    PresenceDataTypes.required, PresenceDataTypes.lacks, PresenceDataTypes.records,
    PresenceDataTypes.lookup, Fields.lookup] at impossible

end Yulang.PresenceLayers
