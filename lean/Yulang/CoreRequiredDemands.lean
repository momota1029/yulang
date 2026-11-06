import Yulang.PresenceRegularLegacyBridge

/-! The common finite required-demand fragment of the two layer languages.
This is a bidirectional data interpretation, not a reflection theorem for
structural subtyping or a connection between their inference results. -/

namespace Yulang.Core.RequiredDemands

open PresenceLayers (Layer)
open SourceDataRuntime (Value)

universe u v
variable {State : Type u} {Row : Type v}

/-- Optional and absent demands have no constructor in the legacy language.
Payload references remain unrestricted, including references into cycles. -/
def Required : Layer State → Prop
  | .union left right | .inter left right => Required left ∧ Required right
  | .optional _ _ | .lacks _ => False
  | _ => True

/-- Re-encode a finite demand, keeping width records as width records. -/
def encode : (layer : Layer State) → Required layer → RegularValueTypes.Layer Row State
  | .bottom, _ => .bottom
  | .top, _ => .top
  | .base name, _ => .base name
  | .union left right, valid => .union (encode left valid.1) (encode right valid.2)
  | .inter left right, valid => .inter (encode left valid.1) (encode right valid.2)
  | .pair left right, _ => .pair left right
  | .variant label payload, _ => .variant label payload
  | .records, _ => .emptyRecord
  | .required label payload, _ => .record label payload .emptyRecord
  | .optional _ _, impossible => False.elim impossible
  | .lacks _, impossible => False.elim impossible

theorem required_mask (layer : Layer State) (valid : Required layer) (hidden : List Nat) :
    Required (layer.mask hidden) := by
  induction layer with
  | union left right ihl ihr | inter left right ihl ihr =>
      exact ⟨ihl valid.1, ihr valid.2⟩
  | required label payload =>
      by_cases masked : label ∈ hidden <;> simp [Layer.mask, masked, Required]
  | optional | lacks => cases valid
  | _ => trivial

/-- Every legacy layer projects into this fragment. Arrows retain the old
data projection to bottom; this statement does not interpret closures. -/
theorem translate_required (layer : RegularValueTypes.Layer Row State) :
    Required (PresenceRegularLegacyBridge.translate layer) := by
  induction layer with
  | union left right ihl ihr | inter left right ihl ihr => exact ⟨ihl, ihr⟩
  | record label payload tail ih => exact ⟨trivial, required_mask _ ih [label]⟩
  | _ => trivial

/-- All predicate assignments, masks and values. No inhabitation, finite
enumeration of parameters, or subtype hypotheses are required. -/
theorem encode_exact (assignment : State → PresenceDataTypes.Ty)
    (layer : Layer State) (valid : Required layer) (hidden : List Nat) (value : Value) :
    (PresenceRegularLegacyBridge.translate (encode (Row := Row) layer valid)).meaning
        assignment hidden value ↔ layer.meaning assignment hidden value := by
  induction layer with
  | union left right ihl ihr => exact or_congr (ihl valid.1) (ihr valid.2)
  | inter left right ihl ihr => exact and_congr (ihl valid.1) (ihr valid.2)
  | required label payload =>
      by_cases masked : label ∈ hidden
      · simp [encode, PresenceRegularLegacyBridge.translate, Layer.record, Layer.meaning,
          Layer.mask, masked, PresenceDataTypes.inter]
      · simp only [encode, PresenceRegularLegacyBridge.translate, Layer.record, Layer.mask,
          Layer.meaning, masked, ↓reduceIte, PresenceDataTypes.inter]
        change (PresenceDataTypes.required label (assignment payload) value ∧
            PresenceDataTypes.records value) ↔ PresenceDataTypes.required label (assignment payload) value
        exact ⟨And.left, fun held => ⟨held, held.1⟩⟩
  | optional | lacks => cases valid
  | _ => rfl

/-- Exact membership in the independently defined finite legacy meaning.
This is preservation and reflection of demands, not of structural subtyping. -/
theorem finite_exact (assignment : State → StructuralBase.Ty Row)
    (layer : Layer State) (valid : Required layer) (hidden : List Nat) (value : Value) :
    layer.meaning (fun state => PresenceLegacyBridge.translate (assignment state) []) hidden value ↔
      DataTypeSemantics.Holds ((encode layer valid).eval assignment)
        (fun label => label ∈ hidden) value :=
  (encode_exact (Row := Row) _ layer valid hidden value).symm.trans
    ((PresenceRegularLegacyBridge.translate_exact assignment hidden (encode layer valid) value).trans
      (PresenceLegacyBridge.translate_exact _ hidden value))

end Yulang.Core.RequiredDemands
