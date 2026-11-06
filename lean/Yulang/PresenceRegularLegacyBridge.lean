import Yulang.PresenceRegularObservations
import Yulang.PresenceLegacyBridge
import Yulang.RegularInferenceModel

/-!
# Exact data projection of the old regular layers

The old required-field graph projects compositionally into finite presence
layers. Every finite observation of every graph agrees with the existing
`DataTypeSemantics.Holds`, including first-field-wins masking below arbitrary
unions and intersections. This is a data interpretation: arrows project to
`bottom`, as in `PresenceLegacyBridge`. It does not identify structural
subtyping with predicate inclusion or replace the old inference model.

The new regular layer also has optional and absent fields which this legacy
projection cannot generate. Its block closure is independently available in
`PresenceRegularObservations.Blocks`; the final theorem here connects the
existing common regular carrier's block closure to the same data meaning.
-/

namespace Yulang.PresenceRegularLegacyBridge

open SourceDataRuntime (Value)

universe u v w

variable {Row : Type u} {Index : Type v}

def translate : RegularValueTypes.Layer Row Index → PresenceLayers.Layer Index
  | .base name => .base name
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (translate left) (translate right)
  | .inter left right => .inter (translate left) (translate right)
  | .pair left right => .pair left right
  | .emptyRecord => .records
  | .record label payload tail => PresenceLayers.Layer.record label payload (translate tail)
  | .variant label payload => .variant label payload
  | .arrow _ _ _ _ => .bottom

/-- No restriction is placed on child types, masks, record tails or values.
In particular, a hidden field inside either branch of a union is forgotten. -/
theorem translate_exact (assignment : Index → StructuralBase.Ty Row)
    (hidden : List Nat) (layer : RegularValueTypes.Layer Row Index) (value : Value) :
    (translate layer).meaning (fun state => PresenceLegacyBridge.translate (assignment state) [])
        hidden value ↔
      PresenceLegacyBridge.translate (layer.eval assignment) hidden value := by
  induction layer generalizing hidden value with
  | base | bottom | top | pair | emptyRecord | variant | arrow => rfl
  | union left right ihl ihr => exact or_congr (ihl hidden value) (ihr hidden value)
  | inter left right ihl ihr => exact and_congr (ihl hidden value) (ihr hidden value)
  | record label payload tail ih =>
      change (_ ∧ _) ↔ (_ ∧ _)
      apply and_congr Iff.rfl
      exact (PresenceLayers.Layer.meaning_mask _ [label] hidden (translate tail) value).trans
        (ih (label :: hidden) value)

theorem translate_map {Target : Type w} (rename : Index → Target)
    (layer : RegularValueTypes.Layer Row Index) :
    translate (layer.map rename) = (translate layer).map rename := by
  induction layer with
  | union left right ihl ihr | inter left right ihl ihr =>
      simp [RegularValueTypes.Layer.map, translate, PresenceLayers.Layer.map, ihl, ihr]
  | record label payload tail ih =>
      simp [RegularValueTypes.Layer.map, translate, PresenceLayers.Layer.record,
        PresenceLayers.Layer.map, PresenceLayers.Layer.map_mask, ih]
  | _ => rfl

def graph (source : RegularValueTypes.Graph Row Index) : PresenceRegularObservations.Graph Index :=
  fun state => translate (source state)

/-- Every old graph, every finite depth and every runtime data value have the
same membership in the new observation and the old finite-data translation. -/
theorem observe_exact (source : RegularValueTypes.Graph Row Index)
    (depth : Nat) (state : Index) (value : Value) :
    PresenceRegularObservations.observe (graph source) depth state value ↔
      PresenceLegacyBridge.translate (RegularValueTypes.observe source depth state) [] value := by
  induction depth generalizing state value with
  | zero => rfl
  | succ depth ih =>
      change (translate (source state)).meaning _ [] value ↔ _
      exact (PresenceLayers.Layer.meaning_congr _ _ ih [] (translate (source state)) value).trans
        (translate_exact (RegularValueTypes.observe source depth) [] (source state) value)

/-- The executable presence checker decides the old independent data meaning
of any finite regular observation. This is not an all-depth subtype test. -/
theorem check_exact (source : RegularValueTypes.Graph Row Index)
    (depth : Nat) (state : Index) (value : Value) :
    PresenceRegularObservations.check (graph source) depth state value = true ↔
      DataTypeSemantics.Holds (RegularValueTypes.observe source depth state)
        DataTypeSemantics.visible value :=
  (PresenceRegularObservations.check_exact (graph source) depth state value).trans
    ((observe_exact source depth state value).trans
      (PresenceLegacyBridge.translate_visible (RegularValueTypes.observe source depth state) value))

/-- The same bridge for an arbitrary outer layer, including a union or
intersection of graph references, rather than only one graph node. -/
theorem layer_exact (source : RegularValueTypes.Graph Row Index)
    (depth : Nat) (layer : RegularValueTypes.Layer Row Index) (value : Value) :
    (translate layer).denote (PresenceRegularObservations.observe (graph source) depth) value ↔
      DataTypeSemantics.Holds (layer.eval (RegularValueTypes.observe source depth))
        DataTypeSemantics.visible value :=
  (PresenceLayers.Layer.meaning_congr _ _ (observe_exact source depth) [] (translate layer) value).trans
    ((translate_exact (RegularValueTypes.observe source depth) [] layer value).trans
      (PresenceLegacyBridge.translate_visible (layer.eval (RegularValueTypes.observe source depth)) value))

/-- Inclusion at every finite data observation is preserved and reflected.
The right side deliberately uses data membership, not structural subtyping. -/
theorem data_subtype_exact (source : RegularValueTypes.Graph Row Index)
    (left right : RegularValueTypes.Layer Row Index) :
    PresenceRegularObservations.DataSubtype (graph source) (translate left) (translate right) ↔
      ∀ depth value,
        DataTypeSemantics.Holds (left.eval (RegularValueTypes.observe source depth))
          DataTypeSemantics.visible value →
        DataTypeSemantics.Holds (right.eval (RegularValueTypes.observe source depth))
          DataTypeSemantics.visible value := by
  constructor
  · intro below depth value valid
    exact (layer_exact source depth right value).mp
      (below depth value ((layer_exact source depth left value).mpr valid))
  · intro below depth value valid
    exact (layer_exact source depth right value).mpr
      (below depth value ((layer_exact source depth left value).mp valid))

/-- Existing finite block closure also preserves and reflects every projected
data observation. Both internal and external roots are quantified. -/
theorem legacy_block_observe_exact {size : Nat}
    (body : Fin size → RegularValueTypes.Layer Row (Fin size ⊕ RegularInferenceModel.State Row))
    (depth : Nat) (state : Fin size ⊕ RegularInferenceModel.State Row) (value : Value) :
    PresenceRegularObservations.observe (graph (RegularInferenceModel.graph Row))
        depth (RegularInferenceModel.blockRef body state) value ↔
      PresenceRegularObservations.observe (graph (RegularInferenceModel.blockGraph body))
        depth state value := by
  rw [observe_exact, observe_exact, RegularInferenceModel.block_observe]

end Yulang.PresenceRegularLegacyBridge
