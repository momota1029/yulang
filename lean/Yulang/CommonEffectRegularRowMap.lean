import Yulang.CommonEffectFiniteRowMap

/-! Whole Common regular-row transport commutes with every constructor
observation. The generic automorphism theorem is then specialized to the
actual signed transports, including arbitrary short and infinite rows. -/
namespace Yulang.CommonEffectRegularRowMap
open Common (Ty Row)
open CommonSyntax (Layer State graph observe)
open CommonEffectTypeRowMap (layer type state blockLayer blockList ref oldState oldType oldBlockLayer oldBlockList oldRef)

def oldLayer (onRow : Row → Row) (onRef : α → β) : RegularValueTypes.Layer Row α → RegularValueTypes.Layer Row β
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (oldLayer onRow onRef a) (oldLayer onRow onRef b)
  | .inter a b => .inter (oldLayer onRow onRef a) (oldLayer onRow onRef b)
  | .pair a b => .pair (onRef a) (onRef b)
  | .emptyRecord => .emptyRecord
  | .record label head tail => .record label (onRef head) (oldLayer onRow onRef tail)
  | .variant label payload => .variant label (onRef payload)
  | .arrow arg incoming result outgoing => .arrow (onRef arg) (onRow incoming) (onRef result) (onRow outgoing)

theorem oldLayer_map (onRow : Row → Row) (first : α → β) (last : β → γ) (source : RegularValueTypes.Layer Row α) :
    oldLayer onRow last (source.map first) = oldLayer onRow (last ∘ first) source := by
  induction source <;> simp_all only [RegularValueTypes.Layer.map, oldLayer, Function.comp_apply]

theorem map_oldLayer (onRow : Row → Row) (first : α → β) (last : β → γ) (source : RegularValueTypes.Layer Row α) :
    (oldLayer onRow first source).map last = oldLayer onRow (last ∘ first) source := by
  induction source <;> simp_all only [RegularValueTypes.Layer.map, oldLayer, Function.comp_apply]

theorem layer_map (onRow : Row → Row) (first : α → β) (last : β → γ) (source : Layer Row α) :
    layer onRow last (source.map first) = layer onRow (last ∘ first) source := by
  induction source <;> simp_all only [Layer.map, layer, Function.comp_apply]

theorem map_layer (onRow : Row → Row) (first : α → β) (last : β → γ) (source : Layer Row α) :
    (layer onRow first source).map last = layer onRow (last ∘ first) source := by
  induction source <;> simp_all only [Layer.map, layer, Function.comp_apply]

theorem oldType_layer (onRow : Row → Row) (source : RegularValueTypes.Layer Row (RegularInferenceModel.State Row)) :
    oldType onRow source = oldLayer onRow (oldState onRow) source := by
  induction source <;> simp_all only [oldType, oldLayer]

theorem oldBlockLayer_layer (onRow : Row → Row) (source : RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row)) :
    oldBlockLayer onRow source = oldLayer onRow (oldRef onRow) source := by
  induction source <;> simp_all only [oldBlockLayer, oldLayer]

theorem type_layer (onRow : Row → Row) (source : Layer Row (State Row)) :
    type onRow source = layer onRow (state onRow) source := by
  induction source <;> simp_all only [type, layer]

theorem blockLayer_layer (onRow : Row → Row) (source : Layer Row (Nat ⊕ State Row)) :
    blockLayer onRow source = layer onRow (ref onRow) source := by
  induction source <;> simp_all only [blockLayer, layer]

theorem oldBlockList_map (onRow : Row → Row) (body : List (RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row))) :
    oldBlockList onRow body = body.map (oldBlockLayer onRow) := by
  induction body <;> simp_all only [oldBlockList, List.map]

theorem oldBlockList_get (onRow : Row → Row) (body : List (RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row))) (root : Nat) :
    (oldBlockList onRow body)[root]?.getD .bottom = oldBlockLayer onRow (body[root]?.getD .bottom) := by
  rw [oldBlockList_map, List.getElem?_map]
  cases body[root]? <;> rfl

theorem blockList_map (onRow : Row → Row) (body : List (Layer Row (Nat ⊕ State Row))) :
    blockList onRow body = body.map (blockLayer onRow) := by
  induction body <;> simp_all only [blockList, List.map]

theorem blockList_get (onRow : Row → Row) (body : List (Layer Row (Nat ⊕ State Row))) (root : Nat) :
    (blockList onRow body)[root]?.getD .bottom = blockLayer onRow (body[root]?.getD .bottom) := by
  rw [blockList_map, List.getElem?_map]
  cases body[root]? <;> rfl

theorem old_raw_ref (onRow : Row → Row) (body : List (RegularValueTypes.Layer Row (Nat ⊕ RegularInferenceModel.State Row)))
    (index : Nat ⊕ RegularInferenceModel.State Row) :
    RegularInferenceModel.rawBlockRef (oldBlockList onRow body) (oldRef onRow index) =
      oldState onRow (RegularInferenceModel.rawBlockRef body index) := by
  cases index <;> rfl

theorem raw_ref (onRow : Row → Row) (body : List (Layer Row (Nat ⊕ State Row))) (index : Nat ⊕ State Row) :
    CommonSyntax.rawRef (blockList onRow body) (ref onRow index) = state onRow (CommonSyntax.rawRef body index) := by
  cases index <;> rfl

theorem old_state_graph (onRow : Row → Row) (source : RegularInferenceModel.State Row) :
    RegularInferenceModel.graph Row (oldState onRow source) = oldLayer onRow (oldState onRow) (RegularInferenceModel.graph Row source) := by
  cases source with
  | node body => exact oldType_layer onRow body
  | block body root =>
    simp only [oldState, RegularInferenceModel.graph, oldBlockList_get, oldBlockLayer_layer, map_oldLayer, oldLayer_map]
    congr 1
    funext index
    exact old_raw_ref onRow body index

theorem ofOld_layer (onRow : Row → Row) (onRef : α → β) (source : RegularValueTypes.Layer Row α) :
    CommonSyntax.ofOldLayer (oldLayer onRow onRef source) = layer onRow onRef (CommonSyntax.ofOldLayer source) := by
  induction source <;> simp_all only [oldLayer, layer, CommonSyntax.ofOldLayer]

theorem state_graph (onRow : Row → Row) (source : State Row) :
    graph Row (state onRow source) = layer onRow (state onRow) (graph Row source) := by
  cases source with
  | node body => exact type_layer onRow body
  | block body root =>
    simp only [state, graph, blockList_get, blockLayer_layer, map_layer, layer_map]
    congr 1
    funext index
    exact raw_ref onRow body index
  | legacy source =>
    simp only [state, graph, old_state_graph, ofOld_layer, map_layer, layer_map]
    rfl

theorem layer_factor (onRow : Row → Row) (onRef : α → β) (source : Layer Row α) :
    layer onRow onRef source = (layer onRow id source).map onRef := by
  induction source <;> simp_all only [layer, Layer.map, id]

theorem layer_eval (onRow : Row → Row) (source : Layer Row α) (depth : Nat) (values : α → CommonFinite.Ty Row) :
    (layer onRow id source).evalAt depth (fun name => CommonEffectFiniteRowMap.type onRow (values name)) =
      CommonEffectFiniteRowMap.type onRow (source.evalAt depth values) := by
  induction source <;> simp_all only [layer, Layer.evalAt, CommonEffectFiniteRowMap.type, id]
  case recordDefault => cases depth <;> simp_all only [CommonEffectFiniteRowMap.type]

theorem observe_state (onRow : Row → Row) (depth : Nat) (source : State Row) :
    observe (graph Row) depth (state onRow source) = CommonEffectFiniteRowMap.type onRow (observe (graph Row) depth source) := by
  induction depth generalizing source with
  | zero => rfl
  | succ depth ih =>
    rw [observe, state_graph, layer_factor, Layer.evalAt_map]
    have same : observe (graph Row) depth ∘ state onRow =
        fun name => CommonEffectFiniteRowMap.type onRow (observe (graph Row) depth name) := funext ih
    rw [same, layer_eval]
    rfl

theorem observe_type (onRow : Row → Row) (depth : Nat) (source : Ty) :
    Common.observeTy depth (type onRow source) = CommonEffectFiniteRowMap.type onRow (Common.observeTy depth source) := by
  rw [Common.observeTy, type_layer, layer_factor, Layer.evalAt_map]
  have same : observe (graph Row) depth ∘ state onRow =
      fun name => CommonEffectFiniteRowMap.type onRow (observe (graph Row) depth name) := funext (observe_state onRow depth)
  rw [same, layer_eval]
  rfl

theorem subtype_exact (first last : Row → Row) (leftInverse : ∀ row, last (first row) = row)
    (rightInverse : ∀ row, first (last row) = row)
    (rowsExact : ∀ a b, Common.rowLe (first a) (first b) ↔ Common.rowLe a b) (source target : Ty) :
    Common.Subtype (type first source) (type first target) ↔ Common.Subtype source target := by
  change (∀ depth, CommonFinite.ProducerLe Common.rowLe _ _) ↔ (∀ depth, CommonFinite.ProducerLe Common.rowLe _ _)
  apply forall_congr'; intro depth
  rw [observe_type, observe_type]
  exact CommonEffectFiniteRowMap.producerLe_exact first last leftInverse rightInverse rowsExact _ _

theorem transport_rowLe_exact (scope : Nat) (permission : CommonEffectRequestGeneration.Permission) (delta : Int)
    (first last : Row) :
    Common.rowLe (CommonSignedRows.transport scope permission.allows delta first)
      (CommonSignedRows.transport scope permission.allows delta last) ↔ Common.rowLe first last := by
  constructor
  · intro included occurrence member
    have moved : CommonSignedRows.transport scope permission.allows delta first
        (CommonSignedRows.shiftOccurrence scope permission.allows delta occurrence) := by
      simpa only [CommonSignedRows.transport, CommonSignedRows.shiftOccurrence_inverse] using member
    simpa only [CommonSignedRows.transport, CommonSignedRows.shiftOccurrence_inverse] using included _ moved
  · intro included occurrence member
    exact included _ member

theorem transport_subtype_exact (scope : Nat) (permission : CommonEffectRequestGeneration.Permission) (delta : Int)
    (source target : Ty) :
    Common.Subtype (type (CommonSignedRows.transport scope permission.allows delta) source)
      (type (CommonSignedRows.transport scope permission.allows delta) target) ↔ Common.Subtype source target := by
  apply subtype_exact _ (CommonSignedRows.transport scope permission.allows (-delta))
  · exact CommonSignedRows.transport_inverse scope permission.allows delta
  · intro row
    simpa only [Int.neg_neg] using CommonSignedRows.transport_inverse scope permission.allows (-delta) row
  · exact transport_rowLe_exact scope permission delta

theorem transport_equivalent_exact (scope : Nat) (permission : CommonEffectRequestGeneration.Permission) (delta : Int)
    (source target : Ty) :
    Common.Equivalent (type (CommonSignedRows.transport scope permission.allows delta) source)
      (type (CommonSignedRows.transport scope permission.allows delta) target) ↔ Common.Equivalent source target :=
  and_congr (transport_subtype_exact scope permission delta source target)
    (transport_subtype_exact scope permission delta target source)

end Yulang.CommonEffectRegularRowMap
