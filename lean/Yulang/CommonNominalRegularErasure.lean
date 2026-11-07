import Yulang.CommonNominalFiniteErasure
import Yulang.CommonNominalFullModelMap

/-!
# Block-preserving erasure of intermediate old-source witnesses

This auxiliary erasure retains each supplied finite block body and root, and
all references and rows in preserved old structural positions. Entire nominal
argument lists are discarded with their atomic heads; payloads occurring only
there are not retained. This map never defines the language carrier.
-/

namespace Yulang.CommonNominalRegularErasure

abbrev Row := Common.Row
abbrev NewState := CommonNominalSyntax.State Row
abbrev OldState := CommonSyntax.State Row
abbrev New := CommonNominalFullCarrier.Ty
abbrev Old := Common.Ty

mutual
  def layer : CommonNominalSyntax.Layer Row (NewState) → CommonSyntax.Layer Row (OldState)
    | .base scalar => .base scalar
    | .float | .nominal _ _ => .base .unit
    | .bottom => .bottom
    | .top => .top
    | .union first last => .union (layer first) (layer last)
    | .inter first last => .inter (layer first) (layer last)
    | .pair first last => .pair (state first) (state last)
    | .emptyRecord => .emptyRecord
    | .exactEmpty => .exactEmpty
    | .record label payload rest => .record label (state payload) (layer rest)
    | .recordDefault label source fallback => .recordDefault label (layer source) (state fallback)
    | .variant label payload => .variant label (state payload)
    | .arrow input incoming output outgoing => .arrow (state input) incoming (state output) outgoing
    | .mask hidden source => .mask hidden (layer source)

  def openLayer : CommonNominalSyntax.Layer Row (Nat ⊕ NewState) → CommonSyntax.Layer Row (Nat ⊕ OldState)
    | .base scalar => .base scalar
    | .float | .nominal _ _ => .base .unit
    | .bottom => .bottom
    | .top => .top
    | .union first last => .union (openLayer first) (openLayer last)
    | .inter first last => .inter (openLayer first) (openLayer last)
    | .pair first last => .pair (openRef first) (openRef last)
    | .emptyRecord => .emptyRecord
    | .exactEmpty => .exactEmpty
    | .record label payload rest => .record label (openRef payload) (openLayer rest)
    | .recordDefault label source fallback => .recordDefault label (openLayer source) (openRef fallback)
    | .variant label payload => .variant label (openRef payload)
    | .arrow input incoming output outgoing => .arrow (openRef input) incoming (openRef output) outgoing
    | .mask hidden source => .mask hidden (openLayer source)

  def state : NewState → OldState
    | .node type => .node (layer type)
    | .block layers root => .block (body layers) root
    | .legacy old => .legacy old
    | .common old => old

  def openRef : Nat ⊕ NewState → Nat ⊕ OldState
    | .inl index => .inl index
    | .inr external => .inr (state external)

  def body : List (CommonNominalSyntax.Layer Row (Nat ⊕ NewState)) →
      List (CommonSyntax.Layer Row (Nat ⊕ OldState))
    | [] => []
    | first :: rest => openLayer first :: body rest
end

private def outer : CommonNominalSyntax.Layer Row Index → CommonSyntax.Layer Row Index
  | .base scalar => .base scalar
  | .float | .nominal _ _ => .base .unit
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (outer first) (outer last)
  | .inter first last => .inter (outer first) (outer last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload rest => .record label payload (outer rest)
  | .recordDefault label source fallback => .recordDefault label (outer source) fallback
  | .variant label payload => .variant label payload
  | .arrow input incoming output outgoing => .arrow input incoming output outgoing
  | .mask hidden source => .mask hidden (outer source)

private theorem layer_outer (type : New) : layer type = (outer type).map state := by
  induction type <;> simp [layer, outer, CommonSyntax.Layer.map, *]

private theorem open_outer (type : CommonNominalSyntax.Layer Row (Nat ⊕ NewState)) :
    openLayer type = (outer type).map openRef := by
  induction type <;> simp [openLayer, outer, CommonSyntax.Layer.map, *]

private theorem outer_map (rename : Index → Target) (type : CommonNominalSyntax.Layer Row Index) :
    outer (type.map rename) = (outer type).map rename := by
  induction type <;>
    simp [outer, CommonNominalSyntax.Layer.map, CommonSyntax.Layer.map, *]

private theorem outer_common (type : CommonSyntax.Layer Row Index) :
    outer (CommonNominalSyntax.ofCommonLayer type) = type := by
  induction type <;> simp [outer, CommonNominalSyntax.ofCommonLayer, *]

private theorem outer_legacy (type : RegularValueTypes.Layer Row Index) :
    outer (CommonNominalSyntax.ofOldLayer type) = CommonSyntax.ofOldLayer type := by
  induction type <;> simp [outer, CommonNominalSyntax.ofOldLayer, CommonSyntax.ofOldLayer, *]

private theorem body_get (layers : List (CommonNominalSyntax.Layer Row (Nat ⊕ NewState))) (root : Nat) :
    (body layers)[root]?.getD .bottom = openLayer (layers[root]?.getD .bottom) := by
  induction layers generalizing root with
  | nil => simp [body, openLayer]
  | cons first rest ih => cases root <;> simp [body, ih]

private theorem rawRef_commutes (layers : List (CommonNominalSyntax.Layer Row (Nat ⊕ NewState))) :
    state ∘ CommonNominalSyntax.rawRef layers = CommonSyntax.rawRef (body layers) ∘ openRef := by
  funext reference
  cases reference <;> rfl

/-- All finite block bodies and all root indices, including out-of-range
indices. Block back references retain their exact numeric indices. -/
theorem graph_commutes (reference : NewState) :
    layer (CommonNominalSyntax.graph Row reference) = CommonSyntax.graph Row (state reference) := by
  cases reference with
  | node type => rfl
  | block layers root =>
      simp only [CommonNominalSyntax.graph, state, CommonSyntax.graph, body_get,
        layer_outer, outer_map, open_outer, CommonSyntax.Layer.map_comp, rawRef_commutes]
  | common old =>
      simp only [CommonNominalSyntax.graph, state, layer_outer, outer_map, outer_common,
        CommonSyntax.Layer.map_comp]
      change (CommonSyntax.graph Row old).map id = CommonSyntax.graph Row old
      exact CommonSyntax.Layer.map_id _
  | legacy old =>
      simp only [CommonNominalSyntax.graph, state, CommonSyntax.graph, layer_outer,
        outer_map, outer_legacy, CommonSyntax.Layer.map_comp]
      rfl

private theorem outer_eval (depth : Nat)
    (assignment : Index → CommonNominalFullDemand.Ty Row)
    (type : CommonNominalSyntax.Layer Row Index) :
    (outer type).evalAt depth (CommonNominalFiniteErasure.erase ∘ assignment) =
      CommonNominalFiniteErasure.erase (type.evalAt depth assignment) := by
  induction type <;> simp_all [outer, CommonNominalSyntax.Layer.evalAt,
    CommonSyntax.Layer.evalAt, CommonNominalFiniteErasure.erase, Function.comp_def]
  case recordDefault => cases depth <;>
    simp_all [CommonNominalFiniteErasure.erase]

private theorem layer_eval (depth : Nat)
    (newAssignment : NewState → CommonNominalFullDemand.Ty Row)
    (oldAssignment : OldState → CommonFinite.Ty Row)
    (same : ∀ reference, oldAssignment (state reference) =
      CommonNominalFiniteErasure.erase (newAssignment reference)) (type : New) :
    (layer type).evalAt depth oldAssignment =
      CommonNominalFiniteErasure.erase (type.evalAt depth newAssignment) := by
  rw [layer_outer, CommonSyntax.Layer.evalAt_map]
  have agree : oldAssignment ∘ state = CommonNominalFiniteErasure.erase ∘ newAssignment := funext same
  rw [agree]
  exact outer_eval depth newAssignment type

/-- Every constructor depth, arbitrary nested regular states, defaults and
masks. No finite unfolding bound is a premise of the order theorem. -/
theorem state_observe (depth : Nat) (reference : NewState) :
    CommonSyntax.observe (CommonSyntax.graph Row) depth (state reference) =
      CommonNominalFiniteErasure.erase
        (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth reference) := by
  induction depth generalizing reference with
  | zero => rfl
  | succ depth ih =>
      simp only [CommonSyntax.observe, CommonNominalSyntax.observe, ← graph_commutes]
      exact layer_eval depth _ _ ih _

theorem observe_layer (depth : Nat) (type : New) :
    Common.observeTy depth (layer type) =
      CommonNominalFiniteErasure.erase (CommonNominalFullCarrier.observeTy depth type) :=
  layer_eval depth _ _ (state_observe depth) type

/-- Actual full-carrier subtype implies actual old Common subtype of the
block-preserving witness erasures, with every negative rank/environment. -/
theorem subtype_monotone (first last : New)
    (below : CommonNominalFullCarrier.Subtype first last) :
    Common.Subtype (layer first) (layer last) := by
  intro depth
  rw [observe_layer, observe_layer]
  exact CommonNominalFiniteErasure.finite_monotone _ _ (below depth)

mutual
  /-- Literal left inverse on every old graph, including shared blocks. -/
  @[simp] theorem layer_value (type : Common.Ty) :
      layer (CommonNominalFullModelMap.value type) = type := by
    cases type <;> simp [CommonNominalFullModelMap.value, CommonNominalModelMap.value,
      layer, layer_value, state_value]
  @[simp] theorem state_value (reference : CommonSyntax.State Row) :
      state (CommonNominalModelMap.state reference) = reference := by
    cases reference <;> simp [CommonNominalModelMap.state, state, layer_value]
end

end Yulang.CommonNominalRegularErasure
