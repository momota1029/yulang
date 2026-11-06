import Yulang.Common
import Yulang.CommonFinitePresence

/-! # Presence and mask laws on arbitrary common regular parameters -/

namespace Yulang.Common

def MaskedAcceptAt (depth rank : Nat) (env : Environment) (hidden : List Nat)
    (type : Ty) (demand : Demand) : Prop :=
  CommonFinite.MaskedAcceptAt rowLe rank (env.atDepth depth) hidden (observeTy depth type) demand

theorem common_mask_parameter (type : Ty) (hidden : List Nat)
    (depth rank : Nat) (env : Environment) (demand : Demand) :
    AcceptAt depth rank env (mask hidden type) demand ↔
      MaskedAcceptAt depth rank env hidden type demand :=
  CommonFinite.mask_parameter _ hidden rank _ demand

theorem common_mask_composition (type : Ty) (first last : List Nat) :
    Equivalent (mask last (mask first type)) (mask (first ++ last) type) :=
  ⟨fun depth => (CommonFinite.mask_composition (observeTy depth type) first last).1,
    fun depth => (CommonFinite.mask_composition (observeTy depth type) first last).2⟩

theorem common_mask_nil (type : Ty) : Equivalent (mask [] type) type :=
  ⟨fun depth => (CommonFinite.mask_nil (observeTy depth type)).1,
    fun depth => (CommonFinite.mask_nil (observeTy depth type)).2⟩

theorem common_mask_congr (first last : List Nat)
    (same : ∀ label, label ∈ first ↔ label ∈ last) (type : Ty) :
    Equivalent (mask first type) (mask last type) :=
  ⟨fun depth => (CommonFinite.mask_congr first last same (observeTy depth type)).1,
    fun depth => (CommonFinite.mask_congr first last same (observeTy depth type)).2⟩

theorem common_mask_idempotent (type : Ty) (hidden : List Nat) :
    Equivalent (mask hidden (mask hidden type)) (mask hidden type) :=
  ⟨fun depth => (CommonFinite.mask_idempotent (observeTy depth type) hidden).1,
    fun depth => (CommonFinite.mask_idempotent (observeTy depth type) hidden).2⟩

theorem common_mask_required (label : Nat) (payload : Ty) (hidden : List Nat)
    (member : label ∈ hidden) : Equivalent (mask hidden (required label payload)) emptyRecord :=
  ⟨fun _ => (CommonFinite.mask_required label _ hidden member).1,
    fun _ => (CommonFinite.mask_required label _ hidden member).2⟩

theorem exactEmpty_below_width : model.subTy exactEmpty emptyRecord :=
  fun _ => CommonFinite.exactEmpty_below_width

theorem width_not_below_exactEmpty : ¬ model.subTy emptyRecord exactEmpty :=
  fun below => CommonFinite.width_not_below_exactEmpty (below 0)

theorem exactEmpty_not_equivalent_width : ¬ Equivalent exactEmpty emptyRecord :=
  fun same => width_not_below_exactEmpty same.2

theorem common_record_mono (label : Nat) {first last rest tail : Ty}
    (payload : Subtype first last) (remaining : Subtype rest tail) :
    Subtype (record label first rest) (record label last tail) :=
  fun depth => CommonFinite.producerLe_record_mono label (quote_observe_le payload depth) (remaining depth)

theorem common_union_mono {first last first' last' : Ty}
    (left : Subtype first first') (right : Subtype last last') :
    Subtype (.union first last) (.union first' last') :=
  fun depth => CommonFinite.producerLe_union_mono (left depth) (right depth)

theorem common_inter_mono {first last first' last' : Ty}
    (left : Subtype first first') (right : Subtype last last') :
    Subtype (.inter first last) (.inter first' last') :=
  fun depth => CommonFinite.producerLe_inter_mono (left depth) (right depth)

theorem common_union_is_join (first last target : Ty) :
    Subtype (.union first last) target ↔ Subtype first target ∧ Subtype last target := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonFinite.producerLe_union_iff _ _ _).mp (below depth) |>.1,
      fun depth => (CommonFinite.producerLe_union_iff _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨left, right⟩ depth
    exact (CommonFinite.producerLe_union_iff _ _ _).mpr ⟨left depth, right depth⟩

theorem common_inter_is_meet (first last source : Ty) :
    Subtype source (.inter first last) ↔ Subtype source first ∧ Subtype source last := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonFinite.producerLe_inter_iff _ _ _).mp (below depth) |>.1,
      fun depth => (CommonFinite.producerLe_inter_iff _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨left, right⟩ depth
    exact (CommonFinite.producerLe_inter_iff _ _ _).mpr ⟨left depth, right depth⟩

end Yulang.Common
