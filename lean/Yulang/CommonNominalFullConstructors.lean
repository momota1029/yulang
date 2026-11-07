import Yulang.CommonNominalFullModel
import Yulang.CommonNominalFullFinitePresence

/-!
# Regular structural inspectors with arbitrary nominal children

Constructor decomposition, variance and lattice laws are derived from every
extended finite observation. No nominal-free child restriction is used.
-/

namespace Yulang.CommonNominalFullCarrier

open Common (rowLe rowLe_refl rowLe_trans)

def emptyRecord : Ty := .emptyRecord
def exactEmpty : Ty := .exactEmpty
def mask (hidden : List Nat) (type : Ty) : Ty := .mask hidden type

theorem quote_observe_le {first last : Ty} (below : Subtype first last) (depth : Nat) :
    CommonNominalFullDemand.ProducerLe rowLe
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node first))
      (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node last)) := by
  cases depth with
  | zero => exact CommonNominalFullDemand.producerLe_refl _
  | succ depth => exact below depth

theorem common_arrow_iff (arg arg' result result' : Ty)
    (argRow argRow' resultRow resultRow' : Row) :
    model.subTy (arrow arg argRow result resultRow) (arrow arg' argRow' result' resultRow') ↔
      model.subTy arg' arg ∧ rowLe argRow' argRow ∧
      model.subTy result result' ∧ rowLe resultRow resultRow' := by
  constructor
  · intro below
    have split := fun depth => (CommonNominalFullDemand.producerLe_arrow_iff
      rowLe_refl rowLe_trans _ _ _ _ _ _ _ _).mp (below depth)
    exact ⟨fun depth => (split (depth + 1)).1, (split 0).2.1,
      fun depth => (split (depth + 1)).2.2.1, (split 0).2.2.2⟩
  · rintro ⟨argument, incoming, output, outgoing⟩ depth
    exact (CommonNominalFullDemand.producerLe_arrow_iff rowLe_refl rowLe_trans _ _ _ _ _ _ _ _).mpr
      ⟨quote_observe_le argument depth, incoming, quote_observe_le output depth, outgoing⟩

theorem common_pair_iff (first last first' last' : Ty) :
    model.subTy (pair first last) (pair first' last') ↔
      model.subTy first first' ∧ model.subTy last last' := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonNominalFullDemand.producerLe_pair_iff _ _ _ _).mp (below (depth + 1)) |>.1,
      fun depth => (CommonNominalFullDemand.producerLe_pair_iff _ _ _ _).mp (below (depth + 1)) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact (CommonNominalFullDemand.producerLe_pair_iff _ _ _ _).mpr
      ⟨quote_observe_le first depth, quote_observe_le last depth⟩

theorem common_variant_iff (label : Nat) (first last : Ty) :
    model.subTy (variant label first) (variant label last) ↔ model.subTy first last := by
  constructor
  · intro below depth
    exact (CommonNominalFullDemand.producerLe_variant_iff label _ _).mp (below (depth + 1))
  · intro below depth
    exact (CommonNominalFullDemand.producerLe_variant_iff label _ _).mpr (quote_observe_le below depth)

theorem required_as_width_tail (label : Nat) (payload : Ty) :
    record label payload emptyRecord = required label payload := rfl

theorem common_mask_composition (type : Ty) (first last : List Nat) :
    Equivalent (mask last (mask first type)) (mask (first ++ last) type) :=
  ⟨fun depth => (CommonNominalFullDemand.mask_composition (observeTy depth type) first last).1,
    fun depth => (CommonNominalFullDemand.mask_composition (observeTy depth type) first last).2⟩

theorem common_mask_nil (type : Ty) : Equivalent (mask [] type) type :=
  ⟨fun depth => (CommonNominalFullDemand.mask_nil (observeTy depth type)).1,
    fun depth => (CommonNominalFullDemand.mask_nil (observeTy depth type)).2⟩

theorem common_mask_congr (first last : List Nat)
    (same : ∀ label, label ∈ first ↔ label ∈ last) (type : Ty) :
    Equivalent (mask first type) (mask last type) :=
  ⟨fun depth => (CommonNominalFullDemand.mask_congr first last same (observeTy depth type)).1,
    fun depth => (CommonNominalFullDemand.mask_congr first last same (observeTy depth type)).2⟩

theorem common_mask_idempotent (type : Ty) (hidden : List Nat) :
    Equivalent (mask hidden (mask hidden type)) (mask hidden type) :=
  ⟨fun depth => (CommonNominalFullDemand.mask_idempotent (observeTy depth type) hidden).1,
    fun depth => (CommonNominalFullDemand.mask_idempotent (observeTy depth type) hidden).2⟩

theorem common_mask_required (label : Nat) (payload : Ty) (hidden : List Nat)
    (member : label ∈ hidden) : Equivalent (mask hidden (required label payload)) emptyRecord :=
  ⟨fun _ => (CommonNominalFullDemand.mask_required label _ hidden member).1,
    fun _ => (CommonNominalFullDemand.mask_required label _ hidden member).2⟩

theorem exactEmpty_below_width : model.subTy exactEmpty emptyRecord :=
  fun _ => CommonNominalFullDemand.exactEmpty_below_width

theorem width_not_below_exactEmpty : ¬ model.subTy emptyRecord exactEmpty :=
  fun below => CommonNominalFullDemand.width_not_below_exactEmpty (below 0)

theorem exactEmpty_not_equivalent_width : ¬ Equivalent exactEmpty emptyRecord :=
  fun same => width_not_below_exactEmpty same.2

theorem common_record_mono (label : Nat) {first last rest tail : Ty}
    (payload : Subtype first last) (remaining : Subtype rest tail) :
    Subtype (record label first rest) (record label last tail) :=
  fun depth => CommonNominalFullDemand.producerLe_record_mono label (quote_observe_le payload depth) (remaining depth)

theorem common_union_mono {first last first' last' : Ty}
    (left : Subtype first first') (right : Subtype last last') :
    Subtype (.union first last) (.union first' last') :=
  fun depth => CommonNominalFullDemand.producerLe_union_mono (left depth) (right depth)

theorem common_inter_mono {first last first' last' : Ty}
    (left : Subtype first first') (right : Subtype last last') :
    Subtype (.inter first last) (.inter first' last') :=
  fun depth => CommonNominalFullDemand.producerLe_inter_mono (left depth) (right depth)

theorem common_union_is_join (first last target : Ty) :
    Subtype (.union first last) target ↔ Subtype first target ∧ Subtype last target := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonNominalFullDemand.producerLe_union_iff _ _ _).mp (below depth) |>.1,
      fun depth => (CommonNominalFullDemand.producerLe_union_iff _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨left, right⟩ depth
    exact (CommonNominalFullDemand.producerLe_union_iff _ _ _).mpr ⟨left depth, right depth⟩

theorem common_inter_is_meet (first last source : Ty) :
    Subtype source (.inter first last) ↔ Subtype source first ∧ Subtype source last := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonNominalFullDemand.producerLe_inter_iff _ _ _).mp (below depth) |>.1,
      fun depth => (CommonNominalFullDemand.producerLe_inter_iff _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨left, right⟩ depth
    exact (CommonNominalFullDemand.producerLe_inter_iff _ _ _).mpr ⟨left depth, right depth⟩

end Yulang.CommonNominalFullCarrier
