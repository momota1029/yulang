import Yulang.GeneralPresenceModelCongruence245
import Yulang.CommonNominalFullConstructors

/-! Constructor-congruence laws for the concrete full nominal Common carrier.
This supplies semantic model laws only. Actual source-operation fresh-block,
rank, scheduling and boundary producers remain separate obligations. -/
namespace Yulang.GeneralPresenceCommonLaws245
open GeneralPresenceModelCongruence245
open CommonNominalFullCarrier

 theorem recordDefault_equiv (label : Nat) (source source' fallback fallback' : Ty)
    (base : Equiv model source source') (default : Equiv model fallback fallback') :
    Equiv model (model.recordDefault label source fallback)
      (model.recordDefault label source' fallback') := by
  have atDepth (depth : Nat) : CommonNominalFullDemand.ProducerEq Common.rowLe
      (observeTy depth (recordDefault label source fallback))
      (observeTy depth (recordDefault label source' fallback')) := by
    cases depth with
    | zero =>
      exact ⟨CommonNominalFullDemand.producerLe_record_mono label
        (CommonNominalFullDemand.producerLe_refl _) (base.1 0),
        CommonNominalFullDemand.producerLe_record_mono label
        (CommonNominalFullDemand.producerLe_refl _) (base.2 0)⟩
    | succ depth =>
      exact CommonNominalFullDemand.producerEq_recordDefault label
        ⟨base.1 (depth+1),base.2 (depth+1)⟩
        ⟨quote_observe_le default.1 (depth+1),quote_observe_le default.2 (depth+1)⟩
  exact ⟨fun depth => (atDepth depth).1,fun depth => (atDepth depth).2⟩

theorem common_laws : Laws model where
  refl := subtype_refl
  trans := fun _ _ _ before after => subtype_trans before after
  union_congr := fun _ _ _ _ left right =>
    ⟨common_union_mono left.1 right.1,common_union_mono left.2 right.2⟩
  inter_congr := fun _ _ _ _ left right =>
    ⟨common_inter_mono left.1 right.1,common_inter_mono left.2 right.2⟩
  pair_congr := fun _ _ _ _ left right =>
    ⟨(common_pair_iff ..).mpr ⟨left.1,right.1⟩,
     (common_pair_iff ..).mpr ⟨left.2,right.2⟩⟩
  record_congr := fun label _ _ _ _ left right =>
    ⟨common_record_mono label left.1 right.1,common_record_mono label left.2 right.2⟩
  recordDefault_congr := recordDefault_equiv
  required_congr := fun label _ _ equal =>
    ⟨common_record_mono label equal.1 (subtype_refl _),
     common_record_mono label equal.2 (subtype_refl _)⟩
  variant_congr := fun label _ _ equal =>
    ⟨(common_variant_iff label ..).mpr equal.1,(common_variant_iff label ..).mpr equal.2⟩
  arrow_congr := fun _ _ _ _ incoming outgoing left right =>
    ⟨(common_arrow_iff ..).mpr
      ⟨left.2,Common.rowLe_refl incoming,right.1,Common.rowLe_refl outgoing⟩,
     (common_arrow_iff ..).mpr
      ⟨left.1,Common.rowLe_refl incoming,right.2,Common.rowLe_refl outgoing⟩⟩

end Yulang.GeneralPresenceCommonLaws245
