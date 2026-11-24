import Yulang.GeneralDeclarativeI65CollectExactReads384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (shapeOf)

/-- Source-aware alias paths *before* collecting the dependencies
of the current local rule. Written bounds still need their own
authority and output reads carry the exact chosen dictionaries. -/
inductive SourcedAlias384 (rules : ExactSelectedRule384) (ordinary : LogicalOutputEquation383)
    (tagged : ChosenTaggedBinding383) (direct : DirectEquation383)
    (intervals constraints : BoundOrigin384) (s : State) : Nat → Nat → Prop where
  | bounds : OpenBound384 intervals constraints s a b → OpenBound384 intervals constraints s b a →
      SourcedAlias384 rules ordinary tagged direct intervals constraints s a b
  | forward : SourcedOrdinaryRead384 rules ordinary tagged direct s ⟨a,.variable b⟩ →
      SourcedAlias384 rules ordinary tagged direct intervals constraints s a b
  | backward : SourcedOrdinaryRead384 rules ordinary tagged direct s ⟨b,.variable a⟩ →
      SourcedAlias384 rules ordinary tagged direct intervals constraints s a b
  | trans : SourcedAlias384 rules ordinary tagged direct intervals constraints s a b →
      SourcedAlias384 rules ordinary tagged direct intervals constraints s b c →
      SourcedAlias384 rules ordinary tagged direct intervals constraints s a c

theorem collect_sourced_alias384 {source ordinary tagged direct intervals constraints s a b}
    (alias : SourcedAlias384 source ordinary tagged direct intervals constraints s a b) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      OpenAlias384 direct intervals constraints s needs a b := by
  induction alias with
  | bounds lo hi => exact ⟨[],⟨.nil⟩,.bounds lo hi⟩
  | forward proof =>
    obtain ⟨cells,provided,step⟩ := collect_sourced_ordinary_read384 proof
    exact ⟨cells,provided,.forward step⟩
  | backward proof =>
    obtain ⟨cells,provided,step⟩ := collect_sourced_ordinary_read384 proof
    exact ⟨cells,provided,.backward step⟩
  | trans _ _ left right =>
    obtain ⟨xs,⟨xsProof⟩,left⟩ := left
    obtain ⟨ys,⟨ysProof⟩,right⟩ := right
    exact ⟨xs ++ ys,⟨append_exact_supports384 xsProof ysProof⟩,
      .trans (reindex_open_alias384 (needs_embed_left384 xs ys) left)
        (reindex_open_alias384 (needs_embed_right384 xs ys) right)⟩

theorem sourced_alias_of_exact_slots384 {source ordinary tagged direct intervals constraints s needs a b}
    (provided : ExactSupportForest384 source ordinary tagged s needs)
    (alias : OpenAlias384 direct intervals constraints s needs a b) :
    SourcedAlias384 source ordinary tagged direct intervals constraints s a b := by
  induction alias with
  | bounds l r => exact .bounds l r
  | forward step => exact .forward (sourced_ordinary_read_of_exact_slots384 provided step)
  | backward step => exact .backward (sourced_ordinary_read_of_exact_slots384 provided step)
  | trans _ _ l r => exact .trans l r

inductive SourcedObserved384 (source : ExactSelectedRule384) (ordinary : LogicalOutputEquation383)
    (tagged : ChosenTaggedBinding383) (direct : DirectEquation383)
    (intervals constraints : BoundOrigin384) (s : State) : Nat → Shape → Prop where
  | shape :
      SourcedAlias384 source ordinary tagged direct intervals constraints s logical row.left →
      SourcedOrdinaryRead384 source ordinary tagged direct s row →
      shapeOf row.right = some shape →
      SourcedObserved384 source ordinary tagged direct intervals constraints s logical shape

theorem collect_sourced_observation384 {source ordinary tagged direct intervals constraints s logical shape}
    (seen : SourcedObserved384 source ordinary tagged direct intervals constraints s logical shape) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      OpenObserved384 direct intervals constraints s needs logical shape := by
  cases seen with
  | shape route sourceRead normalized =>
    obtain ⟨xs,⟨useX⟩,alias⟩ := collect_sourced_alias384 route
    obtain ⟨ys,⟨useY⟩,eq⟩ := collect_sourced_ordinary_read384 sourceRead
    exact ⟨xs ++ ys,⟨append_exact_supports384 useX useY⟩,
      .shape (reindex_open_alias384 (needs_embed_left384 xs ys) alias)
        (reindex_open_ordinary_read384 (needs_embed_right384 xs ys) eq) normalized⟩

theorem sourced_observation_of_exact_slots384
    {source ordinary tagged direct intervals constraints s needs logical shape}
    (provided : ExactSupportForest384 source ordinary tagged s needs)
    (seen : OpenObserved384 direct intervals constraints s needs logical shape) :
    SourcedObserved384 source ordinary tagged direct intervals constraints s logical shape := by
  cases seen with
  | shape link row normalized =>
    exact .shape (sourced_alias_of_exact_slots384 provided link)
      (sourced_ordinary_read_of_exact_slots384 provided row) normalized

theorem sourced_observation_iff_collected384
    {source ordinary tagged direct intervals constraints s logical shape} :
    SourcedObserved384 source ordinary tagged direct intervals constraints s logical shape ↔
      ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
        OpenObserved384 direct intervals constraints s needs logical shape := by
  constructor
  · exact collect_sourced_observation384
  · rintro ⟨_,⟨supports⟩,seen⟩
    exact sourced_observation_of_exact_slots384 supports seen

end Yulang.GeneralDeclarativeI65
