import Yulang.GeneralNominalOriginCongruence238
import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalProjectionCongruence238
open GeneralNominalAssignmentCongruence238 (Same subtype_iff)
open GeneralNominalOriginCongruence238 (observes inhabited_iff test_iff)
open GeneralNominalRawCongruence238 (equiv_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem fits_iff (same : Same first last) (equal : Equivalent x y)
 (state : GeneralNominalState.State) (bounds : GeneralNominalInspection.Bounds state) :
 Fits state first bounds x ↔ Fits state last bounds y :=
 and_congr (subtype_iff (same _).1 equal) (subtype_iff equal (same _).1)

theorem projection (same : Same first last) (valid : ProjectionModels state report first) :
 ProjectionModels state report last := by
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   refine ⟨(inhabited_iff same _).mp (valid.1 anchor member).1,?_⟩
   intro value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (fits_iff same ⟨equal.2,equal.1⟩ _ _).mp ((valid.1 anchor member).2 old observed)
 · intro test member value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (test_iff equal test.2).mpr (valid.2.1 test member old observed)
 · intro a one b two named origin found value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (fits_iff same ⟨equal.2,equal.1⟩ _ _).mp (valid.2.2.1 a one b two named origin found old observed)
 · intro a one b two named x y atx aty left right seenLeft seenRight
   obtain ⟨oldLeft,oldOne,equalLeft⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seenLeft
   obtain ⟨oldRight,oldTwo,equalRight⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seenRight
   exact equiv_trans equalLeft (equiv_trans (valid.2.2.2 a one b two named x y atx aty oldLeft oldRight oldOne oldTwo)
     ⟨equalRight.2,equalRight.1⟩)

theorem projection_iff (same : Same first last) (state : GeneralNominalState.State) (report : Report state) :
 ProjectionModels state report first ↔ ProjectionModels state report last :=
 ⟨projection same,projection (GeneralNominalAssignmentCongruence238.symm same)⟩

theorem head_models_iff (same : Same first last) (packet : GeneralNominalSaturationState.Packet roles) :
 GeneralNominalVersionedPlans231.HeadModels packet first ↔ GeneralNominalVersionedPlans231.HeadModels packet last :=
 and_congr (GeneralNominalRawCongruence238.models_iff _ same) (projection_iff same _ _)
end Yulang.GeneralNominalProjectionCongruence238
