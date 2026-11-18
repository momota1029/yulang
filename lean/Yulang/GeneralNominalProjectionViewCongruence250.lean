import Yulang.GeneralNominalOriginViewCongruence250
import Yulang.GeneralNominalRebaseProjectionView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalProjectionViewCongruence250
open GeneralNominalAssignmentCongruence238 (Same subtype_iff)
open GeneralNominalOriginViewCongruence250 (observes inhabited_iff test_iff)
open GeneralNominalRawCongruence238 (equiv_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseProjectionView243
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem fits_iff (same : Same first last) (equal : Equivalent x y) (bounds : Bounds) :
 bounds.Fits first x ↔ bounds.Fits last y :=
 and_congr (subtype_iff (GeneralNominalAssignmentCongruence238.type_eval same bounds.lower) equal)
   (subtype_iff equal (GeneralNominalAssignmentCongruence238.type_eval same bounds.upper))

theorem projection (same : Same first last) {report : Report} (valid : report.Models first) :
 report.Models last := by
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   refine ⟨(inhabited_iff same _).mp (valid.1 anchor member).1,?_⟩
   intro value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (fits_iff same ⟨equal.2,equal.1⟩ _).mp ((valid.1 anchor member).2 old observed)
 · intro test member value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (test_iff equal test.2).mpr (valid.2.1 test member old observed)
 · intro a one b two named origin found value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (fits_iff same ⟨equal.2,equal.1⟩ _).mp (valid.2.2.1 a one b two named origin found old observed)
 · intro a one b two named x y atx aty left right seenLeft seenRight
   obtain ⟨oldLeft,oldOne,equalLeft⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seenLeft
   obtain ⟨oldRight,oldTwo,equalRight⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seenRight
   exact equiv_trans equalLeft (equiv_trans (valid.2.2.2 a one b two named x y atx aty oldLeft oldRight oldOne oldTwo)
     ⟨equalRight.2,equalRight.1⟩)

theorem projection_iff (same : Same first last) (report : Report) :
 report.Models first ↔ report.Models last :=
 ⟨projection same,projection (GeneralNominalAssignmentCongruence238.symm same)⟩
end Yulang.GeneralNominalProjectionViewCongruence250
