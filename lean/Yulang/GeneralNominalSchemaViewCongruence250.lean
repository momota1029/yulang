import Yulang.GeneralNominalProjectionViewCongruence250
import Yulang.GeneralNominalRebaseSchemaView243
namespace Yulang.GeneralNominalSchemaViewCongruence250
open GeneralNominalAssignmentCongruence238 (Same subtype_iff type_eval)
open GeneralNominalOriginViewCongruence250 (observes inhabited_iff shared_iff head_iff)
open GeneralNominalRawCongruence238 (equiv_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseSchemaView243
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem argument_iff (same : Same first last) (a : GeneralNominalRebaseLiveView243.Argument) :
 a.Holds first ↔ a.Holds last :=
 and_congr (subtype_iff (type_eval same a.lower) (type_eval same a.center))
   (subtype_iff (type_eval same a.center) (type_eval same a.upper))

theorem site_iff (same : Same first last) (site : GeneralNominalRebaseLiveView243.Site) :
 site.Holds first ↔ site.Holds last :=
 forall_congr' fun a => forall_congr' fun _ => argument_iff same a

theorem requirement_iff (same : Same first last) (equal : Equivalent x y) (r : Requirement) :
 r.Holds first x ↔ r.Holds last y := by
 cases r with
 | equal term => exact equiv_iff equal (type_eval same term)
 | interval lower upper =>
   exact and_congr (subtype_iff (type_eval same lower) equal) (subtype_iff equal (type_eval same upper))

theorem use_forward (same : Same first last) (use : Use) (valid : use.Holds first) : use.Holds last := by
 cases use with
 | same origin target => exact (shared_iff same origin target).mp valid
 | observed origin requirement =>
   refine ⟨(inhabited_iff same _).mp valid.1,?_⟩
   intro value seen
   obtain ⟨old,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
   exact (requirement_iff same ⟨equal.2,equal.1⟩ requirement).mp (valid.2 old observed)

theorem use_iff (same : Same first last) (use : Use) : use.Holds first ↔ use.Holds last :=
 ⟨use_forward same use,use_forward (GeneralNominalAssignmentCongruence238.symm same) use⟩

theorem schema_iff (same : Same first last) (schema : Schema) : schema.Holds first ↔ schema.Holds last :=
 and_congr (forall_congr' fun test => forall_congr' fun _ => head_iff same test.1 test.2)
   (forall_congr' fun use => forall_congr' fun _ => use_iff same use)
end Yulang.GeneralNominalSchemaViewCongruence250
