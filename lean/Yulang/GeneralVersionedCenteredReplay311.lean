import Yulang.GeneralNominalVersionedTransport231
import Yulang.GeneralNominalVersionedChildren232

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionedCenteredReplay311
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedTransport231 (extendedPlan childSite_eq)
open GeneralNominalVersionedChildren232 (emitted)

theorem emitted_extended (plan : Plan roles) (reserved : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (allocated : List GeneralNominalIdentities.Origin) :
    emitted (extendedPlan reserved atoms allocated plan) = emitted plan := by
  unfold emitted
  apply List.map_congr_left
  intro clause _
  exact childSite_eq reserved atoms allocated plan clause.val _

end Yulang.GeneralVersionedCenteredReplay311
