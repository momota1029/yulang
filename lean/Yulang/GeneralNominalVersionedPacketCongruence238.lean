import Yulang.GeneralNominalSchemaCongruence238
import Yulang.GeneralNominalVersionedPacketFrame236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedPacketCongruence238
open GeneralNominalAssignmentCongruence238 (Same)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSchemaCongruence238
open GeneralNominalVersionedPlans231
open GeneralNominalCenters
variable {first last : Assignment}

theorem holds_iff (same : Same first last) (plan : Plan roles) : Holds plan first ↔ Holds plan last := by
 rw [GeneralNominalVersionedPacketFrame236.holds_shape,GeneralNominalVersionedPacketFrame236.holds_shape]
 apply and_congr (GeneralNominalProjectionCongruence238.head_models_iff same _)
 apply and_congr (site_iff same plan.input)
 apply and_congr
 · exact forall_congr' fun _ => forall_congr' fun _ => fits_iff same (same _).1 _
 apply and_congr (schema_iff same plan plan.headSchema)
 apply and_congr
 · apply forall_congr'; intro equation
   apply forall_congr'; intro member
   apply forall_congr'; intro nonactual
   exact equation_iff same _ _ (variables same plan) equation
 apply and_congr
 · apply forall_congr'; intro clause
   apply forall_congr'; intro member
   apply forall_congr'; intro checked
   exact and_congr (site_iff same _) (versioned_total_schema_iff same plan _)
 · exact versioned_total_schema_iff same plan _
end Yulang.GeneralNominalVersionedPacketCongruence238
