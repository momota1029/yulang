import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.GeneralNominalVersionedRecorded232
import Yulang.GeneralNominalVersionedKernelCache232
namespace Yulang.GeneralNominalVersionedSourceInvariants232
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedSourceBoundary232
variable {roles : Roles.RoleDecls}

theorem recorded (path : B4TargetV8.Reachable (boundary roles) value root state) :
    GeneralNominalVersionedRecorded232.Recorded state :=
  GeneralNominalVersionedRecorded232.reachable (reachable_compiled path)

theorem effect_full_holds (path : B4TargetV8.Reachable (boundary roles) value root state)
    (valid : Models state model) (present : effect ∈ state.effects) :
    GeneralNominalVersionedPlans231.Holds effect.plan model :=
  GeneralNominalVersionedRecorded232.effect_full_holds (recorded path) valid present

theorem cache (path : B4TargetV8.Reachable (boundary roles) value root state) :
    GeneralNominalVersionedKernelCache232.Valid state :=
  GeneralNominalVersionedKernelCache232.reachable_cache (reachable_compiled path)

end Yulang.GeneralNominalVersionedSourceInvariants232
