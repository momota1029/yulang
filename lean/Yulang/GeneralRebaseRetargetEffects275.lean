import Yulang.GeneralRebaseRetarget275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 7900000
namespace Yulang.GeneralRebaseRetargetEffects275
open GeneralNominalCenters GeneralDeclarations
open GeneralNominalCandidates (Context)
open GeneralNominalRefinements (Refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalVersionedEffects231 (BodyHolds bodyVariables ClassEffects)
open GeneralNominalCenteredHeadMatEffects (bodySchema Ready)
open GeneralRebaseRetarget275 (Observed retarget variables_eq)
open GeneralNominalCenteredHeadOutputs (requests)

variable {roles : Roles.RoleDecls} {after : Context}
variable (plan : Plan roles) (ref : Refines plan.packet.context.state after.state)
variable (interp : after.interpretation = plan.packet.context.interpretation)

include interp in
theorem body_schema (target : Nat) (body : Body) :
 bodySchema (retarget plan ref) target body = bodySchema plan target body := by
 unfold bodySchema
 cases body with
 | explicit => simp only [GeneralNominalCenteredHeadMatEffects.compileBody,interp]
 | default => simp only [GeneralNominalCenteredHeadMatEffects.compileBody,interp]

include interp in
theorem body_values (seen : Observed plan) (m : Assignment) (body : Body) :
 bodyVariables (retarget plan ref) m body = bodyVariables plan m body := by
 cases body with
 | explicit => exact variables_eq plan ref interp seen m
 | default => rfl

include interp in
theorem body_holds (seen : Observed plan) (target : Nat) (m : Assignment) (body : Body) :
 BodyHolds (retarget plan ref) target m body ↔ BodyHolds plan target m body := by
 unfold BodyHolds
 rw [body_schema plan ref interp,body_values plan ref interp seen]

include interp in
theorem class_effects (state : GeneralNominalCenteredSteps.State roles)
 (seen : Observed plan) (m : Assignment) (valid : ClassEffects state root plan m) :
 ClassEffects state root (retarget plan ref) m := by
 refine ⟨?_,valid.2⟩
 intro output recorded body found
 exact (body_holds plan ref interp seen output.target m body).mpr (valid.1 output recorded body found)

include interp in
theorem ready (state : GeneralNominalCenteredSteps.State roles) (valid : Ready state root plan) :
 Ready state root (retarget plan ref) := by
 intro output recorded
 obtain ⟨body,found,implemented⟩ := valid output recorded
 refine ⟨body,found,?_⟩
 rw [body_schema plan ref interp]
 exact implemented

end Yulang.GeneralRebaseRetargetEffects275
