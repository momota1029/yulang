import Yulang.GeneralRebaseCompoundOwnerExpressions273

set_option maxRecDepth 4096
set_option maxHeartbeats 450000
namespace Yulang.GeneralRebaseCompoundOwnerChildren273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedPlans231 (Holds Outputs emittedSchema variables childSchema childSchema_eq)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan)
open GeneralDictionaryCompoundSource238 (child declaration)
open GeneralDictionaryCompoundSites238 (signature)
open GeneralRebaseCompoundOwnerBlock273 (Slot Block eval loose point)
open GeneralRebaseCompoundOwnerCapture273 (low high read_pair old_pair current_pair historical_center current_center)
open GeneralRebaseCompoundReplacement273 (lower upper center emitted_same)
open GeneralRebaseCompoundChildBoundary273 (variant_equivalent)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralNominalMaterialization (Mode)

open GeneralRebaseCompoundOwnerExpressions273 (physical upper_operand actual_operand raw_upper_equation raw_center_equation)

theorem child_lo_sound (m : Assignment) (p : Plan roles) (b : Block)
 (decl : p.packet.declaration = declaration)
 (schema : emittedSchema p = emittedSchema oldPlan)
 (held : Outputs p m) (lo : Equivalent (m (low p)).1 (m b.lo.val).1) :
 Equivalent (m lower).1 (eval m b .childLo) := by
 have raw := GeneralRebaseCompoundChildBoundary273.raw_lower_equation m p schema held
 rw [GeneralRebaseCompoundChildBoundary273.operand m p decl] at raw
 exact equivalent_trans raw (variant_equivalent _ _ lo)

theorem child_hi_sound (m : Assignment) (p : Plan roles) (b : Block)
 (decl : p.packet.declaration = declaration)
 (childSpec : GeneralNominalVersionedFrame231.childSite p child signature = GeneralDictionaryCompoundSites238.childSite)
 (held : Outputs p m) (hi : Equivalent (m (high p)).1 (m b.hi.val).1) :
 Equivalent (m upper).1 (eval m b .childHi) := by
 have raw := raw_upper_equation m p decl held
 have address := congrArg (fun x : GeneralNominalCenters.Site roles => (x.occurrence.demand.arguments 0).2) childSpec
 rw [upper_operand m p decl,address] at raw
 exact equivalent_trans raw (variant_equivalent _ _ hi)

theorem child_center_sound (m : Assignment) (p : Plan roles) (b : Block)
 (decl : p.packet.declaration = declaration)
 (childSpec : GeneralNominalVersionedFrame231.childSite p child signature = GeneralDictionaryCompoundSites238.childSite)
 (held : Holds p m) (actual : Equivalent (m (binder p 0)).1 (m b.center.val).1) :
 Equivalent (m center).1 (eval m b .childCenter) := by
 have raw := raw_center_equation m p decl held
 have address := congrArg (fun x : GeneralNominalCenters.Site roles => x.center 0) childSpec
 rw [actual_operand m p decl,address] at raw
 exact equivalent_trans raw (variant_equivalent _ _ actual)

end Yulang.GeneralRebaseCompoundOwnerChildren273
