import Yulang.GeneralRebaseCompoundOwnerChildren273

set_option maxRecDepth 4096
set_option maxHeartbeats 450000
namespace Yulang.GeneralRebaseCompoundOwnerMeaning273
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

open GeneralRebaseCompoundOwnerChildren273 (child_lo_sound child_hi_sound child_center_sound)

structure Sound (m : Assignment) (p : Plan roles) (b : Block) : Prop where
 captureLo : Equivalent (m (low p)).1 (m b.lo.val).1
 captureHi : Equivalent (m (high p)).1 (m b.hi.val).1
 childLo : Equivalent (m lower).1 (eval m b .childLo)
 childHi : Equivalent (m upper).1 (eval m b .childHi)
 childCenter : Equivalent (m center).1 (eval m b .childCenter)

theorem historical (m : Assignment) (held : Holds oldPlan m) : Sound m oldPlan loose := by
 have pair := read_pair m _ _ 4 2 (old_pair m held)
 exact ⟨pair.1,pair.2,
   child_lo_sound m oldPlan loose rfl rfl held.2.2 pair.1,
   child_hi_sound m oldPlan loose rfl rfl held.2.2 pair.2,
   child_center_sound m oldPlan loose rfl rfl held (historical_center m held)⟩

theorem replacement (m : Assignment) (held : Holds currentPlan m) : Sound m currentPlan point := by
 have pair := read_pair m _ _ 2 2 (current_pair m held)
 have childSpec := GeneralDictionaryCompoundReplay238.child_site signature
 exact ⟨pair.1,pair.2,
   child_lo_sound m currentPlan point rfl emitted_same held.2.2 pair.1,
   child_hi_sound m currentPlan point rfl childSpec held.2.2 pair.2,
   child_center_sound m currentPlan point rfl childSpec held (current_center m held)⟩

end Yulang.GeneralRebaseCompoundOwnerMeaning273
