import Yulang.GeneralRebaseCompoundOwnerCapture273

set_option maxRecDepth 4096
set_option maxHeartbeats 450000
namespace Yulang.GeneralRebaseCompoundOwnerExpressions273
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

def physical (p : Plan roles) : Slot → Nat
 | .captureLo => low p
 | .captureHi => high p
 | .childLo => lower
 | .childHi => upper
 | .childCenter => center

theorem upper_operand (m : Assignment) (p : Plan roles)
 (decl : p.packet.declaration = declaration) :
 variables p m .upper 0 = (m (high p)).1 := by
 unfold variables
 rw [decl]
 rfl

theorem actual_operand (m : Assignment) (p : Plan roles)
 (decl : p.packet.declaration = declaration) :
 variables p m .actual 0 = (m (binder p 0)).1 := by
 unfold variables
 rw [decl]
 rfl

theorem raw_upper_equation (m : Assignment) (p : Plan roles)
 (decl : p.packet.declaration = declaration) (valid : Outputs p m) :
 Equivalent (m ((GeneralNominalVersionedFrame231.childSite p child signature).occurrence.demand.arguments 0).2).1
   (variant 0 (variables p m .upper 0)) := by
 have member : child ∈ p.packet.declaration.requirements := by rw [decl]; exact List.mem_singleton_self _
 have request := (GeneralNominalVersionedChildIntervals237.endpoint_requests p child member signature 0).2
 have compiled : GeneralNominalCenteredHeadMatExpressions.translate p.packet.registry.constructors
   p.packet.context.interpretation (.variant 0 (.var 0)) = some (.variant 0 (.variable 0)) := rfl
 exact GeneralNominalCenteredHeadMatSchemas.generated_equation valid request compiled

theorem raw_center_equation (m : Assignment) (p : Plan roles)
 (decl : p.packet.declaration = declaration) (held : Holds p m) :
 Equivalent (m ((GeneralNominalVersionedFrame231.childSite p child signature).center 0)).1
   (variant 0 (variables p m .actual 0)) := by
 have member : child ∈ p.packet.declaration.requirements := by rw [decl]; exact List.mem_singleton_self _
 have valid := (held.2.1.2.2.2.2.2.2 child member signature).2
 have request : (⟨.variant 0 (.var 0),(GeneralNominalVersionedFrame231.childSite p child signature).center 0,.actual⟩ : GeneralNominalMaterialization.Request) ∈
   GeneralNominalVersionedPlans231.childRequests p child signature := List.mem_ofFn.mpr ⟨0,rfl⟩
 have compiled : GeneralNominalCenteredHeadMatExpressions.translate p.packet.registry.constructors
   p.packet.context.interpretation (.variant 0 (.var 0)) = some (.variant 0 (.variable 0)) := rfl
 exact GeneralNominalCenteredHeadMatSchemas.generated_equation valid request compiled

end Yulang.GeneralRebaseCompoundOwnerExpressions273
