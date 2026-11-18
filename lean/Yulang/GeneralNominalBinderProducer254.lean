import Yulang.GeneralNominalOutputReadback254
import Yulang.GeneralNominalVersionedChildLabels237
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalBinderProducer254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedFrame231 (clauseChild)
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralPatternAdditiveDepth253 (depth)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : GeneralNominalCommonBridge.Assignment}

/-- The designated producer's actual requested target is exactly the parent's
output binder. No separate equality or finite-output premise is used. -/
theorem binder_child (name : Nat) (output : name ∈ plan.packet.declaration.outputNames) :
 ∃ clause ∈ plan.packet.declaration.requirements,
 ∃ signature : clause.Signature roles,
 ∃ request ∈ (clauseChild plan.packet clause signature).demand.outputs,
 request.target = plan.binder name := by
 obtain ⟨binder,present,same⟩ := List.mem_map.mp output
 obtain ⟨clause,child,_,equation,equationMember,_,producer⟩ := plan.packet.checked.produced binder present
 let signature := plan.packet.checked.signature.2.2.2 clause child
 let target := GeneralDeclarationDemands.outputTarget plan.packet.declaration
   (GeneralNominalVersionedFrame231.capture plan.packet)
   ((GeneralNominalVersionedFrame231.frame plan.packet).allocation plan.packet.declaration.id clause).outputs equation
 refine ⟨clause,child,signature,⟨equation.name,target⟩,List.mem_map.mpr ⟨equation,equationMember,rfl⟩,?_⟩
 have rhs : equation.rhs = .var name := by simpa only [same] using producer
 simp only [target,GeneralDeclarationDemands.outputTarget,rhs,normalize,output,ite_true,
   GeneralNominalVersionedFrame231.capture_outputs,Plan.binder]

/-- Finite child-output readbacks transfer to parent binders along the actual
request target. The premise is about real emitted child outputs, not an
unrelated Associated interpretation. -/
theorem binder_readback (bound : Nat)
 (children : ∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
   ∀ request ∈ (clauseChild plan.packet clause signature).demand.outputs,
   ∃ result : Pattern, result.variables = [] ∧
   Equivalent (model request.target).1
     (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
   depth result ≤ bound)
 (name : Nat) (output : name ∈ plan.packet.declaration.outputNames) :
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model (plan.binder name)).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ bound := by
 obtain ⟨clause,member,signature,request,present,same⟩ := binder_child name output
 simpa only [same] using children clause member signature request present

end Yulang.GeneralNominalBinderProducer254
