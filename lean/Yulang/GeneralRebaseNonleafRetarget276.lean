import Yulang.GeneralRebaseRetargetEffects275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 6500000
namespace Yulang.GeneralRebaseNonleafRetarget276
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCandidates (Context)
open GeneralNominalRefinements (Refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedFrame231
open GeneralNominalVersionedPlans231
open GeneralRebaseRetarget275 (Observed retarget)

variable {roles : Roles.RoleDecls} {after : Context}
variable (p : Plan roles) (ref : Refines p.packet.context.state after.state)
variable (interp : after.interpretation = p.packet.context.interpretation) (seen : Observed p)

include interp seen in
theorem frame_eq : frame (retarget p ref).packet = frame p.packet := by
 unfold frame
 rw [GeneralRebaseRetarget275.packet_bindings p ref interp seen]
 simp only [GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.source,ref.seed]
 congr
 funext key clause
 simp only [GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,ref.seed]

include interp seen in
theorem children_eq : children (retarget p ref).packet = children p.packet := by
 unfold children
 rw [frame_eq p ref interp seen]

include interp seen in
theorem clause_eq (clause : Clause) (valid : clause.Signature roles) :
 clauseChild (retarget p ref).packet clause valid = clauseChild p.packet clause valid := by
 unfold clauseChild
 rw [frame_eq p ref interp seen,GeneralRebaseRetarget275.capture p ref interp seen]

include interp seen in
theorem center_eq (clause pos : Nat) (pattern) :
 emittedCenter (retarget p ref) clause pos pattern = emittedCenter p clause pos pattern := by
 unfold emittedCenter
 cases GeneralDeclarationPatterns.normalize pattern
 all_goals first | exact GeneralRebaseRetarget275.binder p ref interp seen _ | exact congrArg (fun s => fresh s p.packet.site.occurrence.identity p.packet.declaration.id 9 clause pos) ref.seed

include interp seen in
theorem child_site_eq (clause : Clause) (valid : clause.Signature roles) :
 childSite (retarget p ref) clause valid = childSite p clause valid := by
 unfold childSite
 simp only [center_eq p ref interp seen]
 congr 1
 exact clause_eq p ref interp seen clause valid

include interp seen in
theorem requests_eq : emittedRequests (retarget p ref).packet = emittedRequests p.packet := by
 unfold emittedRequests
 rw [GeneralRebaseRetarget275.capture p ref interp seen,frame_eq p ref interp seen]

include interp seen in
theorem emitted_schema_eq : emittedSchema (retarget p ref) = emittedSchema p := by
 unfold emittedSchema
 rw [requests_eq p ref interp seen]
 simp only [interp]

include interp seen in
theorem child_requests_eq (clause : Clause) (valid : clause.Signature roles) :
 childRequests (retarget p ref) clause valid = childRequests p clause valid := by
 unfold childRequests childSite
 simp only [center_eq p ref interp seen]

include interp seen in
theorem child_schema_eq (clause : Clause) (valid : clause.Signature roles) :
 childSchema (retarget p ref) clause valid = childSchema p clause valid := by
 unfold childSchema
 rw [child_requests_eq p ref interp seen]
 simp only [interp]

include interp seen in
theorem inputs_iff (m : Assignment) : Inputs (retarget p ref) m ↔ Inputs p m := by
 unfold Inputs
 have needed (n : Nat) : GeneralNominalSharedCaptures.Needed (retarget p ref).packet n ↔ GeneralNominalSharedCaptures.Needed p.packet n := Iff.rfl
 simp only [needed,GeneralRebaseRetarget275.ordinary p ref interp seen,GeneralRebaseRetarget275.projection p ref interp seen,
   GeneralRebaseRetarget275.capture p ref interp seen,GeneralRebaseRetarget275.binder p ref interp seen,
   GeneralRebaseRetarget275.head_schema p ref interp,GeneralRebaseRetarget275.schema_holds p ref interp seen,
   emitted_schema_eq p ref interp seen,GeneralRebaseRetarget275.variables_eq p ref interp seen,
   child_site_eq p ref interp seen,child_schema_eq p ref interp seen]

include interp seen in
theorem outputs_iff (m : Assignment) : Outputs (retarget p ref) m ↔ Outputs p m := by
 unfold Outputs
 rw [emitted_schema_eq p ref interp seen,GeneralRebaseRetarget275.variables_eq p ref interp seen]

include interp seen in
theorem holds_iff (m : Assignment) :
 Holds (retarget p ref) m ↔ GeneralNominalState.Models after.state m ∧ Inputs p m ∧ Outputs p m := by
 unfold Holds
 rw [inputs_iff p ref interp seen,outputs_iff p ref interp seen]

end Yulang.GeneralRebaseNonleafRetarget276
