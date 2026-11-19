import Yulang.GeneralRebaseRefreshClosure275
import Yulang.GeneralNominalSlotFacts198
import Yulang.GeneralDictionaryRefinedLocations

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralRebaseRetarget275
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState (Packet)
open GeneralNominalCandidates (Context)
open GeneralNominalRefinements (Refines)
open GeneralNominalSlotObservation198 (bounds)
open GeneralNominalSlotFacts198 (candidate_report bindings_report selfChecks_report projection_report finished_report)
open GeneralNominalRefinementTrace197 (ObservedMany)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231

variable {roles : Roles.RoleDecls} {after : Context}

def Observed (plan : Plan roles) : Prop :=
 ObservedMany plan.packet.context.state
  (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
  plan.packet.bounds

abbrev retarget (plan : Plan roles) (ref : Refines plan.packet.context.state after.state) : Plan roles :=
 ⟨⟨plan.packet.registry,after,plan.packet.site,plan.packet.declaration,plan.packet.checked,
   plan.packet.bounds.map (bounds ref.base.embed)⟩,plan.input,plan.input_exact⟩

variable (plan : Plan roles) (ref : Refines plan.packet.context.state after.state)
variable (interpretation : after.interpretation = plan.packet.context.interpretation)

include interpretation in
theorem observed (seen : Observed plan) : Observed (retarget plan ref) := by
 unfold Observed at seen ⊢
 change ObservedMany after.state
   (GeneralNominalInspection.queries after.state after.interpretation plan.packet.declaration)
   (plan.packet.bounds.map (bounds ref.base.embed))
 rw [show GeneralNominalInspection.queries after.state after.interpretation plan.packet.declaration =
   GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration by
     simp only [GeneralNominalInspection.queries,interpretation,ref.constructors]]
 exact GeneralNominalSlotObservation198.observedMany ref seen

include interpretation in
theorem report (seen : Observed plan) :
 GeneralNominalPacketSupport.report (retarget plan ref).packet =
   GeneralNominalSlotReport198.report ref.base.embed (GeneralNominalPacketSupport.report plan.packet) :=
 candidate_report ref interpretation seen

include interpretation in
theorem packet_bindings (seen : Observed plan) : (retarget plan ref).packet.bindings = plan.packet.bindings := by
 change GeneralNominalRecursiveInspection.bindings after.state
    (GeneralNominalPacketSupport.report (retarget plan ref).packet) = _
 rw [report plan ref interpretation seen]
 exact bindings_report ref _

include interpretation in
theorem ordinary (seen : Observed plan) (m : Assignment) :
 Ordinary (retarget plan ref).packet m ↔ Ordinary plan.packet m := by
 unfold Ordinary
 rw [packet_bindings plan ref interpretation seen,report plan ref interpretation seen,selfChecks_report ref]
 simp only [GeneralNominalVersionedAllocation231.merges,GeneralNominalVersionedAllocation231.capture,
   GeneralNominalAllocation.source,ref.seed]

include interpretation in
theorem projection (seen : Observed plan) (m : Assignment) :
 GeneralNominalRecursiveInspection.ProjectionModels after.state
    (GeneralNominalPacketSupport.report (retarget plan ref).packet) m ↔
 GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state
    (GeneralNominalPacketSupport.report plan.packet) m := by
 rw [report plan ref interpretation seen]
 exact projection_report ref _ m

include interpretation in
theorem capture (seen : Observed plan) :
 GeneralNominalVersionedFrame231.capture (retarget plan ref).packet =
 GeneralNominalVersionedFrame231.capture plan.packet := by
 change GeneralNominalVersionedAllocation231.capture after.state plan.packet.registry
   plan.packet.site.occurrence.identity plan.packet.declaration.id (retarget plan ref).packet.bindings = _
 rw [packet_bindings plan ref interpretation seen]
 simp only [GeneralNominalVersionedFrame231.capture,GeneralNominalVersionedFrame231.frame,
   GeneralNominalVersionedAllocation231.capture,GeneralNominalAllocation.source,ref.seed]

include interpretation in
theorem binder (seen : Observed plan) (name : Nat) :
 GeneralNominalVersionedFrame231.binder (retarget plan ref) name =
 GeneralNominalVersionedFrame231.binder plan name := by
 unfold GeneralNominalVersionedFrame231.binder
 rw [capture plan ref interpretation seen]
 simp only [ref.seed]

include interpretation in
theorem variables_eq (seen : Observed plan) (m : Assignment) :
 variables (retarget plan ref) m = variables plan m := by
 funext mode name
 unfold variables
 rw [binder plan ref interpretation seen,capture plan ref interpretation seen]

include interpretation in
theorem head_schema :
 (retarget plan ref).headSchema = plan.headSchema := by
 unfold Plan.headSchema
 simp only [retarget,GeneralNominalInspection.queries,interpretation,ref.constructors]

theorem no_emission (invocation : Nat) (declaration : Declaration)
 (checked : DeclarationChecked constructors roles declaration) (capture : GeneralDeclarationDemands.Capture)
 (allocation : (clause : Clause) → GeneralDeclarationDemands.Allocation roles clause)
 (empty : declaration.requirements = []) :
 GeneralCanonicalChildOrder.canonicalEmit invocation declaration checked capture allocation = [] := by
 have no : (GeneralCanonicalChildOrder.canonicalDeclaration declaration).requirements = [] := by
   simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,empty]
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro item member
 unfold GeneralCanonicalChildOrder.canonicalEmit GeneralDeclarationDemands.emitAll at member
 obtain ⟨clause,_,_⟩ := List.mem_map.mp member
 exact List.not_mem_nil (Eq.mp (congrArg (fun req => clause.val ∈ req) no) clause.property)

theorem emissions_leaf (empty : plan.packet.declaration.requirements = []) :
 GeneralNominalVersionedPlans231.emittedRequests (retarget plan ref).packet =
 GeneralNominalVersionedPlans231.emittedRequests plan.packet := by
 unfold GeneralNominalVersionedPlans231.emittedRequests
 rw [no_emission _ _ _ _ _ empty,no_emission _ _ _ _ _ empty]

theorem children_leaf (empty : plan.packet.declaration.requirements = []) :
 GeneralNominalVersionedFrame231.children (retarget plan ref).packet = [] := by
 simp [GeneralNominalVersionedFrame231.children,retarget,GeneralDictionaryEmissionPlans.children,
   GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
   GeneralCanonicalChildOrder.canonicalRequirements,GeneralDeclarationDemands.emitAll,empty]

include interpretation in
theorem emitted_schema (empty : plan.packet.declaration.requirements = []) :
 emittedSchema (retarget plan ref) = emittedSchema plan := by
 unfold emittedSchema
 rw [emissions_leaf plan ref empty]
 simp only [interpretation]

include interpretation in
theorem schema_holds (seen : Observed plan) (schema : GeneralNominalMaterialization.Schema) (m : Assignment) :
 SchemaHolds (retarget plan ref) schema m ↔ SchemaHolds plan schema m := by
 unfold SchemaHolds
 rw [capture plan ref interpretation seen]
 simp only [retarget, binder plan ref interpretation seen]

include interpretation in
theorem holds_leaf (seen : Observed plan) (empty : plan.packet.declaration.requirements = [])
 (m : Assignment) (new : GeneralNominalState.Models after.state m) (valid : Holds plan m) :
 Holds (retarget plan ref) m := by
 have same := variables_eq plan ref interpretation seen m
 have cap := capture plan ref interpretation seen
 have bin := binder plan ref interpretation seen
 have schema := emitted_schema plan ref interpretation empty
 refine ⟨new,?_,?_⟩
 · refine ⟨(ordinary plan ref interpretation seen m).mpr valid.2.1.1,
     (projection plan ref interpretation seen m).mpr valid.2.1.2.1,valid.2.1.2.2.1,?_,?_,?_,?_⟩
   · intro name needed
     rw [cap,bin]
     exact valid.2.1.2.2.2.1 name needed
   · rw [head_schema plan ref interpretation]
     exact (schema_holds plan ref interpretation seen _ m).mpr valid.2.1.2.2.2.2.1
   · rw [schema,same]
     exact valid.2.1.2.2.2.2.2.1
   · intro clause member
     exact False.elim (List.not_mem_nil (empty ▸ member))
 · unfold Outputs
   rw [schema,same]
   exact valid.2.2

end Yulang.GeneralRebaseRetarget275
