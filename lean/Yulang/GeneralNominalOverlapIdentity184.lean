import Yulang.GeneralNominalOverlapProvenance184
import Yulang.GeneralNominalBinderIdentity181

/-! Exact metadata of a historical purpose-eight producer. The invocation
identity conclusion does not assert equality of whole occurrences. -/
namespace Yulang.GeneralNominalOverlapIdentity184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalSupportProvenance182
open GeneralNominalRegisteredReadback182
open GeneralNominalCenteredGroundBoundary (groundBoundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem registered_binder_identity
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (equal : plan.binder name =
      fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    name = owner ∧ position = 0 ∧
    plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
    name ∉ plan.packet.declaration.outputNames ∧
    ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
  have separate := GeneralNominalGroundRawSupport183.capture_separate reachable plan.packet
    (GeneralNominalOverlapProvenance184.ground_registered_packet reachable plan registered)
    (invocation := invocation) (declaration := declaration) (purpose := 8)
    (owner := owner) (position := position) (by omega) name
  have notOutput : name ∉ plan.packet.declaration.outputNames := by
    intro output
    have value : plan.binder name = (GeneralNominalPacketSupport.capture plan.packet).outputs name := by
      simp only [Plan.binder,output,ite_true]
    exact separate.1 (equal.symm.trans value)
  have nonpoint : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
    intro point
    have value : plan.binder name = ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 := by
      simp only [Plan.binder,notOutput,ite_false,point,ite_true]
    exact separate.2.1 (equal.symm.trans value)
  rw [GeneralNominalBinderIdentity181.binder_fresh plan name notOutput nonpoint,
    (GeneralNominalHeadTransport184.ground_registered_configuration reachable plan registered).1] at equal
  have identities := (GeneralNominalCenteredAllocation.fresh_identity
    state.erased.current.context.state.seed
    (plan.packet.site.occurrence.identity,plan.packet.declaration.id,8,name,0)
    (invocation,declaration,8,owner,position)).mp equal
  simp only [Prod.mk.injEq,true_and] at identities
  exact ⟨identities.2.2.1,identities.2.2.2.symm,identities.1,identities.2.1,notOutput,nonpoint⟩


theorem ground_overlap_producer
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (member : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state) :
    position = 0 ∧ ∃ plan ∈ state.plans, ∃ schema, SchemaLocation plan schema ∧
      ∃ entry ∈ schema.variables, entry.mode = .actual ∧ entry.name = owner ∧
      plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
      owner ∉ plan.packet.declaration.outputNames ∧
      ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).1 ≠
        ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).2 ∧
      plan.binder owner = fresh state.erased.current.context.state.seed invocation declaration 8 owner position := by
  obtain ⟨origin,plan,registered,schema,location,entry,present,actual,equal,_⟩ :=
    GeneralNominalOverlapProvenance184.ground_overlap_actual reachable member
  obtain ⟨name,position,identity,declaration,output,nonpoint⟩ :=
    registered_binder_identity reachable plan registered entry.name equal
  exact ⟨position,plan,registered,schema,location,entry,present,actual,name,identity,declaration,
    name ▸ output,name ▸ nonpoint,name ▸ equal⟩

theorem uniform_ground_overlap_producer
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (member : fresh state.erased.current.context.state.seed invocation declaration 8 owner position ∈
      GeneralNominalModeLedger181.fullSources state) :
    position = 0 ∧ ∃ plan ∈ state.plans, ∃ schema, SchemaLocation plan schema ∧
      ∃ entry ∈ schema.variables, entry.mode = .actual ∧ entry.name = owner ∧
      plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
      owner ∉ plan.packet.declaration.outputNames ∧
      ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).1 ≠
        ((GeneralNominalPacketSupport.capture plan.packet).inputs owner).2 ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model entry.origin
        (.source (fresh state.erased.current.context.state.seed invocation declaration 8 owner position)) := by
  obtain ⟨zero,plan,registered,schema,location,entry,present,actual,name,identity,decl,output,nonpoint,equal⟩ :=
    ground_overlap_producer reachable member
  refine ⟨zero,plan,registered,schema,location,entry,present,actual,name,identity,decl,output,nonpoint,?_⟩
  intro model valid
  apply actual_same valid
  exact ⟨plan,registered,schema,location,entry,present,actual,name.symm ▸ equal,rfl⟩

end Yulang.GeneralNominalOverlapIdentity184
