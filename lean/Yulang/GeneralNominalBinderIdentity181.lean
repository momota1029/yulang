import Yulang.GeneralNominalCenteredAllocation

/-! The allocated binder namespace identifies its invocation, declaration and
name. Registered actual uses supply readback when those identities and the
origin agree. This is not a classification of the full old footprint. -/
namespace Yulang.GeneralNominalBinderIdentity181
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

variable {roles : Roles.RoleDecls} {model : GeneralNominalCommonBridge.Assignment}

theorem binder_fresh (plan : Plan roles) (name : Nat)
    (notOutput : name ∉ plan.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2) :
    plan.binder name = fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
      plan.packet.declaration.id 8 name 0 := by
  simp only [Plan.binder,notOutput,ite_false,nonpoint]

theorem binder_collision_iff (first last : Plan roles) (one two : Nat)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (firstNotOutput : one ∉ first.packet.declaration.outputNames)
    (lastNotOutput : two ∉ last.packet.declaration.outputNames)
    (firstNonpoint : ((GeneralNominalPacketSupport.capture first.packet).inputs one).1 ≠
      ((GeneralNominalPacketSupport.capture first.packet).inputs one).2)
    (lastNonpoint : ((GeneralNominalPacketSupport.capture last.packet).inputs two).1 ≠
      ((GeneralNominalPacketSupport.capture last.packet).inputs two).2) :
    first.binder one = last.binder two ↔
      first.packet.site.occurrence.identity = last.packet.site.occurrence.identity ∧
      first.packet.declaration.id = last.packet.declaration.id ∧ one = two := by
  rw [binder_fresh first one firstNotOutput firstNonpoint,
    binder_fresh last two lastNotOutput lastNonpoint,seed]
  rw [GeneralNominalCenteredAllocation.fresh_identity last.packet.context.state.seed
    (first.packet.site.occurrence.identity,first.packet.declaration.id,8,one,0)
    (last.packet.site.occurrence.identity,last.packet.declaration.id,8,two,0)]
  simp only [Prod.mk.injEq,true_and,and_true]

theorem registered_readback
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (old candidate : Plan roles) (registered : old ∈ state.plans)
    (valid : Models state model) (use : GeneralNominalMaterialization.Use)
    (present : use ∈ old.headSchema.variables) (actual : use.mode = .actual)
    (origin : Origin) (sameOrigin : origin = use.origin) (name : Nat)
    (sameCenter : candidate.binder name = old.binder use.name)
    (value : Ty) (seen : Observes model origin value) :
    Equivalent value (model (candidate.binder name)).1 := by
  have readback := GeneralNominalCenteredAllocation.registered_nested_name
    path registered valid use present actual
  rw [sameOrigin] at seen
  rw [sameCenter]
  exact readback.2.2 value (model (old.binder use.name)).1 seen (.source _)

theorem registered_identity_readback
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (old candidate : Plan roles) (registered : old ∈ state.plans)
    (valid : Models state model) (use : GeneralNominalMaterialization.Use)
    (present : use ∈ old.headSchema.variables) (actual : use.mode = .actual)
    (seed : candidate.packet.context.state.seed = old.packet.context.state.seed)
    (invocation : candidate.packet.site.occurrence.identity = old.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration.id = old.packet.declaration.id)
    (candidateNotOutput : use.name ∉ candidate.packet.declaration.outputNames)
    (oldNotOutput : use.name ∉ old.packet.declaration.outputNames)
    (candidateNonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs use.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs use.name).2)
    (oldNonpoint : ((GeneralNominalPacketSupport.capture old.packet).inputs use.name).1 ≠
      ((GeneralNominalPacketSupport.capture old.packet).inputs use.name).2)
    (origin : Origin) (sameOrigin : origin = use.origin)
    (value : Ty) (seen : Observes model origin value) :
    Equivalent value (model (candidate.binder use.name)).1 := by
  apply registered_readback path old candidate registered valid use present actual origin sameOrigin use.name
  · exact (binder_collision_iff candidate old use.name use.name seed
      candidateNotOutput oldNotOutput candidateNonpoint oldNonpoint).mpr ⟨invocation,declaration,rfl⟩
  · exact seen

end Yulang.GeneralNominalBinderIdentity181
