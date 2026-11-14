import Yulang.GeneralNominalHeadCoreOverlap185
import Yulang.GeneralNominalHeadReadback185
import Yulang.GeneralNominalBinderIdentity181

/-! Exact metadata of a historical purpose-eight producer. The invocation
identity conclusion does not assert equality of whole occurrences. -/
namespace Yulang.GeneralNominalHeadBinderIdentity185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalSupportProvenance182
open GeneralNominalRegisteredReadback182
open GeneralNominalCenteredHeadWFBoundary (boundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem registered_binder_identity
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (equal : plan.binder name =
      fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    name = owner ∧ position = 0 ∧
    plan.packet.site.occurrence.identity = invocation ∧ plan.packet.declaration.id = declaration ∧
    name ∉ plan.packet.declaration.outputNames ∧
    ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 := by
  have separate := GeneralNominalHeadCoreOverlap185.capture_separate reachable plan.packet
    (GeneralNominalHeadCoreOverlap185.wf_registered_packet reachable plan registered)
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
    (GeneralNominalHeadReadback185.wf_registered_configuration reachable plan registered).1] at equal
  have identities := (GeneralNominalCenteredAllocation.fresh_identity
    state.core.erased.current.context.state.seed
    (plan.packet.site.occurrence.identity,plan.packet.declaration.id,8,name,0)
    (invocation,declaration,8,owner,position)).mp equal
  simp only [Prod.mk.injEq,true_and] at identities
  exact ⟨identities.2.2.1,identities.2.2.2.symm,identities.1,identities.2.1,notOutput,nonpoint⟩


end Yulang.GeneralNominalHeadBinderIdentity185
