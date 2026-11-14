import Yulang.GeneralNominalRawSupport183
import Yulang.GeneralNominalCenteredGroundBoundary

/-! The original ground boundary supplies the installed depth bound for the
historical private/capture exclusions. Full raw support is not yet covered. -/
namespace Yulang.GeneralNominalGroundRawSupport183
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalCenteredTrace (configuration_trace)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem capture_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) (name : Nat) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      (GeneralNominalPacketSupport.capture packet).outputs name ∧
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).1 ∧
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ≠
      ((GeneralNominalPacketSupport.capture packet).inputs name).2 := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(configuration_trace path).1]
  exact GeneralNominalRawSupport183.historical_capture_separate source
    (GeneralNominalCenteredAncestry.installed_depth_bound point ground) path packet member high name

theorem private_separate
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources packet.privateContext.state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(configuration_trace path).1]
  exact GeneralNominalRawSupport183.historical_private_separate source
    (GeneralNominalCenteredAncestry.installed_depth_bound point ground) path packet member high

end Yulang.GeneralNominalGroundRawSupport183
