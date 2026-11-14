import Yulang.GeneralNominalSiteOrigin182
import Yulang.GeneralNominalRawOrigin182

/-! The assigned ground boundary supplies the retrospective depth bound.
These producer facts are about its actual reachable states, without adding a
caller-supplied bound. They do not establish its EvidenceNode field. -/
namespace Yulang.GeneralNominalGroundProvenance182
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open GeneralNominalCenteredTrace (configuration_trace)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

 theorem site_origin (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites) :
    site = rootSite state.erased.current.context.state.seed root ∨
      ∃ plan ∈ state.plans, site ∈ plan.emitted := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(configuration_trace path).1]
  exact GeneralNominalSiteOrigin182.initial_site_origin path site member

 theorem plan_seed (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (member : plan ∈ state.plans) :
    plan.packet.context.state.seed = state.erased.current.context.state.seed := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact (GeneralNominalSiteOrigin182.plan_seed path plan member).trans (configuration_trace path).1.symm

 theorem report_no_center (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.erased.current.packets)
    (high : 7 ≤ purpose) :
    fresh state.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.reportSources packet.context.state
        (GeneralNominalRecursiveCandidates.report packet.context packet.declaration packet.bounds) := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(configuration_trace path).1]
  exact GeneralNominalRawOrigin182.fresh_outside_packet_report source
    (GeneralNominalCenteredAncestry.installed_depth_bound point ground) path packet member high

 theorem site_needed (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧
      plan.binder name = site.center index := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(configuration_trace path).1] at center
  exact GeneralNominalSiteOrigin182.purpose_eight_site_needed source path site member index center

 theorem site_fits (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.erased.current.context.state.seed invocation declaration 8 owner position)
    (valid : Models state model) :
    ∃ plan ∈ state.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧
      plan.binder name = site.center index ∧ GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (site.center index)).1 := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  rw [(configuration_trace path).1] at center
  exact GeneralNominalSiteOrigin182.purpose_eight_site_fits source path site member index center valid

end Yulang.GeneralNominalGroundProvenance182
