import Yulang.GeneralNominalSiteSeparation184
import Yulang.GeneralNominalCenteredHeadStepEnumeration
import Yulang.GeneralNominalCenteredHeadWFBoundary

/-! Namespace exclusion for observed sites along the actual head-only step.
The WF wrapper derives the source and depth bound from its initial state;
it does not assume a simulation into the historical centered transition. -/
namespace Yulang.GeneralNominalHeadSiteSupport185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)
open GeneralNominalCenteredHeadStepAncestry (InstalledDepthBound)
open GeneralNominalCenteredHeadStepTrace (configuration_trace)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem trace_sources_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources state.core.erased.current.context.state :=
  fun member => GeneralNominalCenteredAllocation.outside_pool source high
    ((GeneralNominalCenteredHeadStepEnumeration.source_pool source bound path).1 member)

theorem trace_sites_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    ∀ site ∈ state.core.erased.current.sites,
      fresh context.state.seed invocation declaration purpose owner position ∉ rawSiteSources site := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    have supported := GeneralNominalSiteSupport184.point_sources root source.linked.1
    intro present
    exact GeneralNominalCenteredAllocation.outside_pool (limit := limit) source high
      (List.mem_append_left _ (supported present))
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalCenteredHeadStepProgress.generated_registered path generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro site member
      change site ∈ before.core.erased.current.sites ++
        plan.packet.children.map (GeneralNominalSharedEmission.childSite plan.packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp added
        have seed : plan.packet.context.state.seed = context.state.seed := by
          rw [enabled.frame.context_eq]
          exact (configuration_trace path).1
        have parent := ih plan.packet.site enabled.frame.raw_recorded
        have outside : fresh plan.packet.context.state.seed invocation declaration purpose owner position ∉
            GeneralNominalState.sources plan.packet.context.state := by
          rw [enabled.frame.context_eq,(configuration_trace path).1]
          exact trace_sources_separate source bound path high
        simpa only [seed] using GeneralNominalSiteSeparation184.child_separate plan.packet child childMember
          high outside (by simpa only [seed] using parent)

theorem wf_sources_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources state.core.erased.current.context.state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  rw [(configuration_trace path).1]
  exact trace_sources_separate source
    (GeneralNominalCenteredHeadStepAncestry.installed_depth_bound point ground) path high

theorem wf_sites_separate
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root state)
    (site : GeneralNominalDemandMerging.Site roles) (member : site ∈ state.core.erased.current.sites)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∉
      rawSiteSources site := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  rw [(configuration_trace path).1]
  exact trace_sites_separate source
    (GeneralNominalCenteredHeadStepAncestry.installed_depth_bound point ground) path high site member

end Yulang.GeneralNominalHeadSiteSupport185
