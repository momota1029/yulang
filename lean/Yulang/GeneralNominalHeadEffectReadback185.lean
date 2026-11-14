import Yulang.GeneralNominalHeadEffectsOrigin185
import Yulang.GeneralNominalHeadOutputSupport185

/-! Actual reachable snapshot and live output support produces uniform
actual-origin readback. No target-exclusion or historical-snapshot premise is
left to the caller; both are derived from the actual head-step trace. -/
namespace Yulang.GeneralNominalHeadEffectReadback185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem wf_request_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (focus : Occurrence roles) (output : GeneralSourceState.Output)
    (member : output ∈ requests state.core focus) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ≠ output.target := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  obtain ⟨site,registered,_,present⟩ := mem_requests_iff.mp member
  rw [(GeneralNominalCenteredHeadStepTrace.configuration_trace path).1]
  intro equal
  exact GeneralNominalCenteredAllocation.outside_pool source high
    (equal.symm ▸ (GeneralNominalCenteredHeadStepEnumeration.source_pool source
      (GeneralNominalCenteredHeadStepAncestry.installed_depth_bound point ground) path).2 site registered output present)

theorem wf_effect_packet_seed
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) :
    effect.plan.packet.context.state.seed = state.core.erased.current.context.state.seed := by
  rw [effect.frame.context_eq]
  exact GeneralNominalHeadEffectsOrigin185.wf_effect_seed reachable effect member

theorem wf_effect_context_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose) :
    fresh effect.plan.packet.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalState.sources effect.plan.packet.context.state := by
  obtain ⟨before,prior,snapshot,_⟩ := GeneralNominalHeadEffectsOrigin185.wf_effect_snapshot_reachable reachable effect member
  rw [effect.frame.context_eq,snapshot]
  exact GeneralNominalHeadSiteSupport185.wf_sources_separate prior high

theorem wf_live_overlap_iff
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources state.core effect.plan.packet.site.occurrence effect.plan ↔
    ∃ entry ∈ (outputSchema state.core effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name := by
  have seed := wf_effect_packet_seed reachable effect member
  rw [← seed]
  apply GeneralNominalHeadOutputSupport185.output_overlap_iff _ _ _ high
    (wf_effect_context_separate reachable effect member high)
  intro output present
  rw [seed]
  exact wf_request_separate reachable _ output present high

theorem wf_live_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose)
    (overlap : fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources state.core effect.plan.packet.site.occurrence effect.plan) :
    ∃ entry ∈ (outputSchema state.core effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name ∧
      ∀ model : Assignment, Models state model →
        GeneralNominalOriginTerms.Same model entry.origin
          (.source (fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position)) := by
  obtain ⟨entry,present,actual,equal⟩ := (wf_live_overlap_iff reachable effect member high).mp overlap
  refine ⟨entry,present,actual,equal,?_⟩
  intro model valid
  rw [equal]
  simpa only [actual,ite_true] using ((valid.2 effect member).2).1.2 entry present

theorem wf_snapshot_overlap_iff
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources effect.snapshot effect.plan.packet.site.occurrence effect.plan ↔
    ∃ entry ∈ (outputSchema effect.snapshot effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name := by
  have seed := wf_effect_packet_seed reachable effect member
  rw [← seed]
  apply GeneralNominalHeadOutputSupport185.output_overlap_iff _ _ _ high
    (wf_effect_context_separate reachable effect member high)
  obtain ⟨before,prior,snapshot,_⟩ := GeneralNominalHeadEffectsOrigin185.wf_effect_snapshot_reachable reachable effect member
  intro output present
  rw [effect.frame.context_eq,snapshot]
  rw [snapshot] at present
  exact wf_request_separate prior _ output present high

theorem wf_snapshot_overlap_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (member : effect ∈ state.effects) (high : 7 ≤ purpose)
    (overlap : fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.outputSources effect.snapshot effect.plan.packet.site.occurrence effect.plan) :
    ∃ entry ∈ (outputSchema effect.snapshot effect.plan.packet.site.occurrence effect.plan).variables,
      entry.mode = .actual ∧
      fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position = effect.plan.binder entry.name ∧
      ∀ model : Assignment, Models state model →
        GeneralNominalOriginTerms.Same model entry.origin
          (.source (fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position)) := by
  obtain ⟨entry,present,actual,equal⟩ := (wf_snapshot_overlap_iff reachable effect member high).mp overlap
  refine ⟨entry,present,actual,equal,?_⟩
  intro model valid
  rw [equal]
  simpa only [actual,ite_true] using ((valid.2 effect member).1).2.1.2 entry present

end Yulang.GeneralNominalHeadEffectReadback185
