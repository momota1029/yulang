import Yulang.GeneralNominalValueBoundary
import Yulang.GeneralNominalDownstreamExamples
import Yulang.GeneralNominalBudgetPrefix

/-! Source-supported installations remain executable with value provenance.
The old R and sibling-output obstructions remain blocked. These are actual
existing source traces, distinct from the six-role stress-test construction. -/
namespace Yulang.GeneralNominalValueExamples
open GeneralNominalSupport GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples

theorem display_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = displayRoot ∧ packet.declaration.id = 1 ∧ packet.children = [displayChild] ∧
    GeneralNominalValueSteps.Step registry displayRoot (GeneralNominalSupportExamples.start displayRoot)
      (GeneralNominalSupportSteps.install (GeneralNominalSupportExamples.start displayRoot) packet support) := by
  obtain ⟨packet,support,root,key,children,step⟩ := GeneralNominalDownstreamExamples.display_expands
  exact ⟨packet,support,root,key,children,GeneralNominalValueSteps.empty_ledger_step rfl step⟩

theorem wrap_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = wrapRoot ∧ packet.declaration.id = 2 ∧ packet.children = [wrapChild] ∧
    wrapChild.demand.outputs = [⟨1,itemTarget⟩] ∧
    GeneralNominalValueSteps.Step registry wrapRoot (GeneralNominalSupportExamples.start wrapRoot)
      (GeneralNominalSupportSteps.install (GeneralNominalSupportExamples.start wrapRoot) packet support) := by
  obtain ⟨packet,support,root,key,children,equation,step⟩ := GeneralNominalDownstreamExamples.wrap_expands
  exact ⟨packet,support,root,key,children,equation,GeneralNominalValueSteps.empty_ledger_step rfl step⟩

theorem p_first_step : GeneralNominalValueSteps.Step GeneralNominalSupportSiblings.reg
    GeneralNominalSupportSiblings.root GeneralNominalSupportSiblings.start GeneralNominalSupportSiblings.afterP :=
  GeneralNominalValueSteps.empty_ledger_step rfl GeneralNominalDownstreamExamples.p_first_step

theorem container_step : GeneralNominalValueSteps.Step GeneralNominalSupportSiblings.reg
    GeneralNominalSupportSiblings.root GeneralNominalSupportSiblings.afterP GeneralNominalBudgetContainer.afterC :=
  GeneralNominalValueSteps.source_install _ _ GeneralNominalSupportSiblings.children_generated.1
    GeneralNominalBudgetContainer.enabled GeneralNominalBudgetContainer.novel
    GeneralNominalDownstreamSiblingFixture.container_source_guard.1

theorem wrap_step : GeneralNominalValueSteps.Step GeneralNominalSupportSiblings.reg
    GeneralNominalSupportSiblings.root GeneralNominalBudgetContainer.afterC GeneralNominalBudgetPrefix.afterW :=
  GeneralNominalValueSteps.source_install _ _
    (GeneralNominalValueSteps.generated_monotone container_step GeneralNominalSupportSiblings.children_generated.2.1)
    GeneralNominalBudgetPrefix.enabled GeneralNominalBudgetPrefix.novel GeneralNominalBudgetPrefix.source_guard.1

theorem actual_sibling_prefix : B4Target.Steps
    (GeneralNominalValueSteps.Step GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.root)
    GeneralNominalSupportSiblings.start GeneralNominalBudgetPrefix.afterW :=
  .tail (.tail (.tail .refl p_first_step) container_step) wrap_step

theorem sibling_formed : GeneralNominalValueSteps.SourceFormed GeneralNominalSupportSiblings.reg
    GeneralNominalSupportSiblings.root GeneralNominalBudgetPrefix.afterW :=
  .update (.update (.update (.initial _ GeneralNominalSupportSiblings.initial_source) p_first_step) container_step) wrap_step

theorem sibling_downstream_blocked (support : List (Occurrence roles))
    (supported : GeneralNominalValueSupport.Supported GeneralNominalSupportSiblings.reg GeneralNominalBudgetPrefix.afterW support) :
    ¬ HeadSupported GeneralNominalBudgetPrefix.afterW support 2 (.nominal 0 1) :=
  GeneralNominalBudgetPrefix.actual_downstream_head_blocked support (GeneralNominalValueSupport.supported_old supported)

theorem r_first_step : GeneralNominalValueSteps.Step GeneralNominalOutputGrowth.registry
    (GeneralNominalOutputGrowthModels.root 0) GeneralNominalSupportGrowth.start GeneralNominalSupportGrowth.added :=
  GeneralNominalValueSteps.empty_ledger_step rfl GeneralNominalDownstreamExamples.r_first_step

theorem r_refresh : GeneralNominalValueSteps.Step GeneralNominalOutputGrowth.registry
    (GeneralNominalOutputGrowthModels.root 0) GeneralNominalSupportGrowth.added GeneralNominalSupportGrowth.observed := by
  refine ⟨GeneralNominalOutputGrowthPackets.child 0,?_,.administrative _ _
    (.refresh _ GeneralNominalOutputGrowthRefresh.refreshedContext
      GeneralNominalOutputGrowthRefresh.refresh_certificate 1 ?_ ?_
      GeneralNominalOutputGrowthRefresh.child_known)⟩
  · apply Generated.child .root
    change (GeneralNominalOutputGrowthModels.root 0,GeneralNominalOutputGrowthPackets.child 0) ∈
      [] ++ (GeneralNominalOutputGrowthPackets.packet 0).children.map _
    rw [GeneralNominalOutputGrowthPackets.children_exact]
    simp [GeneralNominalDemandMerging.pointSite]
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨GeneralNominalOutputGrowthPackets.endpoint 0,rfl⟩)))
  · exact (GeneralNominalOutputGrowthPackets.child_pending 0).choose_spec

theorem r_child_blocked (packet : Packet roles) (support : List (Occurrence roles))
    (context : packet.context = GeneralNominalSupportGrowth.observed.current.context)
    (focus : packet.site.occurrence = GeneralNominalOutputGrowthPackets.child 0) :
    ¬ GeneralNominalValueSupport.PacketGuard GeneralNominalSupportGrowth.observed packet support :=
  fun guard => GeneralNominalDownstreamExamples.r_child_blocked packet support context focus
    (GeneralNominalValueSupport.packet_old guard)

theorem r_formed : GeneralNominalValueSteps.SourceFormed GeneralNominalOutputGrowth.registry
    (GeneralNominalOutputGrowthModels.root 0) GeneralNominalSupportGrowth.observed :=
  .update (.update (.initial _ (GeneralNominalOutputGrowthModels.initial_source 0)) r_first_step) r_refresh

theorem r_child_pending : GeneralNominalValueBoundary.Local GeneralNominalOutputGrowth.registry
    GeneralNominalSupportGrowth.observed (GeneralNominalOutputGrowthPackets.child 0) .pending := by
  apply GeneralNominalValueBoundary.support_pending
  · exact GeneralNominalOutputGrowthRefresh.child_ready
  · rintro ⟨support,guard,_⟩
    exact GeneralNominalSupportGrowth.child_not_ready support guard.1 (guard.2.1 ⟨0,by decide⟩)
  · exact GeneralNominalOutputGrowthRefresh.child_not_rootK2
  · exact GeneralNominalOutputGrowthRefresh.child_not_candidateK2

end Yulang.GeneralNominalValueExamples
