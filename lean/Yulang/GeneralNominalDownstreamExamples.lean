import Yulang.GeneralNominalDownstreamBoundary
import Yulang.GeneralNominalSupportExamples
import Yulang.GeneralNominalSupportRankObstruction

/-! Actual source-supported installations retain their child identities and
named equations. The direct output-growth continuation is still blocked. -/
namespace Yulang.GeneralNominalDownstreamExamples
open GeneralNominalSupport GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples

theorem display_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = displayRoot ∧ packet.declaration.id = 1 ∧ packet.children = [displayChild] ∧
    GeneralNominalDownstreamSteps.Step registry displayRoot (GeneralNominalSupportExamples.start displayRoot)
      (GeneralNominalSupportSteps.install (GeneralNominalSupportExamples.start displayRoot) packet support) := by
  obtain ⟨packet,support,root,key,children,step⟩ := GeneralNominalSupportExamples.display_expands
  exact ⟨packet,support,root,key,children,GeneralNominalDownstreamSteps.empty_ledger_step rfl step⟩

theorem wrap_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = wrapRoot ∧ packet.declaration.id = 2 ∧ packet.children = [wrapChild] ∧
    wrapChild.demand.outputs = [⟨1,itemTarget⟩] ∧
    GeneralNominalDownstreamSteps.Step registry wrapRoot (GeneralNominalSupportExamples.start wrapRoot)
      (GeneralNominalSupportSteps.install (GeneralNominalSupportExamples.start wrapRoot) packet support) := by
  obtain ⟨packet,support,root,key,children,step⟩ := GeneralNominalSupportExamples.wrap_expands
  exact ⟨packet,support,root,key,children,rfl,GeneralNominalDownstreamSteps.empty_ledger_step rfl step⟩

theorem p_first_step : GeneralNominalDownstreamSteps.Step GeneralNominalSupportSiblings.reg
    GeneralNominalSupportSiblings.root GeneralNominalSupportSiblings.start GeneralNominalSupportSiblings.afterP :=
  GeneralNominalDownstreamSteps.empty_ledger_step rfl GeneralNominalSupportSiblings.first_step

theorem p_first_formed : GeneralNominalDownstreamSteps.SourceFormed GeneralNominalSupportSiblings.reg
    GeneralNominalSupportSiblings.root GeneralNominalSupportSiblings.afterP :=
  .update (.initial _ GeneralNominalSupportSiblings.initial_source) p_first_step

theorem r_first_step : GeneralNominalDownstreamSteps.Step GeneralNominalOutputGrowth.registry
    (GeneralNominalOutputGrowthModels.root 0) GeneralNominalSupportGrowth.start GeneralNominalSupportGrowth.added :=
  GeneralNominalDownstreamSteps.empty_ledger_step rfl GeneralNominalSupportGrowth.first_install

theorem r_refresh : GeneralNominalDownstreamSteps.Step GeneralNominalOutputGrowth.registry
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

theorem r_formed : GeneralNominalDownstreamSteps.SourceFormed GeneralNominalOutputGrowth.registry
    (GeneralNominalOutputGrowthModels.root 0) GeneralNominalSupportGrowth.observed :=
  .update (.update (.initial _ (GeneralNominalOutputGrowthModels.initial_source 0)) r_first_step) r_refresh

theorem r_child_blocked (packet : Packet roles) (support : List (Occurrence roles))
    (context : packet.context = GeneralNominalSupportGrowth.observed.current.context)
    (focus : packet.site.occurrence = GeneralNominalOutputGrowthPackets.child 0) :
    ¬ GeneralNominalDownstreamSupport.PacketGuard GeneralNominalSupportGrowth.observed packet support := by
  intro guard
  have old := guard.1.2
  rw [context,focus] at old
  exact GeneralNominalSupportGrowth.child_not_ready support old.1 (old.2.1 ⟨0,by decide⟩)

theorem r_child_pending : GeneralNominalDownstreamBoundary.Local GeneralNominalOutputGrowth.registry
    GeneralNominalSupportGrowth.observed (GeneralNominalOutputGrowthPackets.child 0) .pending := by
  apply GeneralNominalDownstreamBoundary.support_pending
  · exact GeneralNominalOutputGrowthRefresh.child_ready
  · rintro ⟨support,guard,_⟩
    exact GeneralNominalSupportGrowth.child_not_ready support guard.1 (guard.2.1 ⟨0,by decide⟩)
  · exact GeneralNominalOutputGrowthRefresh.child_not_rootK2
  · exact GeneralNominalOutputGrowthRefresh.child_not_candidateK2

/-- The successful guarded first installation still refutes a rank based on
arbitrary journal-model denotations. The new rule does not make that proposed
measure valid, even though it prevents the recursive continuation. -/
theorem no_modelwise_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : CommonNominalFullCarrier.Ty → Measure) :
    ¬ (∀ model, Models GeneralNominalSupportGrowth.added.current model →
      less (rank (model ((GeneralNominalOutputGrowthPackets.child 0).demand.arguments ⟨0,by decide⟩).1).1)
        (rank (model ((GeneralNominalOutputGrowthModels.root 0).demand.arguments ⟨0,by decide⟩).1).1)) :=
  GeneralNominalSupportGrowth.no_modelwise_guarded_rank less wellFounded rank

theorem sibling_source_conservative (model : GeneralNominalCommonBridge.Assignment)
    (source : GeneralNominalState.Models GeneralNominalSupportSiblings.src model) :
    AllModels GeneralNominalSupportSiblings.afterP model := by
  apply (GeneralNominalSupportSteps.formed_exact GeneralNominalSupportSiblings.first_formed model).mp
  apply (GeneralNominalFeedbackSites.install_models GeneralNominalSupportSiblings.start.current
    GeneralNominalSupportSiblings.pk (GeneralNominalFeedbackSites.emitted GeneralNominalSupportSiblings.pk) rfl model).mpr
  exact ⟨(initial_models _ _ model).mpr source,GeneralNominalSupportSiblings.p_branch model source⟩

theorem unresolved_siblings_grounded :
    GeneralNominalDownstreamSupport.Grounded GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP
      GeneralNominalSupportSiblings.kidC ∧
    GeneralNominalDownstreamSupport.Grounded GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP
      GeneralNominalSupportSiblings.kidW := by
  constructor <;> exact GeneralNominalDownstreamSupport.source_conservative_grounded _ _ sibling_source_conservative _

theorem redundant_cycle_harmless :
    GeneralNominalSupportRankObstruction.Permitted GeneralNominalSupportSiblings.afterP GeneralNominalSupportSiblings.root
      GeneralNominalSupportSiblings.kidC GeneralNominalSupportSiblings.kidW ∧
    GeneralNominalSupportRankObstruction.Permitted GeneralNominalSupportSiblings.afterP GeneralNominalSupportSiblings.root
      GeneralNominalSupportSiblings.kidW GeneralNominalSupportSiblings.kidC ∧
    GeneralNominalDownstreamSupport.Supported GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP
      [GeneralNominalSupportSiblings.kidC,GeneralNominalSupportSiblings.kidW] := by
  refine ⟨GeneralNominalSupportRankObstruction.sibling_cycle.1,
    GeneralNominalSupportRankObstruction.sibling_cycle.2,?_⟩
  intro producer member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact unresolved_siblings_grounded.1
  · exact unresolved_siblings_grounded.2

end Yulang.GeneralNominalDownstreamExamples
