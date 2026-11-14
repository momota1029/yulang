import Yulang.GeneralNominalCenteredPermutationCounterparts

set_option backward.isDefEq.respectTransparency false

/-! Both legacy classifier guards and joint alias applicability transport with
the candidate plan. The current-context equalities are explicit premises. -/
namespace Yulang.GeneralNominalCenteredPermutationInstallable
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalJournalPermutation
open GeneralNominalCenteredPermutationCounterparts
variable {roles : Roles.RoleDecls} {r s : Registry}
variable {left right : GeneralNominalSaturationState.State roles}

theorem cycle_order (order : Reorders r s) (roleEq : r.roles = roles)
    (context) (root : Occurrence roles) (frontier) :
    GeneralNominalCycleK2.Local r context root frontier ↔ GeneralNominalCycleK2.Local s context root frontier :=
  GeneralLocalPredicateCongruence.local_iff (first := GeneralNominalCycleK2.fields roles)
    (last := GeneralNominalCycleK2.fields roles) (r₁ := r) (r₂ := s) Iff.rfl Iff.rfl
    (GeneralNominalCandidateReordering.cycle_candidateK2 order context root)
    (GeneralNominalCandidateReordering.cycle_inspection_pending order roleEq context root)
    (GeneralNominalCandidateReordering.survivor order roleEq context root) frontier

theorem feedback_order (order : Reorders r s) (roleEq : r.roles = roles)
    (state : GeneralNominalSaturationState.State roles) (root : Occurrence roles) (frontier) :
    GeneralNominalFeedbackK2.Local r state root frontier ↔ GeneralNominalFeedbackK2.Local s state root frontier :=
  GeneralLocalPredicateCongruence.local_iff (first := GeneralNominalFeedbackK2.fields roles)
    (last := GeneralNominalFeedbackK2.fields roles) (r₁ := r) (r₂ := s) Iff.rfl Iff.rfl
    (GeneralNominalCandidateReordering.feedback_candidateK2 order state root)
    (GeneralNominalCandidateReordering.cycle_inspection_pending order roleEq state.context root)
    (GeneralNominalCandidateReordering.survivor order roleEq state.context root) frontier

theorem choice_forward (same : Related left right) {packet other : GeneralNominalSaturationState.Packet roles}
    (pair : PacketPair packet other) (valid : GeneralNominalCycleSteps.ChoiceCompatible left packet) :
    GeneralNominalCycleSteps.ChoiceCompatible right other := by
  intro prior member alias
  obtain ⟨old,present,paired⟩ := same.packet_right member
  rw [← pair.identity,← paired.identity]
  apply valid old present
  apply (same.alias _ _).mpr
  rwa [pair.site,paired.site]

theorem choice (same : Related left right) {packet other : GeneralNominalSaturationState.Packet roles}
    (pair : PacketPair packet other) :
    GeneralNominalCycleSteps.ChoiceCompatible left packet ↔ GeneralNominalCycleSteps.ChoiceCompatible right other :=
  ⟨choice_forward same pair,choice_forward same.symm pair.symm⟩

theorem merges (same : Related left right) (site : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalCycleSteps.MergesClosed left site ↔ GeneralNominalCycleSteps.MergesClosed right site := by
  have models := funext (fun model => propext (same.models model))
  simp only [GeneralNominalCycleSteps.MergesClosed,same.sites,models,same.alias]

theorem feedback_merges (same : Related left right) (site : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalFeedbackSteps.MergesClosed left site ↔ GeneralNominalFeedbackSteps.MergesClosed right site := by
  simp only [GeneralNominalFeedbackSteps.MergesClosed,same.sites,same.sameInputs,same.alias]

theorem installable_forward (same : Related left right) (order : Reorders r s) (roleEq : r.roles = roles)
    {plan other : Plan roles} (matched : Match plan other)
    (registry : other.packet.registry = s) (context : other.packet.context = right.context)
    (visible : other.packet.declaration ∈ s.declarations)
    (enabled : GeneralNominalFeedbackSteps.Installable r left plan.packet) :
    GeneralNominalFeedbackSteps.Installable s right other.packet := by
  obtain ⟨⟨originalRegistry,originalContext,site,_,role,located,prepared,selected,compatible,closed,model,joint⟩,feedback,merged⟩ := enabled
  have siteEq := matched.packet.site
  have idEq := matched.packet.identity
  have childrenEq := matched.packet.children
  refine ⟨⟨registry,context,?_,visible,?_,matched.located.mp located,matched.prepared.mp prepared,
    ?_,(choice same matched.packet.toPacketPair).mp compatible,?_,?_,?_⟩,?_,?_⟩
  · rw [← siteEq,← same.sites]; exact site
  · rw [← siteEq,← matched.declaration.role]; exact role
  · rw [← siteEq,← idEq,← childrenEq]
    exact (cycle_order order roleEq right.context _ _).mp
      ((GeneralNominalCenteredPermutationApplicability.cycle_local same.context r _ _).mp selected)
  · rw [← siteEq]; exact (merges same _).mp closed
  · obtain ⟨model,valid,branch⟩ := model
    exact ⟨model,(same.models model).mp valid,(matched.packet.holds model).mp branch⟩
  · rw [← siteEq,← idEq]
    exact (GeneralDictionaryJointReordering.joint order roleEq right _ _).mp
      ((GeneralNominalCenteredPermutationApplicability.joint same r _ _).mp joint)
  · rw [← siteEq,← idEq,← childrenEq]
    exact (feedback_order order roleEq right _ _).mp
      ((GeneralNominalCenteredPermutationApplicability.feedback_local same r _ _).mp feedback)
  · rw [← siteEq]; exact (feedback_merges same _).mp merged

theorem installable (same : Related left right) (order : Reorders r s) (roleEq : r.roles = roles)
    {plan other : Plan roles} (matched : Match plan other)
    (oneRegistry : plan.packet.registry = r) (twoRegistry : other.packet.registry = s)
    (oneContext : plan.packet.context = left.context) (twoContext : other.packet.context = right.context)
    (oneVisible : plan.packet.declaration ∈ r.declarations) (twoVisible : other.packet.declaration ∈ s.declarations) :
    GeneralNominalFeedbackSteps.Installable r left plan.packet ↔ GeneralNominalFeedbackSteps.Installable s right other.packet :=
  ⟨installable_forward same order roleEq matched twoRegistry twoContext twoVisible,
    installable_forward same.symm (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq)
      matched.symm oneRegistry oneContext oneVisible⟩

end Yulang.GeneralNominalCenteredPermutationInstallable
