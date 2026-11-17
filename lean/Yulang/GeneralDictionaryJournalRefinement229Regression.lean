import Yulang.GeneralDictionaryJournalRefinement229Selected
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement229Regression
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralDictionaryJournalRefinement228Stage
open GeneralDictionaryJournalRefinement229Selected
open GeneralDictionaryJournalRefinement229Refresh (after)

theorem selected_without_instance :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root stage ∧
    GeneralNominalCenteredHeadMatStepJournal.Models stage model ∧
    GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry stage root
      (.selected declaration.id currentPacket.children) ∧
    ¬ GeneralDictionaryTotalEvidence206.Instance registry stage.core model root declaration.id currentPacket.children ∧
    ¬ GeneralDictionaryHeadSharingBoundary220.Stable sourceRegistry stage root :=
  ⟨GeneralDictionaryJournalRefinement228Reachable.reachable,stage_model,selected,no_instance,
    GeneralDictionaryJournalRefinement229Refresh.not_stable⟩

theorem stage_generated_root (demand)
    (generated : GeneralNominalSaturationState.Generated stage.core.erased.current root demand) : demand = root := by
  induction generated with
  | root => rfl
  | child generated edge ih =>
    change _ ∈ [] ++ packet.children.map (fun child => (root,child)) at edge
    rw [children_empty] at edge
    cases edge
  | alias generated first last same ih =>
    cases List.mem_singleton.mp last
    rfl

/-- The exact stage still satisfies the original EvidenceAt obligation: its
only generated demand is not stable. This guards against misreporting the
stronger no-stability counterexample as an EvidenceNode refutation. -/
theorem stage_evidenceAt : B4SkeletonV8.EvidenceAt
    (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry stage root := by
  intro m valid demand key children dictionaries reached stable childStable chosen evidence
  have same : demand = root := by
    rcases reached with same | generated
    · exact same
    · exact stage_generated_root demand generated
  subst demand
  exact False.elim (GeneralDictionaryJournalRefinement229Refresh.not_stable stable)

end Yulang.GeneralDictionaryJournalRefinement229Regression
