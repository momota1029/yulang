import Yulang.GeneralDictionaryJournalRefinement229Raw
import Yulang.GeneralDictionaryJournalRefinement228Reachable
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement229Diagnostic
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralDictionaryJournalRefinement228Stage
open GeneralDictionaryJournalRefinement229Snapshot
open GeneralDictionaryJournalRefinement229Refresh
open GeneralDictionaryJournalRefinement229Raw
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters

theorem reachable : B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles)
    sourceRegistry root after :=
  ⟨start,initial,.tail GeneralDictionaryJournalRefinement228Reachable.path GeneralDictionaryJournalRefinement229Refresh.step⟩

theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models after model :=
  (GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate).mpr stage_model

theorem no_survivor (key children) :
    ¬ GeneralNominalCenteredHeadCandidates.Survivor registry refreshedContext root key children := by
  rintro ⟨_,d,visible,_,_,_,_,_,prepared,_⟩
  cases List.mem_singleton.mp visible
  exact not_prepared prepared

theorem failed : GeneralNominalCenteredHeadCandidates.Failed registry refreshedContext root declaration := by
  refine ⟨?_,?_,[(0,0)],rfl,?_,?_,Or.inr ?_⟩
  · exact source.metadata
  · intro key member _
    exact List.mem_append_right _ member
  · rw [GeneralDictionaryJournalRefinement229Raw.report_exact]
  · rw [GeneralDictionaryJournalRefinement229Raw.report_exact]
  · rintro ⟨m,head⟩; exact no_head_model m head

theorem not_root_pending : ¬ GeneralNominalState.RootPending refreshedSnapshot
    (GeneralNominalCenteredHeadCandidates.inputs root).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 5),rfl,Or.inr ⟨GeneralDictionaryJournalRefinement228Reobserve.exactCopy,rfl⟩⟩

theorem not_inspection_pending : ¬ GeneralNominalCenteredHeadCandidates.InspectionPending registry refreshedContext root := by
  rintro ⟨_,d,visible,_,notFailed,_⟩
  cases List.mem_singleton.mp visible
  exact notFailed failed

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady after root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one _ last two _
  cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
  exact .refl _

theorem rejected : GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry after root .rejected := by
  classical
  have prior : B4TargetV6.Local (GeneralDictionaryDefaultBoundary208.boundary roles).toV6 sourceRegistry after root .rejected := by
    apply B4TargetV6.Local.rejected
    refine ⟨not_root_pending,Or.inr (Or.inr ⟨?_,Or.inl no_survivor⟩)⟩
    rintro (pending | missing)
    · exact not_inspection_pending pending
    · exact missing administrative_ready
  have noAmbiguity : ¬ B4TargetV7.PriorityAmbiguity (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry after root := by
    rintro ⟨_,a,xs,z,ys,one,_,_⟩
    exact no_survivor a xs one
  have v7 : GeneralDictionaryDefaultBoundary208.Local sourceRegistry after root .rejected := by
    by_cases conflict : (GeneralDictionaryDefaultBoundary208.boundary roles).MergedOutputConflict sourceRegistry after root
    · exact .mergedRejected conflict noAmbiguity
    · exact .ordinary conflict prior
  by_cases conflict : GeneralDictionaryHeadSharingConflict220.Conflict sourceRegistry after root
  · exact .sharingRejected conflict noAmbiguity
  · exact .ordinary conflict v7

/-- The reachable stage that defeated raw instance extraction is not stable.
An actual trusted refresh preserves its full journal model and rejects its root.
This is a regression, not a proof of the general EvidenceNode obligation. -/
theorem regression :
    ¬ GeneralDictionaryDefaultKernel208.Stable registry stage root ∧
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root after ∧
    GeneralNominalCenteredHeadMatStepJournal.Models after model ∧
    GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry after root .rejected :=
  ⟨not_stable,reachable,inhabited,rejected⟩
end Yulang.GeneralDictionaryJournalRefinement229Diagnostic
