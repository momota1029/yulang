import Yulang.GeneralMixedCompoundPointSteps308
import Yulang.GeneralMixedCompoundSourceFork308
import Yulang.GeneralMixedCompoundPointFirstExact308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedCompoundPointTrace308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry checked declaration)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundSourcePrefix308 (pointBefore)
open GeneralMixedCompoundPointFirstPlan308 (pointFirst candidateModel)
open GeneralMixedCompoundPointPorts308 (afterSnap)
open GeneralMixedCompoundPointView308 (previously_unknown)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointOutcome308 (local_child tree result)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedMixedResolver236 (rejected)
open CommonRoleOutermostResolver (classification)

theorem child_waits :
    GeneralNominalState.RootPending afterSnap
      (GeneralNominalVersionedCandidates231.inputs childSite.occurrence).demand :=
  ⟨⟨0,by decide⟩,previously_unknown⟩

theorem pending_child :
    Local sourceRegistry pointFirst childSite.occurrence .pending := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have notSharing : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict registry pointFirst childSite.occurrence := by
    rintro ⟨_,_,_,safe,_⟩
    exact safe.1 child_waits
  have h (focus : GeneralSourceDictionaries.Occurrence roles) :
      GeneralNominalCenteredHeadOutputs.EqualOutputs pointFirst.core focus candidateModel := by
    intro a one b two same
    exact GeneralMixedCompoundPointSites308.equal_outputs candidateModel focus a
      ((GeneralNominalVersionedRefresh232.refresh_requests pointFirst GeneralMixedCompoundPointView308.context).mpr one)
      b ((GeneralNominalVersionedRefresh232.refresh_requests pointFirst GeneralMixedCompoundPointView308.context).mpr two) same
  have notMerged := GeneralNominalVersionedMergedConflict232.models_exclude_conflict
    GeneralMixedCompoundPointFirstInstall308.point_first_held (fun focus _ => h focus) (h childSite.occurrence)
  exact .ordinary notSharing (.ordinary notMerged (.pending child_waits))

theorem resolver_waits :
    GeneralNominalVersionedMixedResolver236.tree ⟨rfl,checked⟩
      GeneralMixedCompoundPointFirstInstall308.reachable childSite.occurrence = .pending :=
  GeneralNominalVersionedMixedResolver236.pending ⟨rfl,checked⟩
    GeneralMixedCompoundPointFirstInstall308.reachable pending_child

theorem resolver_rejects :
    GeneralNominalVersionedMixedResolver236.tree ⟨rfl,checked⟩
      GeneralMixedCompoundPointChild308.reachable childSite.occurrence = .rejected :=
  rejected ⟨rfl,checked⟩ GeneralMixedCompoundPointChild308.reachable local_child

theorem actual_prefix : B4Target.Steps (Step registry root) before observed :=
  .tail GeneralMixedCompoundPointFirstInstall308.two_step GeneralMixedCompoundPointViewTrust308.step

theorem actual_emission_observation :
    GeneralNominalSaturationState.Generated pointFirst.core.erased.current root childSite.occurrence ∧
    Step registry root pointFirst observed ∧
    Local sourceRegistry pointFirst childSite.occurrence .pending ∧
    Local sourceRegistry observed childSite.occurrence .rejected ∧
    ∀ payload, ¬ Evidence registry observed.core candidateModel root payload :=
  ⟨GeneralMixedCompoundPointFirstInstall308.generated_child,GeneralMixedCompoundPointViewTrust308.step,
    pending_child,local_child,GeneralMixedCompoundPointEvidence308.no_recursive_root _⟩

end Yulang.GeneralMixedCompoundPointTrace308
