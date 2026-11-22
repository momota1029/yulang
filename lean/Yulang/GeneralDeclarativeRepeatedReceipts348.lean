import Yulang.GeneralDeclarativeRepeatedDictionary348
import Yulang.GeneralDeclarativeTxnQuiet348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 39000
set_option maxHeartbeats 65000000
namespace Yulang.GeneralDeclarativeRepeatedReceipts348
open GeneralDeclarativeRepeatedDictionary348 (one_model rules dict)
open GeneralDeclarativeRepeatedWorld348 (now)
open GeneralDeclarativeRepeatedPlacement348 (requested)
open GeneralDeclarativeRepeatedClosure348 (Instance)
open GeneralDeclarativeRepeatedVisible348 (completed silent exact_rows)
open GeneralDeclarativeRepeatedRows348 (low high loRow hiRow corrected_position)
open GeneralDeclarativeTxnNormalized348 (Observed)
open GeneralDeclarativeStoppedPaired341 (activeDemand Placement)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand original_targets)
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereVersionSnapshot317 (context)
open GeneralWhereVersionCase317 (site occ)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralDeclarativeTxnComplete348 (actual_outputs)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralDictionaryJournalRefinement228Source (root interpretation)
open GeneralLiveCompoundRegistry316 (sourceRegistry)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalCommonBridge (Assignment)

theorem public_request :
    requests fixed.mixed.core rootPlan.packet.site.occurrence = [⟨0,4⟩] := by
  rw [GeneralDeclarativeTxnEffects348.literal_requests before context rootPlan silent rootPlan.packet.site.occurrence]
  have h := congrArg GeneralDeclarativeDemand320.Demand.outputs GeneralDeclarativeRepeatedTxn348.effective
  change requests before.mixed.core rootPlan.input.occurrence = actualDemand.outputs at h
  have exactOcc : rootPlan.input.occurrence = rootPlan.packet.site.occurrence := rfl
  rw [exactOcc,original_targets] at h
  exact h

theorem exact_output (m : Assignment) (fit : Models fixed m) :
    GeneralDictionaryDefaultEvidence204.OutputWitness rootPlan m ⟨0,4⟩ :=
  actual_outputs completed m fit ⟨0,4⟩ (public_request.symm ▸ List.mem_singleton_self _)

/-- A single repaired-fixture model witnesses both ordered recursive
dictionaries, the genuine child at its corrected ordinal, both current
mode-specific source receipts and the original public output. -/
theorem paired (m : Assignment) (fit : Models fixed m) :
    ∃ n, Models fixed n ∧ (∀ k ∈ journalSources fixed,n k = m k) ∧
      GeneralDeclarativeHead320.Models now n ∧
      GeneralSourceDictionaries.ErasedEvidence (Instance n) root dict ∧
      CommonRoleOutermostResolver.Classify rules actualDemand (.selected dict) ∧
      GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n actualDemand dict ∧
      Placement fixed.mixed now occ requested ∧
      fixed.mixed.core.sites[2]? = some site ∧
      Observed before fixed rootPlan low 0 site loRow ∧
      Observed before fixed rootPlan high 0 site hiRow ∧
      GeneralDictionaryDefaultEvidence204.OutputWitness rootPlan n ⟨0,4⟩ := by
  obtain ⟨n,raw,old,model,physical,selected,proves,placed⟩ := one_model m fit
  obtain ⟨l,h⟩ := exact_rows n raw
  exact ⟨n,raw,old,model,physical,selected,proves,placed,(corrected_position n raw).1,l,h,exact_output n raw⟩

end Yulang.GeneralDeclarativeRepeatedReceipts348
