import Yulang.GeneralDictionaryCompoundChild239
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryCompoundFailure239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundSites238
open GeneralDictionaryCompoundSnapshot239 GeneralDictionaryCompoundRefresh239
open GeneralDictionaryCompoundChild239

theorem fresh : GeneralNominalVersionedAllocation231.Fresh extendedSnapshot registry childSite.occurrence.identity [] := by
  have outside : ∀ key ∈ GeneralNominalVersionedAllocation231.keys registry childSite.occurrence.identity [],
      GeneralNominalIdentities.source snapshot.seed key ∉ GeneralNominalState.sources extendedSnapshot := by decide +kernel
  intro key member collision
  exact False.elim (outside key member collision)

theorem failed : GeneralNominalVersionedCandidates231.Failed registry extendedContext childSite.occurrence declaration := by
  refine ⟨GeneralDictionaryCompoundSource238.source.metadata,[(5,6)],located,?_,?_,?_,?_⟩
  · rw [report_exact]
    exact fresh
  · rw [report_exact]
  · rw [report_exact]
  · left; rw [report_exact]; intro h; cases h

theorem known : ¬ GeneralNominalState.RootPending extendedSnapshot childSite.occurrence.demand := by
  rintro ⟨index,unknown⟩
  have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
  subst index
  exact unknown GeneralDictionaryCompoundRefreshStep239.lower_known

theorem no_inspection_pending : ¬ GeneralNominalVersionedCandidates231.InspectionPending registry extendedContext childSite.occurrence := by
  rintro ⟨_,candidate,visible,_,notFailed,_⟩
  cases List.mem_singleton.mp visible
  exact notFailed failed
end Yulang.GeneralDictionaryCompoundFailure239
