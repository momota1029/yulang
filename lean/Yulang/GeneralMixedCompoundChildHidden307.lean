import Yulang.GeneralMixedCompoundChildEquality307
import Yulang.GeneralRebaseClosedEdgeCompound279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000
namespace Yulang.GeneralMixedCompoundChildHidden307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundFrame238 (before installed effect)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot)
open GeneralDictionaryCompoundBase239 (source)
open GeneralMixedCompoundChildEquality307 (mid hi equal_refreshed separation mid_not_read)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step Equal)
open GeneralNominalSaturationState (Generated)

theorem no_reservation : mid ∉ extendedSnapshot.reserved := by
  change mid ∉ (GeneralNominalVersionedAllocation231.reserved snapshot registry root.identity
    GeneralDictionaryCompoundPacket238.packet.bindings)
  rw [GeneralDictionaryCompoundPacket238.bindings_exact]
  decide +kernel

theorem unsupported :
    mid ∉ GeneralNominalState.sources refreshed.core.erased.current.context.state := by
  change mid ∉ GeneralNominalState.sources extendedSnapshot
  intro present
  simp only [GeneralNominalState.sources,List.mem_append] at present
  apply mid_not_read
  simp only [GeneralDictionaryDefaultRawSupport213.sources,List.mem_append]
  rcases present with ((types | rows) | reserved) | atoms
  · exact Or.inl (Or.inl types)
  · exact Or.inl (Or.inr rows)
  · exact False.elim (no_reservation reserved)
  · exact Or.inr atoms

theorem child_center : childSite.center 0 = mid := by decide +kernel

theorem generated_child : Generated refreshed.core.erased.current root childSite.occurrence :=
  .child .root (GeneralNominalVersionedInstall232.installed_child
    (GeneralDictionaryCompoundSites238.children ▸ List.mem_singleton_self _))

theorem root_request_retained :
    GeneralSourceState.Output.mk 0 4 ∈ GeneralNominalCenteredHeadOutputs.requests refreshed.core root := by
  apply GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr
  refine ⟨GeneralNominalDemandMerging.pointSite root,?_,.refl _,?_⟩
  · exact GeneralDictionaryCompoundSites238.raw_sites ▸ List.mem_cons_self ..
  · exact List.mem_singleton_self _

/-- Knowing full semantic equality, even at an actually generated child with
a known endpoint, is insufficient for the feedback rule. The hidden actual
center is part of the journal-only materialization, not a raw source. -/
theorem actual_center_gap :
    Generated refreshed.core.erased.current root childSite.occurrence ∧
    childSite.center 0 = mid ∧ Equal refreshed mid hi ∧
    ¬ GeneralNominalFeedbackSteps.RawEqual refreshed.core.erased.current mid hi ∧
    mid ∉ GeneralNominalState.sources refreshed.core.erased.current.context.state :=
  ⟨generated_child,child_center,equal_refreshed,separation,unsupported⟩

theorem no_feedback_pair :
    ¬ (mid ∈ GeneralNominalState.sources refreshed.core.erased.current.context.state ∧
      hi ∈ GeneralNominalState.sources refreshed.core.erased.current.context.state ∧
      Equal refreshed mid hi ∧
      ¬ GeneralNominalFeedbackSteps.RawEqual refreshed.core.erased.current mid hi) :=
  fun h => unsupported h.1

theorem no_refresh_into_support {ctx} (valid : GeneralNominalVersionedMixedObservations233.Refresh refreshed ctx) :
    ¬ GeneralNominalState.Known ctx.state mid := by
  rintro ⟨slot,equal,_⟩
  exact unsupported (valid.support _ (equal ▸ GeneralNominalAllocationSupport.slot_source ctx.state slot))

end Yulang.GeneralMixedCompoundChildHidden307
