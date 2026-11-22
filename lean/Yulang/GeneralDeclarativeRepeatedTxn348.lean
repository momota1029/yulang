import Yulang.GeneralDeclarativeTxnCell348
import Yulang.GeneralDeclarativeNativeRepeatInput347
import Yulang.GeneralWhereVersionPreserve317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 40000000
namespace Yulang.GeneralDeclarativeRepeatedTxn348
open GeneralDeclarativeWhereTxn348 (SourcePermit Txn exact_models)
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereVersionSnapshot317 (context)
open GeneralWhereVersionRefine317 (refines)
open GeneralWhereVersionPreserve317 (exact_legacy_projection)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (sourceRegistry boundary_checked)
open GeneralLiveCompoundPostRootHead316 (frame)
open GeneralDeclarativeNativePlacement347 (exact_root)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot)
open GeneralDeclarativeInitialRoot343 (support)
open GeneralDeclarativeNativeReplay347 (keep)
open GeneralDeclarativeNativeRepeatStage347 (spans)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereOriginSupport318 (journalSources)

theorem original_focus : rootPlan.packet.site.occurrence = GeneralDictionaryJournalRefinement228Source.root :=
  frame.occurrence_eq

theorem effective :
    GeneralDeclarativeStoppedPaired341.activeDemand before.mixed rootPlan.input =
      GeneralDeclarativeVersionedRootGuard342.actualDemand := exact_root

noncomputable def permit : SourcePermit sourceRegistry before rootPlan where
  view := observedRoot
  done := fun _ => False
  support := support _
  waiting := GeneralDeclarativeVersionedChildWitness342.waiting
  models m fit := GeneralDeclarativeNativeRoot347.starting_model m fit.1
  choice := by
    rw [effective]
    exact GeneralDeclarativeNativeRepeatInput347.elected _
  keep := keep
  named := observedRoot
  spans := spans
  receipts := []
  input := by
    rw [effective]
    exact GeneralDeclarativeNativeRepeatInput347.exact_inputs _ _

theorem checked : Txn sourceRegistry before context rootPlan := by
  refine ⟨boundary_checked,original_focus.symm ▸ frame,⟨permit⟩,⟨refines⟩,rfl,
    GeneralLiveCompoundProposedRepair316.choice_compatible,?_⟩
  intro m fit
  obtain ⟨n,valid,same⟩ := exact_legacy_projection m fit
  refine ⟨n,valid,?_⟩
  intro a present
  change a ∈ GeneralNominalVersionedJournalFrame236.sources after ++ [] at present
  rw [List.append_nil] at present
  exact same a present

theorem exactly (m : Assignment) :
    Models before m ↔ ∃ n, Models fixed n ∧ GeneralNominalCenteredFrame179.Agree (journalSources before) m n :=
  exact_models checked m

end Yulang.GeneralDeclarativeRepeatedTxn348
