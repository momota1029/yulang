import Yulang.GeneralRebaseReceiptGuardedReadback289
import Yulang.GeneralRebaseMergeRegression264

/-! Applied to a previously checked real mixed-kernel merge. The supplied
sample is not claimed externally reachable or a new row fixture. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReceiptAliasControl289
open GeneralRebaseMergeRegression264 (sample merged last last_present last_absent merge_step)
open GeneralNominalCenteredHeadAllocMergeSource (roles registry root)
open GeneralNominalCenteredHeadAllocMergeInstall (aSite)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralRebaseReceiptGuardedProduct289 (guardedTick)
open GeneralRebaseReceiptMachine289 (Phase)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralDeclarations (Registry)

theorem actual_merge_gain :
    Step registry root sample merged ∧
    last ∉ requests sample.core aSite.occurrence ∧
    last ∈ requests merged.core aSite.occurrence :=
  ⟨merge_step,last_absent,last_present⟩

theorem actual_merge_excludes_even_replay (r : Registry) (ask stamp : Offer) (phase : Phase) :
    guardedTick r merged aSite.occurrence ask phase ≠ some (.published stamp) :=
  GeneralRebaseReceiptLiveEffects289.cannot_publish_effectful phase stamp last last_present

end Yulang.GeneralRebaseReceiptAliasControl289
