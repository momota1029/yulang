import Yulang.GeneralWhereOriginReceipt318
import Yulang.GeneralWhereOriginLayoutContract318
import Yulang.GeneralWhereOriginRealInstall318
import Yulang.GeneralWhereOriginHeadAgree318
import Yulang.GeneralWhereOriginCurrent318
import Yulang.GeneralWhereOriginShadow318

open Yulang
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralWhereVersionInstall317 (before fixed Models InstallStep)
open GeneralWhereOriginTrace318 (Trace)
open GeneralWhereOriginSingleCells318 (loOld loNow hi oldChild newChild)
open GeneralWhereOriginSingleSource318 (older newer oldPlan newPlan)
open GeneralWhereOriginSingleModel318 (previousLo previousHi presentLo presentHi)
open GeneralNominalVersionedPlans231 (HeadModels variables)

example :
    InstallStep GeneralLiveCompoundRegistry316.sourceRegistry before fixed ∧
    Trace GeneralLiveCompoundRegistry316.sourceRegistry fixed ∧
    (∃ m, Models before m ∧ Models fixed m) ∧
    ∀ d ∈ GeneralWhereVersionCompiler317.children GeneralLiveCompoundPostFrames316.rootPlan,
      GeneralNominalSaturationState.Generated fixed.mixed.core.erased.current root d :=
  GeneralWhereOriginRealInstall318.executed

example :
    oldChild.occurrence.identity = newChild.occurrence.identity ∧ loOld ≠ loNow ∧
    oldChild.occurrence.demand.arguments 0 = (loOld,hi) ∧
    newChild.occurrence.demand.arguments 0 = (loNow,hi) :=
  GeneralWhereOriginSingleCells318.unique_endpoint

example :
    ∃ m, HeadModels older m ∧ HeadModels newer m ∧
      previousLo.row.Holds (variables oldPlan m) m ∧ previousHi.row.Holds (variables oldPlan m) m ∧
      presentLo.row.Holds (variables newPlan m) m ∧ presentHi.row.Holds (variables newPlan m) m :=
  GeneralWhereOriginHeadAgree318.exact_observations

example (vars : GeneralNominalMaterialization.Mode → Nat → CommonNominalFullCarrier.Ty) :
    GeneralWhereOriginShadow318.Span vars GeneralDictionaryDefault214ActualShadowRegression.expression :=
  GeneralWhereOriginShadow318.checked_shadow_example vars

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 15000000

/-- Reconstruct the actual lower row receipt from the C317 physical slot. -/
example (m : GeneralNominalCommonBridge.Assignment) (valid : Models fixed m) :
    ∃ p ∈ fixed.versionedWhere, ∃ c : GeneralWhereOriginDelta318.Cell p,
      p.packet.site.occurrence.identity = root.identity ∧
      p.packet.declaration = GeneralLiveCompoundRegistry316.declaration ∧
      c.row = GeneralWhereOriginFixture318.lowerCurrent.row ∧
      c.row ∈ (GeneralWhereVersionCompiler317.schema p).equations := by
  have f := (GeneralWhereVersionCurrentCert317.current_certified m valid).1
  have frame : GeneralNominalVersionedEvidence231.Frame
      (GeneralVersionedHistoryEvidence310.Compiled GeneralLiveCompoundRegistry316.sourceRegistry)
      fixed.mixed.core root GeneralLiveCompoundRegistry316.declaration.id
      GeneralWhereVersionRootReport317.plan := by
    rw [GeneralWhereVersionInstall317.mixed_eq]
    exact f
  have physical : GeneralDictionaryBinderLocations.sourceSlot (GeneralWhereOriginTrace318.rawOf fixed).base
      GeneralWhereOriginFixture318.lowerCurrent.row.target = some GeneralWhereVersionBase317.loSlot := by
    change GeneralDictionaryBinderLocations.sourceSlot GeneralWhereVersionSnapshot317.snap.base _ = _
    exact GeneralWhereVersionReuse317.exact_slots.1
  obtain ⟨p,seen,c,owner,decl,_,_,_,row,recorded⟩ :=
    GeneralWhereOriginReceipt318.exact_receipt GeneralLiveCompoundRegistry316.boundary_checked
      GeneralWhereOriginCheckedLayout318.enumerated_trace frame
      GeneralWhereOriginFixture318.lowerCurrent physical
  exact ⟨p,seen,c,owner,decl,row,recorded⟩
