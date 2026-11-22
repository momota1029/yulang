import Yulang.GeneralDeclarativeVersionedCurrent342
import Yulang.GeneralDeclarativeVersionedChildView342
import Yulang.GeneralDeclarativeVersionedSeparation342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeVersionedReceipt342
open GeneralWherePhysicalCommit319 (final)
open GeneralWherePhysicalCurrentRead319 (plan low high reads address_lo address_hi)
open GeneralWherePhysicalCurrentModel319 (emitted_rows binder_now exact_child)
open GeneralWhereOriginSingleCells318 (loNow hi loOld sig)
open GeneralWhereOriginSingleSource318 (oldPlan)
open GeneralWhereOriginSingleRead318 (old_reads)
open GeneralWhereOriginSingleModel318 (previousHi)
open GeneralWherePhysicalTicket319 (target_eq upper_physical)
open GeneralDeclarativeVersionedPhysical342 (current transported holds_now recorded_version)
open GeneralDeclarativeVersionedChildView342 (lower actual upper supported basis)
open GeneralDeclarativeVersionedRows342 (ordinary aligned)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralWhereVersionCompiler317 (schema)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereVersionCase317 (expr)
open GeneralDictionaryOptionalExpression229 (expression)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralNominalCommonBridge (Assignment)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralLiveCompoundRegistry316 (otherChild)

theorem lower_exact : ordinary plan low.row = lower := by
  change (⟨GeneralVersionedEndpointAddress315.atCell plan .lower otherChild.id 0 expr,
    .variant 0 (.variable (variableSource plan .lower 0))⟩ : GeneralDeclarativeHead320.Equation) = lower
  rw [address_lo,reads.1]

theorem upper_exact : ordinary plan high.row = upper := by
  change (⟨GeneralVersionedEndpointAddress315.atCell plan .upper otherChild.id 0 expr,
    .variant 0 (.variable (variableSource plan .upper 0))⟩ : GeneralDeclarativeHead320.Equation) = upper
  rw [address_hi,reads.2]

theorem actual_exact : ordinary plan (⟨mid,.actual,expr⟩ : Equation) = actual := by
  change (⟨mid,.variant 0 (.variable (GeneralNominalVersionedFrame231.binder plan 0))⟩ :
    GeneralDeclarativeHead320.Equation) = actual
  rw [binder_now 0 (.inl rfl)]

abbrev ownerOutput : GeneralDeclarativeHead320.Equation := ⟨4,expression⟩

theorem current_order :
    (schema current).equations.map (ordinary current) = [ownerOutput,lower,upper] := by
  unfold current
  rw [aligned transported,emitted_rows]
  simp only [List.map_cons,List.map_nil,lower_exact,upper_exact]
  rfl

/-- The actual center is justified by the genuine current clause's
centre schema, not by pretending it was written as a source row,
or by silently using one of the two lower/upper addresses. -/
theorem center_receipt :
    (GeneralNominalVersionedPlans231.childSchema plan otherChild sig).equations.map (ordinary plan) = [actual] := by
  rw [exact_child sig]
  simp only [List.map_cons,List.map_nil,actual_exact]

theorem reused_exact : ordinary oldPlan previousHi.row = upper := by
  change (⟨hi,.variant 0 (.variable (variableSource oldPlan .upper 0))⟩ :
    GeneralDeclarativeHead320.Equation) = upper
  rw [old_reads.2]

theorem current_literals (m : Assignment) (valid : Models final m) :
    (schema current).equations.map (ordinary current) = [ownerOutput,lower,upper] ∧
    (∀ row ∈ [ownerOutput,lower,upper], GeneralDeclarativeEntailment320.Holds m row) ∧
    ownerOutput.left = 4 ∧ ordinary oldPlan previousHi.row = upper := by
  refine ⟨current_order,?_,rfl,reused_exact⟩
  intro row used
  exact GeneralDeclarativeVersionedRows342.all current m (holds_now m valid) _ (current_order.symm ▸ used)

end Yulang.GeneralDeclarativeVersionedReceipt342
