import Yulang.GeneralDeclarativeVersionedRows342
import Yulang.GeneralWherePhysicalEvidence319
import Yulang.GeneralDeclarativeExactWalk323

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14800
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeVersionedSeparation342
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWherePhysicalCurrentRead319 (plan reads)
open GeneralWherePhysicalCurrentModel319 (emitted_rows)
open GeneralWherePhysicalActive319 (active refines)
open GeneralWherePhysicalPast319 (point_models loose_models)
open GeneralWherePhysicalChildModel319 (ports mid_value)
open GeneralWherePhysicalEvidence319 (recorded)
open GeneralWhereOriginSingleSource318 (oldPlan)
open GeneralWhereOriginSingleCells318 (loOld loNow hi oldChild)
open GeneralWhereOriginSingleModel318 (previousLo)
open GeneralWhereOriginSingleRead318 (old_reads)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalVersionedExpressionFrame236 (variable_value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent variant subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralDictionaryOptionalExpression229 (expression expression_value)
open GeneralDictionaryOptionalOutput229 (value not_width)
open GeneralDictionaryJournalRefinement228Source (width_two)
open GeneralDeclarativeExactWalk323 (variant_exact)

theorem root_output (m : Assignment) (valid : Models final m) :
    Equivalent (m 4).1 value := by
  have allRows := (valid.2 plan recorded).1.rows
  unfold GeneralNominalCenteredHeadMatSchemas.Schema.Holds at allRows
  rw [emitted_rows] at allRows
  have out := allRows _ List.mem_cons_self
  change Equivalent (m 4).1 (GeneralNominalCenteredHeadMatExpressions.value
    (variables plan m) .actual expression) at out
  rwa [expression_value] at out

theorem exact_width (m : Assignment) (valid : Models final m) :
    Equivalent (m 2).1 .emptyRecord := by
  have physical : GeneralNominalState.Models active m := valid.1.1.1
  have before := GeneralNominalRefinements.models refines m physical
  exact width_two m ((loose_models m).mp ((point_models m).mp before)).1

theorem archived (m : Assignment) (valid : Models final m) :
    Equivalent (m loOld).1 (variant 0 (m 4).1) := by
  have kept : oldPlan ∈ final.versionedWhere := List.mem_cons_self
  have row := (valid.2 oldPlan kept).1.rows previousLo.row previousLo.written.1
  change Equivalent (m loOld).1 (variant 0 (variables oldPlan m .lower 0)) at row
  rwa [variable_value,old_reads.1] at row

/-- On every actual final model the two registered lower endpoints are
not even semantically equivalent. This excludes an id-only source
locator and a model-equivalent alias at the stale version. -/
theorem unequal_operands (m : Assignment) (valid : Models final m) :
    ¬ Equivalent (m 4).1 (m 2).1 := by
  intro tied
  exact not_width (eqv_trans (eqv_symm (root_output m valid))
    (eqv_trans tied (exact_width m valid)))

theorem not_current_lower (m : Assignment) (valid : Models final m) :
    ¬ Equivalent (m loOld).1 (m loNow).1 := by
  intro equiv
  have same := eqv_trans (eqv_symm (archived m valid)) (eqv_trans equiv (ports m valid).1)
  have operands := (variant_exact 0 (m 4).1 (m 2).1).mp same
  exact unequal_operands m valid operands

/-- The actual historical captures are genuinely nonpoint in the
inhabited final models, while the corrected *current root* captures
read payload 2 at both bounds. The child still has distinct physical
endpoint IDs, even when their meanings agree. -/
theorem mode_changes (m : Assignment) (valid : Models final m) :
    (GeneralNominalVersionedFrame231.capture oldPlan.packet).inputs 0 = (4,2) ∧
    (GeneralNominalVersionedFrame231.capture plan.packet).inputs 0 = (2,2) ∧
    ¬ Equivalent (m 4).1 (m 2).1 ∧
    loNow ≠ hi ∧ Equivalent (m loNow).1 (m hi).1 := by
  refine ⟨GeneralWherePhysicalOldValues319.old_capture 0 (.inl rfl),
    GeneralWherePhysicalCurrentModel319.capture_now 0 (.inl rfl),unequal_operands m valid,
    GeneralWhereOriginSingleModel318.new_lo_ne_hi,?_⟩
  exact eqv_trans (ports m valid).1 (eqv_symm (ports m valid).2)

end Yulang.GeneralDeclarativeVersionedSeparation342
