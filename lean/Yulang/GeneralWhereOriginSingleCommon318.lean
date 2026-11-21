import Yulang.GeneralWhereOriginSingleModel318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralWhereOriginSingleCommon318
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (old_reads new_reads)
open GeneralWhereOriginSingleCells318 (loOld loNow hi lower_moves upper_kept)
open GeneralWhereOriginSingleModel318
open GeneralNominalVersionedExpressionFrame236 (variable_value)
open GeneralNominalVersionedPlans231 (variables private_models_iff HeadModels)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Models sources)
open GeneralNominalAllocationSupport (slot_source)
open CommonNominalFullCarrier

private theorem old_four : (4:Nat) ∈ sources older.context.state :=
  slot_source older.context.state (4 : Fin 5)
private theorem old_two : (2:Nat) ∈ sources older.context.state :=
  slot_source older.context.state (2 : Fin 5)
private theorem new_two : (2:Nat) ∈ sources newer.context.state :=
  slot_source newer.context.state (2 : Fin 8)

theorem recorded_lo (m : Assignment) :
    previousLo.row.Holds (variables oldPlan (previous m)) (previous m) := by
  change Equivalent (previous m loOld).1 (variant 0 (variables oldPlan (previous m) .lower 0))
  rw [variable_value,old_reads.1,← old_oldSources m 4 old_four]
  exact (two_writes m).1

theorem recorded_hi (m : Assignment) :
    previousHi.row.Holds (variables oldPlan (previous m)) (previous m) := by
  change Equivalent (previous m hi).1 (variant 0 (variables oldPlan (previous m) .upper 0))
  rw [variable_value,old_reads.2,← old_oldSources m 2 old_two]
  exact (two_writes m).2

noncomputable abbrev result (m : Assignment) := patched (previous m)

theorem raw_agree_old (m : Assignment) : Agree (sources older.context.state) m (result m) := by
  intro n found
  exact (old_oldSources m n found).trans (patch_oldSources (previous m) n found)

theorem raw_agree_new (m : Assignment) : Agree (sources newer.context.state) m (result m) := by
  intro n found
  exact (old_newSources m n found).trans (patch_newSources (previous m) n found)

theorem retains_rows (m : Assignment) :
    previousLo.row.Holds (variables oldPlan (result m)) (result m) ∧
    previousHi.row.Holds (variables oldPlan (result m)) (result m) := by
  have lower := recorded_lo m
  change Equivalent (previous m loOld).1 (variant 0 (variables oldPlan (previous m) .lower 0)) at lower
  have upper := recorded_hi m
  change Equivalent (previous m hi).1 (variant 0 (variables oldPlan (previous m) .upper 0)) at upper
  constructor
  · change Equivalent (patched (previous m) loOld).1 (variant 0 (variables oldPlan (patched (previous m)) .lower 0))
    rw [variable_value,old_reads.1,← patch_oldSources (previous m) 4 old_four,
      ← patched_outside (previous m) loOld lower_moves.symm]
    rwa [variable_value,old_reads.1] at lower
  · change Equivalent (patched (previous m) hi).1 (variant 0 (variables oldPlan (patched (previous m)) .upper 0))
    rw [variable_value,old_reads.2,← patch_oldSources (previous m) 2 old_two,
      ← patched_outside (previous m) hi new_lo_ne_hi]
    rwa [variable_value,old_reads.2] at upper

theorem current_rows (m : Assignment) :
    presentLo.row.Holds (variables newPlan (result m)) (result m) ∧
    presentHi.row.Holds (variables newPlan (result m)) (result m) := by
  constructor
  · change Equivalent (patched (previous m) loNow).1 (variant 0 (variables newPlan (patched (previous m)) .lower 0))
    rw [variable_value,new_reads.1,← patch_newSources (previous m) 2 new_two]
    exact new_write (previous m)
  · have visible : declaration ∈ registry.declarations := List.mem_cons_self
    have checked : GeneralDeclarations.Checked registry := GeneralWhereOriginSingleSource318.checked
    exact (GeneralWhereVersionStoredRow317.same_target_iff checked
      (p := newPlan) (q := oldPlan) rfl rfl rfl visible visible
      presentHi.written.2 previousHi.written.2 upper_kept (result m)).mpr (retains_rows m).2

theorem common (m : Assignment)
    (old : Models older.context.state m) (now : Models newer.context.state m) :
    ∃ n, Models older.context.state n ∧ Models newer.context.state n ∧
      Agree (sources older.context.state ++ sources newer.context.state) m n ∧
      previousLo.row.Holds (variables oldPlan n) n ∧ previousHi.row.Holds (variables oldPlan n) n ∧
      presentLo.row.Holds (variables newPlan n) n ∧ presentHi.row.Holds (variables newPlan n) n ∧
      previous m hi = n hi ∧ previous m loOld = n loOld := by
  refine ⟨result m,GeneralNominalCenteredModelExtension.source_models_same _ (raw_agree_old m) old,
    GeneralNominalCenteredModelExtension.source_models_same _ (raw_agree_new m) now,?_,
    (retains_rows m).1,(retains_rows m).2,(current_rows m).1,(current_rows m).2,
    patched_outside _ _ new_lo_ne_hi,patched_outside _ _ lower_moves.symm⟩
  intro key found
  exact (List.mem_append.mp found).elim (raw_agree_old m key) (raw_agree_new m key)

theorem nonvacuous :
    ∃ m, Models older.context.state m ∧ Models newer.context.state m := by
  let w := GeneralLiveCompoundLeafProof316.w
  refine ⟨w,?_,GeneralLiveCompoundLeafProof316.valid.1.1⟩
  have old := GeneralLiveCompoundLeafProof316.valid.2.1 GeneralLiveCompoundRoot316.plan (List.mem_cons_self)
  exact ((private_models_iff ..).mp (GeneralNominalVersionedPlans231.head_models old).1).1

end Yulang.GeneralWhereOriginSingleCommon318
