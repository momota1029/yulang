import Yulang.GeneralDictionaryCompoundModel238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundTotal238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPacket238 (plan packet actual lo hi frame)
open GeneralDictionaryCompoundModel238
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open CommonNominalFullCarrier

theorem emitted_schema : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩,
      ⟨names 0,.lower,.variant 0 (.variable 0)⟩,
      ⟨names 1,.upper,.variant 0 (.variable 0)⟩],false⟩ := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem variables_lower : GeneralNominalCenteredHeadMatEffects.variables plan extended .lower 0 = (extended lo).1 := by
  unfold GeneralNominalCenteredHeadMatEffects.variables
  simp [show (0 ∉ declaration.outputNames) from by decide +kernel]
  congr 2
  decide +kernel

theorem variables_upper : GeneralNominalCenteredHeadMatEffects.variables plan extended .upper 0 = (extended hi).1 := by
  unfold GeneralNominalCenteredHeadMatEffects.variables
  simp [show (0 ∉ declaration.outputNames) from by decide +kernel]
  congr 2
  decide +kernel

theorem variables_actual : GeneralNominalCenteredHeadMatEffects.variables plan extended .actual 0 = (extended actual).1 := by
  unfold GeneralNominalCenteredHeadMatEffects.variables
  simp [show (0 ∉ declaration.outputNames) from by decide +kernel]
  rw [GeneralDictionaryCompoundPacket238.binder_exact]

theorem emitted_holds : (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
    (GeneralNominalCenteredHeadMatEffects.variables plan extended) extended := by
  rw [emitted_schema]
  intro equation member
  rcases List.mem_cons.mp member with rfl | member
  · change Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
    rw [old_value 4 (by simp [pool])]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rcases List.mem_cons.mp member with rfl | member
    · simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,variables_lower]
      change Equivalent (extended (names 0)).1 (variant 0 (extended lo).1)
      rw [fresh_value 0,old_value lo (by simp [pool]),GeneralDictionaryCompoundPacket238.lower_value]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp member
      simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,variables_upper]
      change Equivalent (extended (names 1)).1 (variant 0 (extended hi).1)
      rw [fresh_value 1,old_value hi (by simp [pool]),GeneralDictionaryCompoundPacket238.upper_value]
      exact ⟨subtype_refl _,subtype_refl _⟩

theorem child_schema (signature : child.Signature roles) :
    GeneralNominalCenteredHeadMatPlans.childSchema plan child signature =
      ⟨[⟨names 2,.actual,.variant 0 (.variable 0)⟩],false⟩ := rfl

theorem child_holds (signature : child.Signature roles) :
    (GeneralNominalCenteredHeadMatPlans.childSchema plan child signature).Holds
      (GeneralNominalCenteredHeadMatEffects.variables plan extended) extended := by
  rw [child_schema]
  intro equation member
  cases List.mem_singleton.mp member
  simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,variables_actual]
  change Equivalent (extended (names 2)).1 (variant 0 (extended actual).1)
  rw [fresh_value 2,old_value actual (by simp [pool]),GeneralDictionaryCompoundPacket238.actual_value]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan extended := by
  apply (GeneralDictionaryReachableRest227.packet_characterization plan frame extended inhabited).mpr
  refine ⟨?_,head_holds,emitted_holds,?_⟩
  · exact (GeneralNominalAllocation.propagate_models ..).mp
      ((GeneralNominalState.extend_models ..).mp head_model.1).1 |>.2.2
  · intro clause member signature
    cases List.mem_singleton.mp member
    refine ⟨?_,child_holds signature⟩
    intro index
    have same : index = 0 := Fin.ext (by have h := index.isLt; change index.val < 1 at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h))
    subst index
    change Subtype (extended (names 0)).1 (extended (names 2)).1 ∧
      Subtype (extended (names 2)).1 (extended (names 1)).1
    rw [fresh_value 0,fresh_value 1,fresh_value 2]
    exact ⟨(common_variant_iff ..).mpr GeneralDictionaryOptionalOutput229.below_width,subtype_refl _⟩

end Yulang.GeneralDictionaryCompoundTotal238
