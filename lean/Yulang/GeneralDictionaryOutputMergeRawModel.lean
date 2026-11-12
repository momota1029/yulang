import Yulang.GeneralDictionaryOutputMergeSuccess
import Yulang.GeneralDictionaryRecursiveObstruction

/-! The scalar facts of the recorded parent are absent from the raw context.
Changing both merged output targets together preserves that raw context. -/
namespace Yulang.GeneralDictionaryOutputMergeRawModel
open GeneralDictionaryOutputMergeSuccess
open GeneralNominalExamples (model state)
open CommonNominalFullCarrier

abbrev badModel : GeneralNominalCommonBridge.Assignment := fun source =>
  if source = outputTarget 10 ∨ source = outputTarget 11 then (.base .str,Common.rowEmpty)
  else model source

theorem output_above_one (n : Nat) : 1 < outputTarget n := by
  exact GeneralNominalIdentities.source_above_seed (state true).seed
    (GeneralNominalAllocation.origin 100 1 5 (n+20) 0)

theorem at_zero : badModel 0 = model 0 := by
  have a := output_above_one 10
  have b := output_above_one 11
  simp only [badModel,show ¬(0 = outputTarget 10 ∨ 0 = outputTarget 11) by omega,ite_false]

theorem at_one : badModel 1 = model 1 := by
  have a := output_above_one 10
  have b := output_above_one 11
  simp only [badModel,show ¬(1 = outputTarget 10 ∨ 1 = outputTarget 11) by omega,ite_false]

theorem at_left : badModel (outputTarget 10) = (.base .str,Common.rowEmpty) := by unfold badModel; rw [ite_eq_left (Or.inl rfl)]; rfl
theorem at_right : badModel (outputTarget 11) = (.base .str,Common.rowEmpty) := by unfold badModel; rw [ite_eq_left (Or.inr rfl)]; rfl

theorem source_model : GeneralNominalState.Models (state true) badModel := by
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ GeneralSourceState.equationAtoms (1 : Fin 2) (.base .int) at member
    simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change Subtype (badModel 1).1 (.base .int)
      rw [at_one]; exact subtype_refl _
    · change Subtype (.base .int) (badModel 1).1
      rw [at_one]; exact subtype_refl _
  · intro slot term recorded
    by_cases yes : slot = 1
    · subst slot
      have equal : (Core.PresenceGeneration.TyTerm.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = term := by
        simpa [GeneralNominalExamples.heads,GeneralSourceState.Head.equation] using recorded
      subst term
      change Equivalent (badModel 1).1 (.base .int)
      rw [at_one]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [GeneralNominalExamples.heads,yes,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    change pair ∈ [(0,0),(1,1)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    by_cases zero : slot = 0
    · subst slot
      have same : GeneralNominalExamples.listDescriptor = descriptor := Option.some.inj recorded
      subst descriptor
      refine ⟨[.inl (.base .int)],?_,?_⟩
      · refine .cons ?_ .nil
        · change Subtype (badModel 1).1 (.base .int) ∧ Subtype (.base .int) (badModel 1).1
          rw [at_one]; exact ⟨subtype_refl _,subtype_refl _⟩
      · change Equivalent (badModel 0).1 (nominal 0 [.inl (.base .int)])
        rw [at_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [state,zero] at recorded

theorem raw_model : GeneralNominalState.Models current.state badModel := by
  refine ⟨source_model.1,source_model.2.1,?_⟩
  have shape : current.state.ordinary =
      [.tyLe (.var 1) (.var 1),.tyLe (.var 0) (.var 0),.tyLe (.var 0) (.var 0),
       .tyLe (.var 1) (.var 1),.tyLe (.var (outputTarget 10)) (.var (outputTarget 11)),
       .tyLe (.var (outputTarget 11)) (.var (outputTarget 10))] := by decide +kernel
  rw [shape]
  intro atom member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals change Subtype _ _
  all_goals first | exact subtype_refl _ | (rw [at_left,at_right]; exact subtype_refl _)

theorem not_output_one : ¬ Equivalent (badModel (outputTarget 10)).1 (badModel 1).1 := by
  rw [at_left,at_one]
  intro equal
  have old := (CommonNominalFullModelMap.subtype_exact (.base .str) (.base .int)).mp equal.1
  cases (CommonRigidHeadInspection.base_iff .str .int).mp old
theorem not_raw_equal : ¬ GeneralNominalFeedbackSteps.RawEqual finish.current (outputTarget 10) 1 := by
  intro equal
  exact not_output_one (equal badModel raw_model)
end Yulang.GeneralDictionaryOutputMergeRawModel
