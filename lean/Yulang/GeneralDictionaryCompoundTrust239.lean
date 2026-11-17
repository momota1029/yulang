import Yulang.GeneralDictionaryCompoundVacuity238
import Yulang.GeneralNominalVersionedSupport233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundTrust239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundPoint238
open GeneralDictionaryCompoundObstruction238
open GeneralNominalVersionedSupport233 GeneralNominalVersionedPlans231
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem trusted : Trusted point [.input oldPlan] := by
  refine .input oldPlan .source original_plan_retained ?_
  intro slot visited test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound snapshot model valid.1
    (GeneralNominalSupport.head_recorded head)

theorem lower (model : Assignment) (valid : SliceModels point [.input oldPlan] model) :
    Equivalent (model (GeneralDictionaryCompoundModel238.names 0)).1 (variant 0 (model 4).1) := by
  have input : Inputs oldPlan model := valid.2.2 _ (List.mem_singleton_self _)
  have merges := input.1.2.1
  rw [GeneralDictionaryCompoundPacket238.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ((GeneralNominalAllocation.equations (GeneralDictionaryCompoundVersionedModel238.names 0) (.union (.var 4) (.var 4)) ++ _) ++ _) at merges
  have lower := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.1
  have eq := (GeneralNominalCaptureMerges.equations_exact ..).mp lower
  have aggregate : Equivalent (model (GeneralDictionaryCompoundVersionedModel238.names 0)).1 (model 4).1 :=
    ⟨subtype_trans eq.1 ((common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩),
      subtype_trans ((common_union_is_join _ _ _).mp (subtype_refl _)).1 eq.2⟩
  have emitted := input.2.2.2.2.2.1
  rw [GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema] at emitted
  have endpoint := emitted ⟨GeneralDictionaryCompoundModel238.names 0,.lower,.variant 0 (.variable 0)⟩
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by decide)
  simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value] at endpoint
  have capture : variables oldPlan model .lower 0 = (model (GeneralDictionaryCompoundVersionedModel238.names 0)).1 := by
    unfold variables
    simp [show (0 ∉ declaration.outputNames) from by decide]
    congr 2
    decide +kernel
  rw [capture] at endpoint
  exact ⟨subtype_trans endpoint.1 ((common_variant_iff ..).mpr aggregate.1),
    subtype_trans ((common_variant_iff ..).mpr aggregate.2) endpoint.2⟩

theorem upper (model : Assignment) (valid : SliceModels point [.input oldPlan] model) :
    Equivalent (model (GeneralDictionaryCompoundModel238.names 1)).1 (variant 0 (model 2).1) := by
  have input : Inputs oldPlan model := valid.2.2 _ (List.mem_singleton_self _)
  have merges := input.1.2.1
  rw [GeneralDictionaryCompoundPacket238.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ((_ ++ GeneralNominalAllocation.equations (GeneralDictionaryCompoundVersionedModel238.names 1) (.inter (.var 2) (.var 2))) ++ _) at merges
  have upper := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.2
  have eq := (GeneralNominalCaptureMerges.equations_exact ..).mp upper
  have aggregate : Equivalent (model (GeneralDictionaryCompoundVersionedModel238.names 1)).1 (model 2).1 :=
    ⟨subtype_trans eq.1 ((common_inter_is_meet _ _ _).mp (subtype_refl _)).1,
      subtype_trans ((common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩) eq.2⟩
  have emitted := input.2.2.2.2.2.1
  rw [GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema] at emitted
  have endpoint := emitted ⟨GeneralDictionaryCompoundModel238.names 1,.upper,.variant 0 (.variable 0)⟩
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) (by decide)
  simp only [GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value] at endpoint
  have capture : variables oldPlan model .upper 0 = (model (GeneralDictionaryCompoundVersionedModel238.names 1)).1 := by
    unfold variables
    simp [show (0 ∉ declaration.outputNames) from by decide]
    congr 2
    decide +kernel
  rw [capture] at endpoint
  exact ⟨subtype_trans endpoint.1 ((common_variant_iff ..).mpr aggregate.1),
    subtype_trans ((common_variant_iff ..).mpr aggregate.2) endpoint.2⟩
end Yulang.GeneralDictionaryCompoundTrust239
