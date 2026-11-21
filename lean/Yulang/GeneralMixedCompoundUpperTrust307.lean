import Yulang.GeneralMixedCompoundUpperSnapshot307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 6500000
namespace Yulang.GeneralMixedCompoundUpperTrust307
open GeneralDictionaryJournalRefinement228Source (snapshot width_two)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundPoint238 (original_plan_retained)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralNominalVersionedSupport233
open GeneralNominalVersionedPlans231 (Inputs)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem retained : oldPlan ∈ refreshed.plans := original_plan_retained

theorem input_trusted : Trusted refreshed [.input oldPlan] := by
  refine .input oldPlan .source retained ?_
  intro slot visited test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound snapshot model valid.1
    (GeneralNominalSupport.head_recorded head)

theorem aggregate (m : Assignment) (valid : SliceModels refreshed [.input oldPlan] m) :
    Equivalent (m upper).1 .emptyRecord := by
  have input : Inputs oldPlan m := valid.2.2 _ (List.mem_singleton_self _)
  have merges := input.1.2.1
  rw [GeneralDictionaryCompoundPacket238.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model m
    ((_ ++ GeneralNominalAllocation.equations upper (.inter (.var 2) (.var 2))) ++ _) at merges
  have right := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1 |>.2
  have eq := (GeneralNominalCaptureMerges.equations_exact ..).mp right
  have upperTwo : Equivalent (m upper).1 (m 2).1 :=
    ⟨subtype_trans eq.1 ((common_inter_is_meet _ _ _).mp (subtype_refl _)).1,
      subtype_trans ((common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩) eq.2⟩
  exact GeneralDictionaryDefaultExpression209.equivalent_trans upperTwo (width_two m valid.1)

theorem ports (m : Assignment) (facts : SliceModels refreshed [.input oldPlan] m) :
    Equivalent (m GeneralDictionaryCompoundBase239.lo).1 (variant 0 (m 4).1) ∧
    Equivalent (m GeneralDictionaryCompoundBase239.hi).1 (variant 0 (m 2).1) :=
  ⟨GeneralDictionaryCompoundTrust239.lower m facts,GeneralDictionaryCompoundTrust239.upper m facts⟩

end Yulang.GeneralMixedCompoundUpperTrust307
