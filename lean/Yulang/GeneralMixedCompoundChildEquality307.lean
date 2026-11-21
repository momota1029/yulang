import Yulang.GeneralDictionaryCompoundRefreshStep239
import Yulang.GeneralRebaseCompoundOwnerCapture273
import Yulang.GeneralDictionaryDefaultRawSupport213

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 6000000
namespace Yulang.GeneralMixedCompoundChildEquality307
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds variables childSchema)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralDictionaryJournalRefinement228Source (root width_two)
open GeneralDictionaryCompoundPoint238 (point original_plan_retained)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundSource238 (child)
open GeneralDictionaryCompoundSites238 (signature)
open GeneralDictionaryCompoundRefresh239 (refreshed models_iff)
open GeneralDictionaryCompoundSnapshot239 (extendedSnapshot)
open GeneralDictionaryDefaultRawSupport213 (sources)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

abbrev hi := GeneralDictionaryCompoundModel238.names 1
abbrev mid := GeneralDictionaryCompoundModel238.names 2

theorem historical_child_center (m : Assignment) (held : Holds oldPlan m) :
    Equivalent (m mid).1 (variant 0 (m 2).1) := by
  have fact := (held.2.1.2.2.2.2.2.2 child (List.mem_singleton_self _) signature).2
  rw [GeneralNominalVersionedPlans231.childSchema_eq,GeneralDictionaryCompoundTotal238.child_schema] at fact
  have center := fact _ (List.mem_singleton_self _)
  change Equivalent (m mid).1 (variant 0 (variables oldPlan m .actual 0)) at center
  have value : variables oldPlan m .actual 0 =
      (m (GeneralNominalVersionedFrame231.binder oldPlan 0)).1 := by
    rfl
  rw [value] at center
  have width := GeneralRebaseCompoundOwnerCapture273.historical_center m held
  exact equivalent_trans center ⟨(common_variant_iff ..).mpr width.1,(common_variant_iff ..).mpr width.2⟩

theorem equal_point : Equal point mid hi := by
  intro m valid
  have upper := GeneralDictionaryCompoundTrust239.upper m
    (GeneralNominalVersionedSupport233.trusted_models GeneralDictionaryCompoundTrust239.trusted valid)
  have center := historical_child_center m (valid.2.1 oldPlan original_plan_retained)
  exact equivalent_trans center ⟨upper.2,upper.1⟩

theorem equal_refreshed : Equal refreshed mid hi :=
  fun m valid => equal_point m ((models_iff m).mp valid)

def altered (m : Assignment) : Assignment := fun n =>
  if n = mid then (.top,(m n).2) else m n

theorem mid_distinct : mid ≠ hi := by decide +kernel

theorem mid_not_read : mid ∉ sources extendedSnapshot := by decide +kernel

theorem separation : ¬ GeneralNominalFeedbackSteps.RawEqual refreshed.core.erased.current mid hi := by
  intro equal
  let witness := GeneralDictionaryCompoundVersionedModel238.extended
  have raw : GeneralNominalState.Models extendedSnapshot witness :=
    GeneralDictionaryCompoundRefreshStep239.inhabited.1.1
  have changed : GeneralNominalState.Models extendedSnapshot (altered witness) :=
    (GeneralDictionaryDefaultRawSupport213.models_iff _ (fun n hn => by
      have different : n ≠ mid := fun e => mid_not_read (e ▸ hn)
      rw [altered,ite_eq_right different])).mp raw
  have clash := equal (altered witness) changed
  have value := GeneralDictionaryCompoundVersionedPacket238.child_value 1
  simp only [altered,ite_true,ite_eq_right (Ne.symm mid_distinct)] at clash
  rw [value] at clash
  change Equivalent .top (variant 0 .emptyRecord) at clash
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head _
    (GeneralNominalOriginCongruence238.test_iff clash (.structural (.variant 0)) |>.mpr
     (by exact ⟨[.emptyRecord],rfl,subtype_refl _,subtype_refl _⟩))

end Yulang.GeneralMixedCompoundChildEquality307
