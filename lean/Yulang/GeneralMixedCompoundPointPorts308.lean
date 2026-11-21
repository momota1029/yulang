import Yulang.GeneralMixedCompoundPointFirstPublic308
import Yulang.GeneralMixedCompoundChildHidden307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedCompoundPointPorts308
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundFrame238 (installed)
open GeneralDictionaryCompoundObstruction238 (currentPlan)
open GeneralMixedCompoundPointFirstPlan308 (plan pointFirst candidateModel same_plan)
open GeneralMixedCompoundPointFirstPublic308 (installed_held)
open GeneralNominalVersionedPlans231 (Holds Inputs variables)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Equal)
open GeneralRebaseCompoundOwnerCapture273 (PairFacts low high read_pair)
open GeneralRebaseCompoundReplacement273 (lower upper)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralNominalVersionedFrame231 (capture)
open PresenceNormalForm (all_append)

noncomputable abbrev afterSnap := pointFirst.core.erased.current.context.state

theorem current_pair (m : Assignment) (input : Inputs plan m) :
    PairFacts m (low plan) (high plan) 2 2 := by
  have agg := input.1.2.1
  rw [GeneralDictionaryCompoundCurrent238.bindings_exact] at agg
  have aligned := GeneralDictionaryCompoundPointHead238.capture_exact [] [] []
  change (low plan, high plan) = _ at aligned
  have lo : low plan = _ := congrArg Prod.fst aligned
  have hi : high plan = _ := congrArg Prod.snd aligned
  rw [lo,hi]
  exact ((all_append ..).mp agg).1

theorem ports (m : Assignment) (h : Inputs plan m) :
    Equivalent (m lower).1 (variant 0 (m 2).1) ∧
    Equivalent (m upper).1 (variant 0 (m 2).1) := by
  have pairs := read_pair m _ _ _ _ (current_pair m h)
  have facts := h.2.2.2.2.2.1
  rw [← GeneralDeferredLadderTransport302.emitted_eq same_plan,
    GeneralRebaseCompoundReplacement273.emitted_same,
    GeneralDictionaryCompoundVersionedPacket238.emitted_schema,
    GeneralDictionaryCompoundTotal238.emitted_schema] at facts
  have l := facts _ (List.mem_cons_of_mem _ (List.mem_cons_self)) (by decide)
  have u := facts _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) (by decide)
  change Equivalent (m lower).1 (variant 0 (variables plan m .lower 0)) at l
  change Equivalent (m upper).1 (variant 0 (variables plan m .upper 0)) at u
  rw [GeneralNominalVersionedExpressionFrame236.variable_value] at l u
  change Equivalent (m lower).1 (variant 0 (m (low plan)).1) at l
  change Equivalent (m upper).1 (variant 0 (m (high plan)).1) at u
  exact ⟨equivalent_trans l ⟨(common_variant_iff ..).mpr pairs.1.1,
      (common_variant_iff ..).mpr pairs.1.2⟩,
    equivalent_trans u ⟨(common_variant_iff ..).mpr pairs.2.1,
      (common_variant_iff ..).mpr pairs.2.2⟩⟩

theorem equal : Equal pointFirst lower upper := by
  intro m full
  have pair := ports m (installed_held m full).2.1
  exact equivalent_trans pair.1 ⟨pair.2.2,pair.2.1⟩

theorem old_not_equal : ¬ Equal installed lower upper := by
  intro claim
  have pair := claim GeneralDictionaryCompoundVersionedModel238.extended
    GeneralDictionaryCompoundStep238.installed_model
  rw [GeneralDictionaryCompoundVersionedPacket238.child_value 0,
    GeneralDictionaryCompoundVersionedPacket238.child_value 1] at pair
  change Equivalent (variant 0 GeneralDictionaryOptionalOutput229.value)
    (variant 0 .emptyRecord) at pair
  exact GeneralDictionaryOptionalOutput229.not_width
    ⟨(common_variant_iff ..).mp pair.1,(common_variant_iff ..).mp pair.2⟩

theorem lower_reserved : lower ∈ afterSnap.reserved := by decide +kernel
theorem upper_reserved : upper ∈ afterSnap.reserved := by decide +kernel
theorem lower_not_read : lower ∉ GeneralDictionaryDefaultRawSupport213.sources afterSnap := by decide +kernel

end Yulang.GeneralMixedCompoundPointPorts308
