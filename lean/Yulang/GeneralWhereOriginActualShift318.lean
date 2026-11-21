import Yulang.GeneralWhereOriginFixture318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 42000000
namespace Yulang.GeneralWhereOriginActualShift318
open GeneralLiveCompoundRoot316 (plan)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (otherChild declaration)
open GeneralWhereVersionCase317 (expr lower upper)
open GeneralVersionedEndpointAddress315 (atCell Side footprint fields)
open GeneralNominalVersionedExpressionFrame236 (reads variableSource)
open GeneralNominalAggregateVersion231 (slot slot_eq_iff)
open GeneralDictionaryJournalRefinement228Source (snapshot root)

theorem oldBindings : plan.packet.bindings = [(0,4,2),(0,4,2)] :=
  GeneralDictionaryCompoundPacket238.bindings_exact

theorem newBindings : rootPlan.packet.bindings = [(0,2,2),(0,2,2)] := by
  let p := GeneralLiveCompoundCurrentRoot316.plan
  let a := GeneralLiveCompoundLeafHead316.packet
  open GeneralNominalVersionedInstallation231 (reserved atoms allocated) in
  change (GeneralNominalVersionedTransport231.extendedPlan (reserved a) (atoms a) (allocated a) p).packet.bindings = _
  exact (GeneralNominalVersionedTransport231.packet_bindings _ _ _ p.packet).trans
    GeneralLiveCompoundCurrentRoot316.bindings_exact

theorem old_lower_id : variableSource plan .lower 0 =
    slot snapshot.seed root.identity declaration.id 0 0 [(0,4,2),(0,4,2)] := by
  unfold variableSource
  have notOut : ¬ (0:Nat) ∈ plan.packet.declaration.outputNames := by decide +kernel
  rw [ite_eq_right notOut]
  change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ plan.packet.bindings).inputs 0).1 = _
  rw [oldBindings]
  rfl

theorem old_upper_id : variableSource plan .upper 0 =
    slot snapshot.seed root.identity declaration.id 1 0 [(0,4,2),(0,4,2)] := by
  unfold variableSource
  have notOut : ¬ (0:Nat) ∈ plan.packet.declaration.outputNames := by decide +kernel
  rw [ite_eq_right notOut]
  change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ plan.packet.bindings).inputs 0).2 = _
  rw [oldBindings]
  rfl

theorem new_lower_id : variableSource rootPlan .lower 0 =
    slot snapshot.seed root.identity declaration.id 0 0 [(0,2,2),(0,2,2)] := by
  unfold variableSource
  have notOut : ¬ (0:Nat) ∈ rootPlan.packet.declaration.outputNames := by decide +kernel
  rw [ite_eq_right notOut]
  change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ rootPlan.packet.bindings).inputs 0).1 = _
  rw [newBindings]
  rfl

theorem new_upper_id : variableSource rootPlan .upper 0 =
    slot snapshot.seed root.identity declaration.id 1 0 [(0,2,2),(0,2,2)] := by
  unfold variableSource
  have notOut : ¬ (0:Nat) ∈ rootPlan.packet.declaration.outputNames := by decide +kernel
  rw [ite_eq_right notOut]
  change ((GeneralNominalVersionedAllocation231.capture _ _ _ _ rootPlan.packet.bindings).inputs 0).2 = _
  rw [newBindings]
  rfl

theorem different_aggregate (purpose : Nat) :
    slot snapshot.seed root.identity declaration.id purpose 0 [(0,4,2),(0,4,2)] ≠
      slot snapshot.seed root.identity declaration.id purpose 0 [(0,2,2),(0,2,2)] := by
  intro h
  have found := (slot_eq_iff snapshot.seed root.identity declaration.id purpose 0).mp h
  have old : GeneralNominalAllocation.occurrences [(0,4,2),(0,4,2)] 0 = [(4,2),(4,2)] := by decide +kernel
  have new : GeneralNominalAllocation.occurrences [(0,2,2),(0,2,2)] 0 = [(2,2),(2,2)] := by decide +kernel
  rw [old,new] at found
  have bad : (4:Nat) = 2 := congrArg Prod.fst (List.head_eq_of_cons_eq found)
  cases bad

/-- The actual C316 double-capture change is not a mixed case: both
address footprints move, even though the upper operand is equivalent
in the two known models. Purpose tags rule out cross-polarity reuse. -/
theorem both_move :
    atCell plan .lower otherChild.id 0 expr ≠ lower ∧
    atCell plan .upper otherChild.id 0 expr ≠ upper := by
  constructor
  · intro eq
    have read := (fields (p := plan) (q := rootPlan) (e := expr) (f := expr) rfl eq).2.2.2.2.2
    change [variableSource plan .lower 0] = [variableSource rootPlan .lower 0] at read
    have ids := List.head_eq_of_cons_eq read
    rw [old_lower_id,new_lower_id] at ids
    exact different_aggregate 0 ids
  · intro eq
    have read := (fields (p := plan) (q := rootPlan) (e := expr) (f := expr) rfl eq).2.2.2.2.2
    change [variableSource plan .upper 0] = [variableSource rootPlan .upper 0] at read
    have ids := List.head_eq_of_cons_eq read
    rw [old_upper_id,new_upper_id] at ids
    exact different_aggregate 1 ids

end Yulang.GeneralWhereOriginActualShift318
