import Yulang.GeneralWherePhysicalPast319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 23000000
namespace Yulang.GeneralWherePhysicalOldValues319
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (old_bindings)
open GeneralDictionaryJournalRefinement228Source (snapshot root foo)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralNominalCenters (fresh)
open GeneralNominalRecursiveInspection (Observes)
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

theorem old_capture (n : Nat) (known : n = 0 ∨ n = 1) : (capture older).inputs n = (4,2) := by
  change (GeneralNominalVersionedAllocation231.capture _ _ _ _ older.bindings).inputs n = _
  rw [old_bindings]
  rcases known with rfl|rfl <;> rfl

theorem old_binder (n : Nat) (known : n = 0 ∨ n = 1) :
    binder oldPlan n = fresh snapshot.seed root.identity declaration.id 8 n 0 := by
  have bounds := old_capture n known
  unfold binder
  change (if n ∈ declaration.outputNames then _ else if ((capture older).inputs n).1 = ((capture older).inputs n).2
    then _ else _) = _
  rw [bounds]
  have absent : n ∉ declaration.outputNames := by intro h; cases h
  simp only [absent,ite_false,show (4:Nat) ≠ 2 from by decide]
  rfl

abbrev bind (n : Nat) := fresh snapshot.seed root.identity declaration.id 8 n 0

private theorem bind_zero_value : (w (bind 0)).1 = .emptyRecord := by
  have two (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  have three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  change (GeneralDictionaryCompoundPointModel238.extended (bind 0)).1 = _
  rw [GeneralDictionaryCompoundPointModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i eq; rcases two i with rfl|rfl <;> exact (by decide +kernel : _ ≠ _) eq),
    GeneralDictionaryCompoundVersionedModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i eq; rcases two i with rfl|rfl <;> exact (by decide +kernel : _ ≠ _) eq)]
  change (GeneralDictionaryCompoundModel238.extended (bind 0)).1 = _
  rw [GeneralDictionaryCompoundModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i eq; rcases three i with rfl|rfl|rfl <;> exact (by decide +kernel : _ ≠ _) eq)]
  unfold GeneralDictionaryCompoundPacket238.model
  simp [show ¬ bind 0 ≤ 4 from by decide +kernel,
    show bind 0 ≠ GeneralDictionaryCompoundPacket238.lo from by decide +kernel]

private theorem bind_one_value : (w (bind 1)).1 = .emptyRecord := by
  have two (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  have three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  change (GeneralDictionaryCompoundPointModel238.extended (bind 1)).1 = _
  rw [GeneralDictionaryCompoundPointModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i eq; rcases two i with rfl|rfl <;> exact (by decide +kernel : _ ≠ _) eq),
    GeneralDictionaryCompoundVersionedModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i eq; rcases two i with rfl|rfl <;> exact (by decide +kernel : _ ≠ _) eq)]
  change (GeneralDictionaryCompoundModel238.extended (bind 1)).1 = _
  rw [GeneralDictionaryCompoundModel238.extended,
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (by intro i eq; rcases three i with rfl|rfl|rfl <;> exact (by decide +kernel : _ ≠ _) eq)]
  unfold GeneralDictionaryCompoundPacket238.model
  simp [show ¬ bind 1 ≤ 4 from by decide +kernel,
    show bind 1 ≠ GeneralDictionaryCompoundPacket238.lo from by decide +kernel]

theorem binder_value (n : Nat) (known : n = 0 ∨ n = 1) :
    (w (binder oldPlan n)).1 = .emptyRecord := by
  rw [old_binder n known]
  rcases known with rfl|rfl
  · exact bind_zero_value
  · exact bind_one_value

theorem baseline_raw : GeneralNominalState.Models snapshot w := by
  have prior := GeneralLiveCompoundLeafProof316.valid.2.1 GeneralLiveCompoundRoot316.plan List.mem_cons_self
  exact ((GeneralNominalVersionedPlans231.private_models_iff ..).mp
    (GeneralNominalVersionedPlans231.head_models prior).1).1

theorem old_head : GeneralNominalVersionedPlans231.HeadModels older w := by
  have prior := GeneralLiveCompoundLeafProof316.valid.2.1 GeneralLiveCompoundRoot316.plan List.mem_cons_self
  exact GeneralWhereOriginSingleHead318.old_head w (GeneralNominalVersionedPlans231.head_models prior)

theorem head_value : Equivalent (w 0).1 foo :=
  GeneralDictionaryJournalRefinement228Source.root_fixed w baseline_raw

theorem width_value : Equivalent (w 2).1 .emptyRecord :=
  GeneralDictionaryJournalRefinement228Source.width_two w baseline_raw

theorem bounded (n : Nat) (known : n = 0 ∨ n = 1) :
    GeneralNominalCaptureMerges.Fits w ((capture older).inputs n) (w (binder oldPlan n)).1 := by
  rw [old_capture n known,binder_value n known]
  exact ⟨GeneralDictionaryJournalRefinement228Source.lower_width w baseline_raw,width_value.2⟩

end Yulang.GeneralWherePhysicalOldValues319
