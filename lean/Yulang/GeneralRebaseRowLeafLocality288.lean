import Yulang.GeneralRebaseRowRefreshProjection288

/-! Local packet checks and ambient snapshot validity are distinct.
This exposes the particular conjunct that prevents a fresh source-only
certificate after the output is marked. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralRebaseRowLeafLocality288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLeafWitness288 (source_exact leaf)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowRefreshPackets288 (child_frame child_observed)
open GeneralRebaseRowRefreshEvidence288 (child_children)
open GeneralRebaseRowLeafLifetime288 (topOutput source_survives outside_snapshot)
open GeneralRebaseNonleafCommitted276 (result refinement interpretation)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedPlans231 (Inputs Outputs Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known)

variable {context : GeneralNominalCandidates.Context}

theorem original_current_child_reads_no_nested_heads :
    GeneralNominalSupport.readsMany GeneralRebaseRowWholeChild287.plan.packet.context.state
      (GeneralNominalInspection.queries GeneralRebaseRowWholeChild287.plan.packet.context.state
        GeneralRebaseRowWholeChild287.plan.packet.context.interpretation
        GeneralRebaseRowWholeChild287.plan.packet.declaration) GeneralRebaseRowWholeChild287.plan.packet.bounds = [] := by
  rw [show GeneralNominalInspection.queries _ _ _ = [.variables [0]] from GeneralRebaseRowWholeChild287.query]
  generalize GeneralRebaseRowWholeChild287.plan.packet.bounds = bounds
  cases bounds <;> simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads]

theorem same_leaf_local_checks (certificate : Refresh supplemented context)
    (m : Assignment) (source : SourceSlice (refresh supplemented context) m) :
    Inputs (result child_frame certificate) m ∧ Outputs (result child_frame certificate) m := by
  have initial : SourceSlice (after true) m := source
  have valid := leaf.sourcePacket m initial
  exact ⟨(GeneralRebaseNonleafRetarget276.inputs_iff _ (refinement child_frame certificate)
    (interpretation child_frame certificate) child_observed m).mpr valid.2.1,
    (GeneralRebaseNonleafRetarget276.outputs_iff _ (refinement child_frame certificate)
      (interpretation child_frame certificate) child_observed m).mpr valid.2.2⟩

theorem no_live_requests (_certificate : Refresh supplemented context) :
    GeneralNominalCenteredHeadOutputs.requests (refresh supplemented context).core (child true) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x seen
  have previous := (GeneralNominalVersionedRefresh232.refresh_requests supplemented context).mp seen
  have empty : GeneralNominalCenteredHeadOutputs.requests supplemented.core (child true) = [] :=
    GeneralRebaseRowWholeChild287.requests_empty
  rw [empty] at previous
  cases previous

theorem no_class_restrictions (certificate : Refresh supplemented context) (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects (refresh supplemented context).core
      (child true) (result child_frame certificate) m := by
  constructor <;> intro out present <;> rw [no_live_requests certificate] at present <;> cases present

theorem full_packet_iff_ambient_on_source (certificate : Refresh supplemented context)
    (m : Assignment) (source : SourceSlice (refresh supplemented context) m) :
    Holds (result child_frame certificate) m ↔ GeneralNominalState.Models context.state m :=
  ⟨And.left,fun ambient => ⟨ambient,same_leaf_local_checks certificate m source⟩⟩

theorem exact_obstruction (certificate : Refresh supplemented context)
    (known : Known context.state 2) :
    (∀ m, SourceSlice (refresh supplemented context) m →
      Inputs (result child_frame certificate) m ∧ Outputs (result child_frame certificate) m ∧
      GeneralNominalVersionedEffects231.ClassEffects (refresh supplemented context).core
        (child true) (result child_frame certificate) m) ∧
    (¬ Holds (result child_frame certificate) topOutput) ∧
    GeneralNominalVersionedFrame231.children (result child_frame certificate).packet = [] := by
  refine ⟨fun m src => ⟨(same_leaf_local_checks certificate m src).1,(same_leaf_local_checks certificate m src).2,
    no_class_restrictions certificate m⟩,?_,child_children certificate⟩
  rw [full_packet_iff_ambient_on_source certificate topOutput source_survives]
  exact outside_snapshot certificate known

end Yulang.GeneralRebaseRowLeafLocality288
