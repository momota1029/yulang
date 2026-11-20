import Yulang.GeneralRebaseRowLeafDecisionGuard288

/-! A source-supported known root and an empty nested read footprint are
not enough to settle a child: the deferred row pattern still stays pending. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseRowDeferredDecisionGuard288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after after_model)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralNominalVersionedSupport233 (ReadyAt DecisionGuard)
open GeneralNominalSupport (Head)
open GeneralNominalRecursiveInspection (Test)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem direct_read : ReadyAt (after false) 0 := by
  let observation : GeneralCanonicalObservations.Observation := .nominal raw.base (0 : Fin 3) inner
  have recorded : Head raw 0 (.nominal 6 1) observation :=
    GeneralNominalSupport.Head.nominal (snapshot := raw) (0 : Fin 3) inner rfl
  have currentRead : Head (current false).state 0 (.nominal 6 1) observation :=
    GeneralNominalSupport.Head.nominal (snapshot := (current false).state) (0 : Fin 3) inner rfl
  exact ⟨_,_,currentRead,GeneralNominalVersionedSupport233.source_head recorded⟩

theorem deferred_query : GeneralNominalInspection.queries (current false).state
    (current false).interpretation destructing = [.deferred (.app 6 [.var 0])] := by
  rw [GeneralNominalInspection.queries]
  change [GeneralNominalInspection.translate (current false).state.constructors
    (current false).interpretation (.app 6 [.var 0])] = _
  rw [GeneralRebaseRowHeadBoundary287.translates_deferred
    (layout := ⟨[.row],6⟩) rfl (List.mem_singleton_self _) rfl]

theorem known_but_deferred : DecisionGuard (registry false) (after false) (child false) := by
  constructor
  · intro slot
    exact direct_read
  · intro d visible role bounds _ slot read
    cases GeneralRebaseRowLocal287.child_at_role false d visible role
    change slot ∈ GeneralNominalSupport.readsMany (current false).state
      (GeneralNominalInspection.queries (current false).state (current false).interpretation destructing) bounds at read
    rw [deferred_query] at read
    cases bounds <;> simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads] at read

theorem not_a_settlement_criterion :
    DecisionGuard (registry false) (after false) (child false) ∧
    GeneralNominalVersionedCandidates231.InspectionPending (registry false) (current false) (child false) ∧
    (∃ m, Models (after false) m) ∧
    (∀ m p, ¬ Evidence (registry false) (after false).core m (child false) p) :=
  ⟨known_but_deferred,GeneralRebaseRowGeneratedChild287.pending_actual,⟨_,after_model false Common.rowEmpty⟩,
    GeneralRebaseRowGeneratedChild287.no_child_evidence⟩

end Yulang.GeneralRebaseRowDeferredDecisionGuard288
