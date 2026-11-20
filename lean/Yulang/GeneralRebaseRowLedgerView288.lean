import Yulang.GeneralRebaseRowLedgerStep288

/-! The two-fact output projection does not detect the newly enabled
old refresh on the static ledger extension. In that comparison the
projection is already exhausted, on both sides of the concrete refresh. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralRebaseRowLedgerView288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLedgerStep288 (refreshed)
open GeneralRebaseRowSemanticMark287 (target)
open GeneralRebaseStep258 (done write)
open GeneralRebaseRowProjection287 (support owner output observe after_observe)
open GeneralRebaseLiveProjection264 (liveFacts project)
open GeneralRebaseMultiSelection263 (ofPlan)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State Models)

theorem supplemented_observe : observe supplemented = observe (after true) := by
  have inclusion : liveFacts (after true) ⊆ liveFacts supplemented :=
    GeneralRebaseLiveProjection264.monotone _ _ _ _ (fun _ member => List.mem_cons_of_mem _ member)
      (fun _ _ _ member => member)
  unfold observe
  rw [GeneralRebaseLiveProjection264.rescan _ _ _ _ inclusion]
  change write (observe (after true)) (liveFacts supplemented) = observe (after true)
  rw [after_observe true]
  exact GeneralRebaseStep258.state_ext _ _ rfl

theorem refreshed_observe : observe refreshed = observe supplemented := by
  apply GeneralRebaseLiveProjection264.project_same
  intro fact
  apply GeneralRebaseLiveProjection264.same_members
  · intro plan
    rfl
  · intro p _ out
    simp only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq]
    exact GeneralNominalVersionedRefresh232.refresh_requests supplemented (target true)

theorem no_enabledness_from_output :
    ¬ ∃ recognizer : GeneralRebaseStep258.State support → Prop,
      ∀ s : State roles, recognizer (observe s) ↔ ∃ next, Step (registry true) root s next := by
  rintro ⟨r,exactly⟩
  have enabled := (exactly supplemented).mpr ⟨_,GeneralRebaseRowLedgerStep288.real_refresh_at_hypothetical_state⟩
  rw [supplemented_observe] at enabled
  obtain ⟨next,step⟩ := (exactly (after true)).mp enabled
  exact GeneralRebaseRowClosure287.no_step true next step

theorem raw_refresh_as_projection_stutter :
    Step (registry true) root supplemented refreshed ∧
      observe supplemented = done support ∧ observe refreshed = done support ∧
      GeneralRebaseSourceStepDriver270.next support (observe supplemented) = none ∧
      (∀ m, Models refreshed m ↔ Models (after true) m) := by
  refine ⟨GeneralRebaseRowLedgerStep288.real_refresh_at_hypothetical_state,
    supplemented_observe.trans (after_observe true),
    refreshed_observe.trans (supplemented_observe.trans (after_observe true)),?_,
    GeneralRebaseRowLedgerStep288.refreshed_model_eq⟩
  rw [supplemented_observe]
  exact GeneralRebaseRowProjection287.driver_after true

end Yulang.GeneralRebaseRowLedgerView288
