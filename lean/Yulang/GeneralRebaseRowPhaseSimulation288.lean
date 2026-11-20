import Yulang.GeneralRebaseRowLedgerPhase288

/-! Exact phase-level simulation only on the closed positive family.
An input state is still required to come with its provenance membership. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralRebaseRowPhaseSimulation288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowLedgerStep288 (refreshed real_refresh_at_hypothetical_state)
open GeneralRebaseRowLedgerFirst288 (only_output_refresh)
open GeneralRebaseRowLedgerPhase288
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRowProjection287 (observe after_observe support)
open GeneralRebaseRowLedgerView288 (supplemented_observe)

theorem forward {s t : State roles} (inFamily : Family s) (move : Step (registry true) root s t) :
    Family t ∧ next (phase s) = some (phase t) := by
  cases inFamily with
  | original => exact (GeneralRebaseRowClosure287.no_step true _ move).elim
  | guarded =>
    obtain ⟨ctx,⟨cert⟩,known,rfl⟩ := (only_output_refresh t).mp move
    exact ⟨.finished ctx cert known,by rw [guarded_phase,finished_phase cert known]; rfl⟩
  | finished ctx cert known =>
    exact (GeneralRebaseRowRefreshHalt288.no_step cert known _ move).elim

theorem backward {s : State roles} (inFamily : Family s) (p : Phase)
    (takes : next (phase s) = some p) :
    ∃ t, Step (registry true) root s t ∧ Family t ∧ phase t = p := by
  cases inFamily with
  | original => rw [original_phase] at takes; cases takes
  | guarded =>
    have proved := forward .guarded real_refresh_at_hypothetical_state
    exact ⟨refreshed,real_refresh_at_hypothetical_state,proved.1,Option.some.inj (proved.2.symm.trans takes)⟩
  | finished ctx cert known => rw [finished_phase cert known] at takes; cases takes

theorem exact_observer {s : State roles} (inFamily : Family s) (p : Phase) :
    next (phase s) = some p ↔ ∃ t, Step (registry true) root s t ∧ Family t ∧ phase t = p := by
  constructor
  · exact backward inFamily p
  · rintro ⟨t,move,_,equal⟩
    rw [← equal]
    exact (forward inFamily move).2

theorem all_models_same {s : State roles} (inFamily : Family s) (m : Assignment) :
    Models s m ↔ Models (after true) m := by
  cases inFamily with
  | original => rfl
  | guarded => exact models_eq m
  | finished ctx cert known =>
    exact GeneralRebaseRowLedgerFirst288.all_steps_preserve_models
      ((only_output_refresh _).mpr ⟨ctx,⟨cert⟩,known,rfl⟩) m

theorem all_output_views_same {s : State roles} (inFamily : Family s) :
    observe s = GeneralRebaseStep258.done support := by
  cases inFamily with
  | original => exact after_observe true
  | guarded => exact supplemented_observe.trans (after_observe true)
  | finished ctx cert known =>
    have equal : observe (GeneralNominalVersionedRefresh232.refresh supplemented ctx) = observe supplemented := by
      apply GeneralRebaseLiveProjection264.project_same
      intro fact
      apply GeneralRebaseLiveProjection264.same_members
      · intro p
        rfl
      · intro p _ out
        simp only [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq]
        exact GeneralNominalVersionedRefresh232.refresh_requests supplemented ctx
    exact equal.trans (supplemented_observe.trans (after_observe true))

theorem enabledness_requires_more_than_models_and_outputs :
    (∀ m, Models supplemented m ↔ Models (after true) m) ∧
    observe supplemented = observe (after true) ∧
    next (phase supplemented) = some .finished ∧
    next (phase (after true)) = none := by
  exact ⟨models_eq,supplemented_observe,by rw [guarded_phase]; rfl,by rw [original_phase]; rfl⟩

end Yulang.GeneralRebaseRowPhaseSimulation288
