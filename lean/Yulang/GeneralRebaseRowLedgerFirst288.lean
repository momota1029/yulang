import Yulang.GeneralRebaseRowLedgerView288

/-! For the hypothetical ledger only, the first actual step is exactly a
certified refresh of output coordinate 2. This is not general reachability. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowLedgerFirst288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan)
open GeneralRebaseRowParentFrame287 (after effect after_model)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowLedger288 (supplemented unknown_output models_eq)
open GeneralRebaseRowLedgerStep288 (listed_output)
open GeneralRebaseRowClosure287 (scope only_child_plan)
open GeneralRebaseRowParentEvidence287 (raw_sites centers only_root_plan roles_distinct)
open GeneralRebaseRowAdministrative287 (already_known equality_is_reflexive point_closed)
open GeneralNominalVersionedMixedKernel234 (Step Committed)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known)

theorem committed_forward {p : GeneralNominalCenters.Plan roles}
    (old : Committed (after true) p) : Committed supplemented p :=
  ⟨fun m valid => old.1 m ((models_eq m).mp valid),old.2⟩

theorem cannot_certify_private {context : GeneralNominalCandidates.Context}
    (certificate : Refresh supplemented context) (n : Nat) (high : 2 < n) :
    ¬ Known context.state n := by
  intro known
  let witness := GeneralRebaseRowTrustedBoundary287.putTop (model Common.rowEmpty) n
  have valid : Models (after true) witness :=
    (GeneralRebaseRowParentFrame287.after_exact true witness).mpr
      ((GeneralRebaseRowAdministrative287.output_elsewhere (model Common.rowEmpty) high).mpr
        ((GeneralRebaseRowParentFrame287.after_exact true _).mp (after_model true Common.rowEmpty)))
  obtain ⟨test,obs,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have stored := GeneralNominalVersionedMixedObservations233.cache_sound certificate.cache
    (GeneralNominalSupport.head_recorded head) ((models_eq witness).mpr valid)
  have checked := GeneralDictionaryGroundCopy218Refresh.head_holds head stored
  change test.Holds (if n = n then .top else (model Common.rowEmpty n).1) at checked
  rw [ite_eq_left rfl] at checked
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test checked

theorem refresh_source {context : GeneralNominalCandidates.Context}
    (certificate : Refresh supplemented context) (n : Nat)
    (unknown : ¬ Known (current true).state n) (new : Known context.state n) : n = 2 := by
  by_cases small : n ≤ 1
  · exact (unknown (already_known true _ small)).elim
  · by_cases high : 2 < n
    · exact (cannot_certify_private certificate n high new).elim
    · omega

def IsOutputRefresh (next : State roles) : Prop :=
  ∃ context, Nonempty (Refresh supplemented context) ∧ Known context.state 2 ∧
    next = GeneralNominalVersionedRefresh232.refresh supplemented context

theorem only_output_refresh (next : State roles) :
    Step (registry true) root supplemented next ↔ IsOutputRefresh next := by
  constructor
  · rintro ⟨focus,generated,chosen⟩
    have visible := scope true generated
    cases chosen with
    | administrative action =>
      cases action with
      | enqueue _ absent =>
        rcases visible with rfl | rfl
        · exact (absent _ ((raw_sites true).symm ▸ List.mem_cons_self) rfl).elim
        · exact (absent _ (GeneralRebaseRowGeneratedChild287.raw_child true) rfl).elim
      | refresh context certificate n _ old new =>
        cases refresh_source certificate n old new
        exact ⟨context,⟨certificate⟩,new,rfl⟩
      | equate n k _ _ same novel =>
        have sameId := equality_is_reflexive true n k (fun m valid => same m ((models_eq m).mpr valid))
        subst k
        exact (novel (fun m _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩)).elim
      | reobserve revision _ improves =>
        exact (GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed true) revision improves).elim
    | refresh _ context certificate n _ old new =>
      cases refresh_source certificate n old new
      exact ⟨context,⟨certificate⟩,new,rfl⟩
    | install candidate certificate novel =>
      have frame := candidate.frame
      rw [certificate.registry_eq,certificate.snapshot_eq] at frame
      rcases visible with atRoot | atChild
      · rw [atRoot] at frame
        have exactPlan := only_root_plan true _ (after_model true Common.rowEmpty) frame
        rw [exactPlan] at novel
        exact (novel (committed_forward (GeneralNominalVersionedCommitted232.replay_committed before (effect true)))).elim
      · rw [atChild] at frame
        rw [only_child_plan frame] at novel
        exact (novel (committed_forward GeneralRebaseRowWholeChild287.already_committed)).elim
    | merge first last one two same novel =>
      change first ∈ (after true).core.sites at one
      change last ∈ (after true).core.sites at two
      rw [centers] at one two
      simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
      rcases one with rfl|rfl <;> rcases two with rfl|rfl
      · exact (novel (.refl _)).elim
      · exact (roles_distinct true same.1).elim
      · exact (roles_distinct true same.1.symm).elim
      · exact (novel (.refl _)).elim
  · rintro ⟨context,⟨certificate⟩,new,rfl⟩
    exact ⟨root,.root,.refresh root context certificate 2 listed_output (unknown_output true) new⟩

theorem all_steps_preserve_models {next : State roles}
    (step : Step (registry true) root supplemented next) (m : Assignment) :
    Models next m ↔ Models (after true) m := by
  obtain ⟨context,⟨cert⟩,_,rfl⟩ := (only_output_refresh next).mp step
  exact (GeneralNominalVersionedMixedObservations233.refresh_models cert).trans (models_eq m)

end Yulang.GeneralRebaseRowLedgerFirst288
