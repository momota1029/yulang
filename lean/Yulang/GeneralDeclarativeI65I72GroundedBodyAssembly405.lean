import Yulang.GeneralDeclarativeI65I72GroundedNativeCenters405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Summarizes Tree)

/-- This is a readback of the C402 draft ledger constructor.
Every Event *already carries* the typed copy and the original atlas
lookup proof. Showing this is not a proof that the actual language's
source syntax produces such an Event. -/
theorem draft_ledger_already_has_the_original_B6_RHS405 {s q d} (ledger : Ledger s q d) :
    LedgerMeaning ExactSourceRhs ledger := by
  exact Ledger.rec
    (motive_1 := fun _ _ tree => LedgerMeaning ExactSourceRhs tree)
    (motive_2 := fun _ _ forest => LedgerForestMeaning ExactSourceRhs forest)
    (fun e _ later => by rw [LedgerMeaning]; exact ⟨candidate_keeps_original_B6_body405 e,later⟩)
    (by simp only [LedgerForestMeaning])
    (fun _ _ a b => by rw [LedgerForestMeaning]; exact ⟨a,b⟩)
    ledger

theorem exact_rhs_in_C402_provisional_signature405 : S13bbba := by
  intro s q d ledger model addresses meaning
  exact draft_ledger_already_has_the_original_B6_RHS405 ledger

/-- Actual-slice assembly exposing the one ledger containing the
original typed RHS, the checked priority of every chosen where
node, and the priority of the separate smaller support proofs.
The dictionary evidence uses that ledger in each fitting model. -/
theorem C402_completed_assembly_from_grounded_visits405 {s q d}
    (choice : Classifies completedChoiceSource404 s q (.selected d)) :
    ∃ (t : Tree) (ev : Option (Event s q)) (trace : SourceTrace completedChoiceSource404 s q t ev)
        (tree : I72.GeneralTree trace d) (ledger : Ledger s q d),
      Summarizes t (.selected d) ∧ TracePriority405 trace ∧ PrioritiesOnTree405 tree ∧
      CanonicalReplay tree ledger ∧ LedgerMeaning Addresses ledger ∧ LedgerMeaning ExactSourceRhs ledger ∧
      ∀ m, Fits s m →
        LedgerMeaning (LocalMeaning m) ledger ∧ LedgerMeaning (FixedTargets m) ledger ∧
          DictionaryEvidence s m q d := by
  obtain ⟨t,ev,trace,tree,ledger,summary,priority,align,addresses,meaning⟩ :=
    completed_choice_same_priority_and_ledger405 choice
  exact ⟨t,ev,trace,tree,ledger,summary,
    every_entered_selected_proof_keeps_grounded_priority405 actual_completed_choice_grounds_visits405 trace,
    priority,align,addresses,draft_ledger_already_has_the_original_B6_RHS405 ledger,meaning⟩

theorem C402_completed_scope_dictionary_sound_via_grounded_priorities405 :
    DictionarySound completedChoiceSource404 := by
  intro s q d chosen m fits
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,final⟩ := C402_completed_assembly_from_grounded_visits405 chosen
  exact (final m fits).2.2

end Yulang.GeneralDeclarativeI65.I72
