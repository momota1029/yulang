import Yulang.GeneralDictionaryOutputMergeRefreshEvidence

/-! The concrete refreshed journal's ordinary context now contains enough
constraints to recover its historical packet and site obligations. This is
context completeness, not full support stability or general V5 completeness. -/
namespace Yulang.GeneralDictionaryOutputMergeContextComplete
open GeneralDictionaryOutputMergeSuccess GeneralDictionaryOutputMergeRefresh
open GeneralNominalExamples (displayRoot context state listDescriptor)
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralNominalCommonBridge (Assignment)

/-- The new scalar output slots constrain every raw context assignment. -/
theorem raw_outputs (m : Assignment) (valid : GeneralNominalState.Models snapshot m)
    (n : Nat) (which : n = 10 ∨ n = 11) :
    CommonNominalFullCarrier.Equivalent (m (outputTarget n)).1 (.base .int) := by
  rcases which with rfl | rfl
  · exact valid.1.2.1 (2 : Fin 4) (.base .int) rfl
  · exact valid.1.2.1 (3 : Fin 4) (.base .int) rfl

theorem raw_original (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    GeneralNominalState.Models (state true) m := by
  have old := GeneralNominalRefinements.models refines m valid
  exact ⟨old.1,old.2.1,PresenceNormalForm.all_nil _ _⟩

/-- Reconstruct the actual historical packet, without assuming journal Models. -/
theorem raw_packet (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    packet.Holds m := by
  change BranchModels registry (context true) displayRoot declaration checked [(0,0)] m
  have privateModel := private_models (context true) registry displayRoot declaration 0 listDescriptor rfl 0 rfl
    (1,1) rfl query m (raw_original m valid)
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [schema]
  refine ⟨?_,by simp,by simp,by simp⟩
  intro test member
  rcases List.mem_cons.mp member with eq | member
  · rw [eq]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    exact raw_outputs m valid 10 (Or.inl rfl)
  · rw [List.mem_singleton.mp member]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed; cases observed
    exact raw_outputs m valid 11 (Or.inr rfl)

theorem context_complete : ContextComplete refreshed.current := by
  intro m valid
  have beforeValid : Models before.current m :=
    (GeneralNominalFeedbackSites.install_models (start displayRoot).current packet
      (GeneralNominalFeedbackSites.emitted packet) rfl m).mpr
      ⟨(initial_models ..).mpr (raw_original m valid),raw_packet m valid⟩
  have finishValid : Models finish.current m := by
    apply (merge_models before.current (site 10) (site 11) m).mpr
    refine ⟨beforeValid,?_⟩
    apply (GeneralNominalDemandMerging.output_atoms_exact (site 10) (site 11) m).mpr
    intro a one b two _
    have left := List.mem_singleton.mp one
    have right := List.mem_singleton.mp two
    subst a; subst b
    have l := raw_outputs m valid 10 (Or.inl rfl)
    have r := raw_outputs m valid 11 (Or.inr rfl)
    exact ⟨CommonNominalFullCarrier.subtype_trans l.1 r.2,
      CommonNominalFullCarrier.subtype_trans r.1 l.2⟩
  exact (models_exact m).mpr ((GeneralDictionaryOutputMergeFeedback.next_models m).mpr finishValid)
/-- The semantic/raw equality gap is closed for this concrete refreshed state,
for every source pair, without claiming other rules are disabled. -/
theorem equality_exact (first last : Nat) :
    GeneralNominalFeedbackK2.Equal refreshed.current first last ↔
      GeneralNominalFeedbackSteps.RawEqual refreshed.current first last :=
  ⟨fun equal m valid => equal m (context_complete m valid),
    fun equal m valid => equal m valid.1⟩

end Yulang.GeneralDictionaryOutputMergeContextComplete
