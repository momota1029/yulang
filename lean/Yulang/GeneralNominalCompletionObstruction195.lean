import Yulang.GeneralNominalCurrentCompletion195
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

/-! The production premise cannot be discharged merely by stability and
selection at the frozen WF boundary. This is an existing schema limitation,
not a new claim of a contradiction in language semantics. -/
namespace Yulang.GeneralNominalCompletionObstruction195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalReuseCatalogue195
open GeneralNominalCurrentCompletion195
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadWFJoinLocal
open GeneralNominalCenteredHeadWFJoinCounterexample

/-- No current reusable witness exists for the actual multi-tag source: its
head frame has unknown materialization while RequestReady requires knownness. -/
theorem no_reusable (candidate : Plan roles) (same : candidate.packet.site.occurrence = root) :
    ¬ Reusable registry start candidate := by
  intro reuse
  have unknown := frame_unknown candidate (same ▸ reuse.1)
  have ready := reuse.2.1.2
  rw [unknown] at ready
  contradiction

theorem no_selected_completion : ¬ SelectedCompletion registry start root := by
  intro complete
  obtain ⟨candidate,same,reuse⟩ := complete root .root 37 children selected
  exact no_reusable candidate same reuse

/-- Existing reachable, inhabited, stable and selected source fails the
strictly structural completion contract. General EvidenceNode itself is not
refuted by this theorem. -/
theorem stable_selected_missing_completion :
    B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root start ∧
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root ∧
    GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 37 children) ∧
    (∃ model, GeneralNominalCenteredHeadStepEffects.Models start model) ∧
    ¬ SelectedCompletion registry start root := by
  refine ⟨reachable,stable,selected,?_,no_selected_completion⟩
  obtain ⟨model,valid,_⟩ := positive_baseline
  exact ⟨model,valid⟩
end Yulang.GeneralNominalCompletionObstruction195
