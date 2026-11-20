import Yulang.GeneralRebaseWatchedEvidenceAt284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseDisplayEvidenceWatch284
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseCompiledDisplay277 (after compiled)
open GeneralRebaseDisplayWatch284 (family watch stored next_valid complete child_certificate)
open GeneralRebaseWatchedEvidenceAt284 (Coverage InScope CheckedEvidenceAt)
open GeneralRebaseWatchJoint284 (Complete)
open GeneralRebaseActualWatch284 (Cache)
open GeneralRebaseSliceEvidence283 (Evidence reads)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)

theorem child_witness (m : Assignment) (valid : Models after m) :
    Evidence family compiled after m displayChild (.node 3 []) :=
  GeneralDictionaryReadback.erased_evidence_node _ _ _ [] [] (child_certificate m valid) .nil

theorem coverage : Coverage watch registry after displayRoot := by
  constructor
  · intro focus data eligible m both
    have reached : Generated after.core.erased.current displayRoot focus :=
      eligible.elim (fun eq => eq.symm ▸ .root) id
    rcases GeneralRebaseCompiledEndpoint277.generates_only reached with rfl|rfl
    · have shape := GeneralRebaseCompiledPayload277.parent_shape _ data both.2
      subst data
      exact complete m both
    · have shape := GeneralRebaseCompiledPayload277.child_shape _ data both.2
      subst data
      exact ⟨family,fun {_} h => List.mem_append_right _ h,child_witness _ both.1⟩
  · intro focus key children scope selected child found
    have reached : Generated after.core.erased.current displayRoot focus :=
      scope.elim (fun eq => eq.symm ▸ .root) id
    exact Or.inr (GeneralRebaseCompiledEvidenceAt277.generatedChildren focus key children reached selected child found)

theorem evidence_at : CheckedEvidenceAt watch stored.kept registry after displayRoot := by
  have cache : Cache after watch stored.kept := ⟨next_valid.covers,next_valid.sorted⟩
  exact (GeneralRebaseWatchedEvidenceAt284.equivalent_at cache GeneralRebaseCompiledFixtures282.Display.reached
    (fun {_} h => List.mem_append_left _ (List.mem_append_right _ h)) coverage).mpr
    GeneralRebaseCompiledEvidenceAt277.evidenceAt

end Yulang.GeneralRebaseDisplayEvidenceWatch284
