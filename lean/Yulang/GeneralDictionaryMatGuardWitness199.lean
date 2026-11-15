import Yulang.GeneralDictionaryMatGuardObstruction199
import Yulang.GeneralNominalCenteredHeadMatStepRows

set_option backward.isDefEq.respectTransparency false

/-! A full total-materialization packet can hold even though the unchanged
recursive dictionary judgment rejects every model on its partial compiler guard.
This is a packet-to-instance obstruction, not a stable EvidenceNode counterexample. -/
namespace Yulang.GeneralDictionaryMatGuardWitness199
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralNominalCenteredHeadWFJoinSource hiding start reachable inhabited initial_source
open GeneralDictionaryMatGuardObstruction199 (start)
open GeneralNominalCommonBridge (Assignment)

/-- Reuse the existing corrected source extension, not a new translator claim. -/
theorem packet_inhabited : ∃ after : Assignment,
    GeneralNominalCenteredHeadMatStepPackets.Holds plan after := by
  obtain ⟨after,_,holds,_⟩ := GeneralNominalCenteredHeadMatStepRows.source_packet_extension
  exact ⟨after,holds⟩

theorem holds_without_instance : ∃ after : Assignment,
    GeneralNominalCenteredHeadMatStepPackets.Holds plan after ∧
      ∀ key children, ¬ GeneralDictionaryRecursiveEvidence.Instance registry context after root key children := by
  obtain ⟨after,holds⟩ := packet_inhabited
  exact ⟨after,holds,fun key children => GeneralDictionaryMatGuardObstruction199.no_instance after key children⟩

/-- The same assignment satisfies the real reachable initial journal and the
full prospective packet. Selection is for the actual I33 boundary. Stability
and evidence for the child are intentionally not asserted. -/
theorem reachable_selected_obstruction :
    B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root start ∧
    GeneralNominalCenteredHeadMatStepBoundary.Local registry start root (.selected 37 children) ∧
    ∃ after : Assignment,
      GeneralNominalCenteredHeadMatStepJournal.Models start after ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds plan after ∧
      ∀ key dictionaries, ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence
        registry start after root (.node key dictionaries) := by
  refine ⟨GeneralDictionaryMatGuardObstruction199.reachable,
    GeneralDictionaryMatGuardObstruction199.selected,?_⟩
  obtain ⟨after,holds⟩ := packet_inhabited
  exact ⟨after,(GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr holds.1,
    holds,fun key dictionaries => GeneralDictionaryMatGuardObstruction199.no_evidence after key dictionaries⟩

/-- Even a full total packet cannot imply the unchanged source instance. -/
theorem no_total_instance_conversion : ¬ (∀ after : Assignment,
    GeneralNominalCenteredHeadMatStepPackets.Holds plan after →
      GeneralDictionaryRecursiveEvidence.Instance registry context after root 37 children) := by
  intro convert
  obtain ⟨after,holds,missing⟩ := holds_without_instance
  exact missing 37 children (convert after holds)

end Yulang.GeneralDictionaryMatGuardWitness199
