import Yulang.GeneralDepthTwoMachine300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDepthTwoRootAvailability300
open GeneralGeneratedNestedSource299 (initial root)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralGeneratedDictionaryScope299 (all_left)
open GeneralDepthTwoMachine300 (Phase raw)

theorem initial_middle_absent (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry initial m middle d := by
  intro got
  have seen : PayloadEvidence (Instance compiled initial.core m) middle d :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr got
  cases seen with
  | node instance' _ =>
    obtain ⟨plan,valid⟩ := instance'
    have location := List.mem_singleton.mp valid.frame.raw_recorded
    have same : root = middle := by rw [← valid.frame.occurrence_eq,location]; rfl
    exact GeneralGeneratedNestedPredictions299.different_occurrences.1
      (congrArg (fun o => o.identity) same)

theorem initial_root_absent (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry initial m root d := by
  intro got
  have seen : PayloadEvidence (Instance compiled initial.core m) root d :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr got
  cases seen with
  | node instance' proofs =>
    obtain ⟨p,cert⟩ := instance'
    cases GeneralDepthTwoOnlyFirst300.phase_frame cert.frame
    have branches := cert.children_eq.trans GeneralGeneratedNestedPredictions299.parent_children
    rw [branches] at proofs
    obtain ⟨d,proof⟩ := all_left proofs middle (List.mem_singleton_self _)
    exact initial_middle_absent m d ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mp proof)

theorem after_root_absent (m : Assignment) (d : Payload) :
    ¬ (boundary roles).Evidence registry after m root d := by
  intro got
  have seen : PayloadEvidence (Instance compiled after.core m) root d :=
    (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr got
  cases seen with
  | node instance' proofs =>
    obtain ⟨p,cert⟩ := instance'
    cases GeneralDepthTwoOnlySecond300.root_frame cert.frame
    have branches := cert.children_eq.trans
      ((GeneralNominalVersionedInstallation231.replay_children _).trans
        GeneralGeneratedNestedPredictions299.parent_children)
    rw [branches] at proofs
    obtain ⟨d,proof⟩ := all_left proofs middle (List.mem_singleton_self _)
    exact GeneralDepthTwoPhaseCut300.no_middle_evidence m d
      ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mp proof)

theorem exact_availability (p : Phase) (m : Assignment) (valid : Models (raw p) m) :
    (∃ d, (boundary roles).Evidence registry (raw p) m root d) ↔ p = .done := by
  cases p
  · exact ⟨fun ⟨d,proof⟩ => False.elim (initial_root_absent m d proof),by intro h; cases h⟩
  · exact ⟨fun ⟨d,proof⟩ => False.elim (after_root_absent m d proof),by intro h; cases h⟩
  · exact ⟨fun _ => rfl,fun _ => ⟨_,GeneralDepthTwoEvidence300.root_evidence m valid⟩⟩

end Yulang.GeneralDepthTwoRootAvailability300
