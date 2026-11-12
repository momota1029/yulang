import Yulang.GeneralDictionaryScalarJournalMerge
import Yulang.GeneralDictionaryOutputMergeReachable

/-! The reachable parent's historical packet supplies both named scalar facts.
The equalities therefore hold at EVERY before-state model, despite the absence
of child declarations. This establishes equations, not child dictionaries. -/
namespace Yulang.GeneralDictionaryOutputMergeScalarFacts
open GeneralDictionaryOutputMergeReachable
open GeneralNominalSaturationState

theorem packet_present : packet ∈ before.current.packets := by
  exact List.mem_singleton_self _

theorem requests (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralDictionaryScalarJournalMerge.Requests packet (site n) (fun _ => .int) := by
  intro output present
  have eq := List.mem_singleton.mp present
  subst output
  change (.source (outputTarget n),.scalar .int) ∈
    (GeneralNominalRecursiveCandidates.generated registry (GeneralNominalExamples.context true)
      GeneralNominalExamples.displayRoot declaration checked [(0,0)]).tests
  rw [schema]
  rcases which with rfl | rfl <;> simp

theorem all_models_unchanged (model : GeneralNominalCommonBridge.Assignment) :
    Models finish.current model ↔ Models before.current model :=
  GeneralDictionaryScalarJournalMerge.models_merge_iff before.current (site 10) (site 11)
    packet packet packet_present packet_present (fun _ => .int)
    (requests 10 (Or.inl rfl)) (requests 11 (Or.inr rfl)) model

theorem all_models_evidence_unchanged (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models before.current model) (root : GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)
    (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model root payload ↔
    GeneralDictionaryRecursiveEvidence.Evidence registry before.current.context model root payload :=
  GeneralDictionaryScalarJournalMerge.evidence_merge_iff registry before.current (site 10) (site 11)
    packet packet packet_present packet_present (fun _ => .int)
    (requests 10 (Or.inl rfl)) (requests 11 (Or.inr rfl)) model valid root payload
end Yulang.GeneralDictionaryOutputMergeScalarFacts
