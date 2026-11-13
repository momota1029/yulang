import Yulang.GeneralDictionarySharedRecursiveExample
import Yulang.GeneralDictionarySharedRecordedTree
import Yulang.GeneralDictionarySettledRecursiveExample

/-! Certified-origin execution still distinguishes semantic recursive evidence
from finite recorded-packet settlement. The positive Display dictionary's source
Int leaf has no recorded terminal packet in this one-step journal. -/
namespace Yulang.GeneralDictionarySharedSemanticSettlement
open GeneralNominalExamples
open GeneralDeclarationExamples (roles)
open GeneralDeclarations GeneralNominalSaturationState
open GeneralNominalSupport GeneralSourceDictionaries
open GeneralNominalSharedExamples (packet)
open GeneralDictionarySharedDisplayInstallation (after)

theorem no_discharged (focus : Occurrence roles) : ¬ Discharged after.current focus := by
  apply GeneralDictionarySettledRecursiveExample.no_discharge_without_terminal_packet after.current
  intro recorded member
  change recorded ∈ [packet false] at member
  have same := List.mem_singleton.mp member
  subst recorded
  rw [GeneralDictionarySharedDisplayInstallation.children]
  simp

theorem parent_not_settled : ¬ GeneralNominalSettledSupport.PacketSettled after.current (packet false) := by
  intro settled
  exact no_discharged displayChild (settled.2 displayChild (by rw [GeneralDictionarySharedDisplayInstallation.children]; simp))

theorem no_recorded_tree (focus : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    ¬ GeneralDictionarySharedRecordedTree.RecordedTree after.current focus payload :=
  fun tree => no_discharged focus (GeneralDictionarySharedRecordedTree.discharged tree)

/-- Both the real source history and inhabited universal semantic dictionary
coexist with absence of a recorded tree and ledger settlement. -/
theorem semantic_evidence_not_ledger_completion :
    GeneralNominalSharedSteps.SourceFormed registry displayRoot after ∧
    (∃ model, Models after.current model) ∧
    (∀ model, Models after.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model displayRoot (.node 1 [.node 3 []])) ∧
    ¬ GeneralNominalSettledSupport.PacketSettled after.current (packet false) ∧
    ¬ GeneralDictionarySharedRecordedTree.RecordedTree after.current displayRoot (.node 1 [.node 3 []]) :=
  ⟨GeneralDictionarySharedRecursiveExample.formed,GeneralDictionarySharedDisplayInstallation.inhabited,
    GeneralDictionarySharedRecursiveExample.recursive_evidence,parent_not_settled,no_recorded_tree _ _⟩
end Yulang.GeneralDictionarySharedSemanticSettlement
