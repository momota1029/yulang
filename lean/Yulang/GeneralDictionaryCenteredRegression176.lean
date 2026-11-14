import Yulang.GeneralDictionaryCenteredCandidate176
import Yulang.GeneralDictionaryCenteredFlexible176
import Yulang.GeneralDictionaryCenteredLedger176
import Yulang.GeneralNominalCenteredSelectionCounterexample

/-! Regression on the integrated reachable premerge example. A candidate is
not silently promoted to an installable plan. The state is explicitly not
stable, and therefore is not a counterexample to the stable EvidenceNode law. -/
namespace Yulang.GeneralDictionaryCenteredRegression176
open GeneralDictionaryEarlyMergeScalarExample
open GeneralNominalCenteredSelectionCounterexample
open GeneralNominalExamples (displayRoot context)
open GeneralNominalCenteredSteps GeneralNominalCenters

theorem first_flexible : GeneralDictionaryCenteredFlexible176.Step registry displayRoot cstart cbefore :=
  ⟨displayRoot,.root,.install cplan [] enabled novel cguard⟩

theorem parent_current_instance (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models cbefore model) :
    GeneralDictionaryRecursiveEvidence.Instance registry cbefore.erased.current.context model
      packet.site.occurrence packet.declaration.id packet.children :=
  GeneralDictionaryCenteredFlexible176.initial_trace_instance (context true)
    (.tail .refl first_flexible) packet (List.mem_cons_self ..) model valid

theorem exact_ledger : GeneralDictionaryCenteredLedger176.ExactLedger cbefore :=
  GeneralDictionaryCenteredLedger176.reachable_exact ground_reachable

theorem selected_candidate_not_installable :
    ∃ plan : Plan GeneralDeclarationExamples.roles,
      GeneralDictionaryCenteredCandidate176.Candidate registry cbefore (child 10) 3 [] plan ∧
      ¬ GeneralNominalCenteredBoundary.Installable registry cbefore plan := by
  obtain ⟨plan,candidate⟩ := GeneralDictionaryCenteredCandidate176.reachable_candidate
    ground_reachable (Or.inr child_generated) (child_selected 10)
  exact ⟨plan,candidate,child_not_installable plan candidate.occurrence_eq⟩

theorem premerge_not_stable : ¬ Stable registry cbefore displayRoot := by
  intro stable
  obtain ⟨focus,generated,action⟩ := required_merge_step
  exact stable focus generated _ action

end Yulang.GeneralDictionaryCenteredRegression176
