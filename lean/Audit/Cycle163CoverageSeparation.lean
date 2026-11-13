import Yulang.GeneralDictionarySettledFiniteCoverageExample
import Yulang.GeneralDictionarySettlementExamples

/-! Cross-module acceptance regressions: semantic finite coverage must not be
mistaken for recorded settlement. These are audit-only assertions. -/
namespace Cycle163CoverageSeparation
open Yulang
open GeneralDictionarySupportRecursiveExample
open GeneralNominalExamples

theorem no_exact_upgrade : ¬ (GeneralDictionarySettledFiniteCoverage.Covered registry finish displayRoot →
    GeneralDictionaryRecordedSettlement.PacketCoverage registry finish displayRoot) := by
  intro upgrade
  exact GeneralDictionarySettlementExamples.Nonterminal.no_exact_coverage
    (upgrade GeneralDictionarySettledFiniteCoverageExample.covered)

theorem no_alias_upgrade : ¬ (GeneralDictionarySettledFiniteCoverage.Covered registry finish displayRoot →
    GeneralDictionaryAliasSettlement.AliasCoverage registry finish displayRoot) := by
  intro upgrade
  exact GeneralDictionarySettlementExamples.Nonterminal.no_alias_coverage
    (upgrade GeneralDictionarySettledFiniteCoverageExample.covered)

theorem inhabited_evidence_and_unsettled :
    GeneralNominalSaturationState.Models finish.current model ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry finish.current.context model displayRoot
      (.node 1 [.node 3 []]) ∧ GeneralNominalSettledSupport.Unsettled finish.current packet :=
  ⟨GeneralDictionarySettledFiniteCoverageExample.realized.2.1,
    GeneralDictionarySettledFiniteCoverageExample.realized.2.2,
    GeneralDictionarySettledRecursiveExample.packet_unsettled⟩
end Cycle163CoverageSeparation

#print axioms Cycle163CoverageSeparation.no_exact_upgrade
#print axioms Cycle163CoverageSeparation.no_alias_upgrade
#print axioms Cycle163CoverageSeparation.inhabited_evidence_and_unsettled
