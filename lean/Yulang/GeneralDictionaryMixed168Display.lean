import Yulang.GeneralDictionaryMixed168Tree
import Yulang.GeneralDictionaryOrdinary168Relocation
import Yulang.GeneralDictionarySharedSemanticSettlement

/-! A concrete strictly mixed certificate: the actual Shared Display packet
and a source-shaped Int leaf with no recorded terminal packet. The new generic
interpreter derives its dictionary; no source or target Evidence is assumed. -/
namespace Yulang.GeneralDictionaryMixed168Display
open GeneralNominalExamples GeneralDeclarations GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)
open GeneralDictionaryMixed168Tree
open GeneralDictionarySharedDisplayInstallation (after)
open GeneralNominalSharedExamples (packet)

def leaf_shape : GeneralDictionaryScalarLeaf.ScalarLeafShape after.current.context displayChild intDisplay :=
  GeneralDictionaryScalarLeaf.recursiveDisplayShape

theorem parent_relocates : GeneralDictionaryRecorded168Relocation.Relocates registry after (packet false) :=
  GeneralDictionaryOrdinary168Relocation.packet_relocates registry after (packet false)
    (GeneralDictionarySharedCurrentEvidence.private_extension (packet false) [])

theorem structural_tree : MixedTree registry after displayRoot (.node 1 [.node 3 []]) := by
  apply MixedTree.recorded (packet false) (List.mem_singleton_self _) parent_relocates
  rw [GeneralDictionarySharedDisplayInstallation.children]
  exact .cons (.scalar displayChild intDisplay (by simp) int_display_checked leaf_shape) .nil

theorem interpreted_dictionary (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model
      displayRoot (.node 1 [.node 3 []]) :=
  current_evidence GeneralDictionarySharedRecursiveExample.formed structural_tree model valid

/-- Mixed coverage is strictly stronger than packet-only finite-tree coverage,
without confusing semantic evidence with ledger settlement. -/
theorem mixed_not_recorded :
    MixedTree registry after displayRoot (.node 1 [.node 3 []]) ∧
    ¬ GeneralDictionarySharedRecordedTree.RecordedTree after.current displayRoot (.node 1 [.node 3 []]) :=
  ⟨structural_tree,GeneralDictionarySharedSemanticSettlement.no_recorded_tree _ _⟩

theorem nonvacuous_interpretation :
    GeneralNominalSharedSteps.SourceFormed registry displayRoot after ∧
    MixedTree registry after displayRoot (.node 1 [.node 3 []]) ∧
    ∃ model, Models after.current model ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model
        displayRoot (.node 1 [.node 3 []]) := by
  obtain ⟨model,valid⟩ := GeneralDictionarySharedDisplayInstallation.inhabited
  exact ⟨GeneralDictionarySharedRecursiveExample.formed,structural_tree,model,valid,
    interpreted_dictionary model valid⟩
end Yulang.GeneralDictionaryMixed168Display
