import Yulang.GeneralDictionaryRecorded168Relocation
import Yulang.GeneralDictionaryCapturedTree168Transport

/-! The observed captured producer is replayed from its actual SourceFormed
journal, not from an assumed old or new dictionary. Its scalar refresh is not
required to be an ordinary-context extension. -/
namespace Yulang.GeneralDictionaryCapturedJournal168
open GeneralNominalSaturationState
open GeneralDictionaryRecorded168Relocation
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedProducer
open GeneralDictionarySharedCapturedFinalProducer GeneralDictionarySharedCapturedResumption
open GeneralDictionarySource168Transport

 theorem relocation : Relocates registry observed candidate :=
  ⟨fun slot => slot,actual_sources,actual_seed,GeneralDictionaryCapturedTree168Transport.locality⟩

 theorem journal_tree : RelocatedTree registry observed producer (.node declaration.id []) := by
  apply RelocatedTree.node candidate producer_recorded relocation
  rw [GeneralDictionarySharedCapturedProducerEvidence.terminal]
  exact .nil

 theorem current_dictionary (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models observed.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry observed.current.context model
      producer (.node declaration.id []) :=
  current_evidence observed_formed journal_tree model valid

 theorem nonvacuous_journal_replay :
    GeneralNominalSharedSteps.SourceFormed registry root observed ∧
    RelocatedTree registry observed producer (.node declaration.id []) ∧
    ∃ model, Models observed.current model ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry observed.current.context model
        producer (.node declaration.id []) :=
  ⟨observed_formed,journal_tree,GeneralDictionarySharedCapturedModel.model,inhabited,
    current_dictionary _ inhabited⟩
end Yulang.GeneralDictionaryCapturedJournal168
