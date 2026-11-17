import Yulang.GeneralDictionaryVersionedInstalled232
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedEvidence232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedInstall232
open GeneralNominalCommonBridge (Assignment)

theorem frame : GeneralNominalVersionedEvidence231.Frame registry installed.core root declaration.id
    GeneralDictionaryVersionedReconstruction231.replayed := by
  apply GeneralNominalVersionedFrameTransport232.frame_forward
    (before := GeneralDictionaryVersionedReconstruction231.reconstructed.core)
  · rfl
  · intro site member
    exact List.mem_append_left _ member
  · intro site member
    exact List.mem_append_left _ member
  · exact GeneralDictionaryVersionedFinal231.frame

theorem certificate (valid : Models installed m) :
    GeneralNominalVersionedEvidence231.Certificate registry installed.core m root declaration.id []
      GeneralDictionaryVersionedReconstruction231.replayed := by
  apply GeneralNominalVersionedFrameTransport232.certificate_forward
    (before := GeneralDictionaryVersionedReconstruction231.reconstructed.core)
  · rfl
  · exact fun _ h => List.mem_append_left _ h
  · exact fun _ h => List.mem_append_left _ h
  · exact GeneralDictionaryVersionedFinal231.certificate
      ((GeneralDictionaryVersionedReconstruction231.models_iff m).mpr ((models_iff m).mp valid))

theorem evidence (valid : Models installed m) :
    GeneralNominalVersionedEvidence231.Evidence registry installed.core m root (.node declaration.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,certificate valid⟩

theorem nonvacuous_installed_evidence :
    (∃ m, Models installed m) ∧ ∀ m, Models installed m →
      GeneralNominalVersionedEvidence231.Evidence registry installed.core m root (.node declaration.id []) :=
  ⟨inhabited,fun _ => evidence⟩

theorem every_old_model_extends (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m) :
    ∃ n, Models installed n ∧
      (∀ source ∈ GeneralDictionaryDefaultJournalSupport213.journalSources after, n source = m source) ∧
      GeneralNominalVersionedEvidence231.Evidence registry installed.core n root (.node declaration.id []) := by
  obtain ⟨n,model,kept⟩ := GeneralDictionaryVersionedInstalled232.every_model_extends valid
  exact ⟨n,model,kept,evidence model⟩

end Yulang.GeneralDictionaryVersionedEvidence232
