import Yulang.GeneralDictionaryJournalRefinement228Stage
import Yulang.GeneralDictionaryJournalRefinement228Enable

namespace Yulang.GeneralDictionaryJournalRefinement228Reachable
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryJournalRefinement228Initial
open GeneralDictionaryJournalRefinement228Install
open GeneralDictionaryJournalRefinement228Stage
open GeneralNominalCenteredHeadMatStepJournal

theorem path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step registry root) start stage :=
  .tail (.tail .refl GeneralDictionaryJournalRefinement228Enable.step)
    GeneralDictionaryJournalRefinement228Stage.step

theorem reachable : B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles)
    sourceRegistry root stage := ⟨start,initial,path⟩

/-- Initial-source reachability and a full surviving journal model do not by
 themselves imply instance extraction. Stable and selected Local are deliberately
 absent, so this is not a refutation of EvidenceNode. -/
theorem reachable_obstruction :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root stage ∧
    Models stage model ∧
    ¬ GeneralDictionaryTotalEvidence206.Instance registry stage.core model root key children :=
  ⟨reachable,stage_model,no_instance⟩

end Yulang.GeneralDictionaryJournalRefinement228Reachable
