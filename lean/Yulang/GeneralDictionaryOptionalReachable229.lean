import Yulang.GeneralDictionaryOptionalStage229
import Yulang.GeneralDictionaryOptionalEnable229

namespace Yulang.GeneralDictionaryOptionalReachable229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229
open GeneralNominalCenteredHeadMatStepJournal

theorem path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step registry root) start stage :=
  .tail (.tail .refl GeneralDictionaryOptionalEnable229.step)
    GeneralDictionaryOptionalStage229.step

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

end Yulang.GeneralDictionaryOptionalReachable229
