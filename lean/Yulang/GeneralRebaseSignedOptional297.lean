import Yulang.GeneralRebaseSignedObserver297
import Yulang.GeneralDictionaryVersionedInitialStep233

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSignedOptional297
open GeneralDictionaryVersionedInitialFrame233 (before effect installed class_effects installation_models)
open GeneralDictionaryVersionedInitialStep233 (old_model_initial no_packet)
open GeneralDictionaryVersionedInitialModel233 (extended)
open GeneralDictionaryOptionalInstall229 (plan model)
open GeneralDictionaryOptionalInitial229 (registry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseSignedModels297 (Sign Test)
open GeneralRebaseInstallChecks267 (edgesRecorded)

theorem negative : Test before plan .reject model :=
  ⟨old_model_initial,fun h => no_packet h.1⟩

theorem positive : Test before plan .pass extended :=
  ⟨installation_models.1,installation_models.2.1,class_effects⟩

theorem no_new_edge : edgesRecorded before.core.erased.current plan = true := by decide +kernel

theorem structural_gate_empty :
    GeneralRebaseNoveltyProbe267.novel before (fun _ => false) plan = false := by
  unfold GeneralRebaseNoveltyProbe267.novel
  rw [no_new_edge]
  rfl

theorem semantically_enabled :
    ¬ GeneralRebaseInstallChecks267.semanticCommitted before plan ∧
    ∃ m, Test before plan .pass m :=
  ⟨(GeneralRebaseSignedModels297.reject_exact before plan).mp ⟨model,negative⟩,⟨extended,positive⟩⟩

theorem mixed_raw_actual :
    GeneralNominalVersionedMixedKernel234.Step registry root before installed :=
  GeneralNominalVersionedMixedKernel234.old_step GeneralDictionaryVersionedInitialStep233.step

end Yulang.GeneralRebaseSignedOptional297
