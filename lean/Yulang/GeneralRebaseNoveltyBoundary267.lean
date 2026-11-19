import Yulang.GeneralRebaseExecutableInstall267
import Yulang.GeneralDictionaryVersionedInitialStep233

set_option maxRecDepth 8192
namespace Yulang.GeneralRebaseNoveltyBoundary267
open GeneralDictionaryVersionedInitialFrame233 (before installed)
open GeneralDictionaryOptionalInstall229 (plan)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry)
open GeneralRebaseInstallChecks267 (edgesRecorded)

/-- A real install without a missing edge: returning no structural candidate
cannot be interpreted as source quiescence. The novelty is semantic. -/
theorem actual_semantic_novelty :
 edgesRecorded before.core.erased.current plan = true ∧
 ¬ GeneralRebaseInstallChecks267.semanticCommitted before plan ∧
 GeneralNominalVersionedMixedKernel234.Step registry root before installed := by
 have recorded : edgesRecorded before.core.erased.current plan = true := by decide +kernel
 have novel := GeneralDictionaryVersionedInitialStep233.not_committed
 refine ⟨recorded,?_,GeneralNominalVersionedMixedKernel234.old_step GeneralDictionaryVersionedInitialStep233.step⟩
 intro semantic
 exact novel ((GeneralRebaseInstallChecks267.committed_exact ..).mpr ⟨semantic,recorded⟩)

theorem structural_selector_omits_this_plan (probe : GeneralNominalCenters.Plan roles → Option Bool)
 (entries : List (GeneralNominalCenters.Plan roles)) :
 GeneralRebaseExecutableInstall267.select before probe entries ≠ some plan := by
 intro selected
 obtain ⟨_,_,_,_,_,missing⟩ := GeneralRebaseExecutableInstall267.selection_parts before probe entries selected
 simp [actual_semantic_novelty.1] at missing

end Yulang.GeneralRebaseNoveltyBoundary267
