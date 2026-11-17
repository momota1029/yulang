import Yulang.GeneralDictionaryPointRevisions240
import Yulang.GeneralNominalPointKernel240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointReobserve240

theorem five {state : GeneralNominalVersionedJournal232.State GeneralDictionaryJournalRefinement228Source.roles}
 (source : state.core.erased.source.state = GeneralDictionaryJournalRefinement228Source.snapshot) (allocated reserved ordinary)
 (same : state.core.erased.current.context.state = GeneralDictionaryJournalRefinement228Reobserve.looseExtended allocated reserved ordinary)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence GeneralDictionaryJournalRefinement228Source.roles) :
 GeneralNominalPointKernel240.Step registry root state (GeneralDictionaryVersionedReobserve233.result allocated reserved ordinary same) := by
 exact ⟨root,.root,.administrative (.reobserve root _
 ⟨(GeneralDictionaryVersionedReobserve233.certificate source allocated reserved ordinary same).raw,
 GeneralNominalVersionedMixedObservations233.legacy_cache (GeneralDictionaryVersionedReobserve233.certificate source allocated reserved ordinary same).cache⟩
 (GeneralDictionaryJournalRefinement228Reobserve.revision_improves state.core.erased.current allocated reserved ordinary same)
 (GeneralDictionaryPointRevisions240.five state.core.erased.current allocated reserved ordinary same))⟩

theorem eight {state : GeneralNominalVersionedJournal232.State GeneralDictionaryGroundCopy218Source.roles}
 (source : state.core.erased.source.state = GeneralDictionaryGroundCopy218Source.snapshot) (allocated reserved ordinary)
 (same : state.core.erased.current.context.state = GeneralDictionaryGroundCopy218Reobserve.looseExtended allocated reserved ordinary)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence GeneralDictionaryGroundCopy218Source.roles) :
 GeneralNominalPointKernel240.Step registry root state (GeneralDictionaryMixedGround218Reobserve235.result allocated reserved ordinary same) := by
 exact ⟨root,.root,.administrative (.reobserve root _
 ⟨(GeneralDictionaryMixedGround218Reobserve235.certificate source allocated reserved ordinary same).raw,
 GeneralNominalVersionedMixedObservations233.legacy_cache (GeneralDictionaryMixedGround218Reobserve235.certificate source allocated reserved ordinary same).cache⟩
 (GeneralDictionaryGroundCopy218Reobserve.revision_improves state.core.erased.current allocated reserved ordinary same)
 (GeneralDictionaryPointRevisions240.eight state.core.erased.current allocated reserved ordinary same))⟩
end Yulang.GeneralDictionaryPointReobserve240
