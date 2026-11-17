import Yulang.GeneralNominalPointRevision240
import Yulang.GeneralDictionaryVersionedReobserve233
import Yulang.GeneralDictionaryMixedGround218Reobserve235
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointRevisions240
open GeneralNominalReobservationSteps

theorem five (prior : GeneralNominalSaturationState.State GeneralDictionaryJournalRefinement228Source.roles) (allocated reserved ordinary)
 (same : prior.context.state = GeneralDictionaryJournalRefinement228Reobserve.looseExtended allocated reserved ordinary) :
 GeneralNominalPointRevision240.Preserves (GeneralDictionaryJournalRefinement228Reobserve.revisionFor prior allocated reserved ordinary same) := by
 rcases prior with ⟨⟨data,interpretation⟩,packets,sites,edges,aliases⟩
 dsimp only at same
 subst data
 intro slot descriptor found point
 change (if slot = 0 then some GeneralDictionaryJournalRefinement228Reobserve.loose else if slot = 1 then some GeneralDictionaryJournalRefinement228Reobserve.exactCopy else none) = some descriptor at found
 change (if slot = 0 ∨ slot = 1 then some GeneralDictionaryJournalRefinement228Reobserve.exactCopy else none) = some descriptor
 split at found
 · cases Option.some.inj found
   have impossible := point (.type (4,2)) (by simp)
   exact False.elim (by cases impossible)
 · split at found
   · rename_i equal
     cases Option.some.inj found
     simp [equal]
   · cases found

theorem eight (prior : GeneralNominalSaturationState.State GeneralDictionaryGroundCopy218Source.roles) (allocated reserved ordinary)
 (same : prior.context.state = GeneralDictionaryGroundCopy218Reobserve.looseExtended allocated reserved ordinary) :
 GeneralNominalPointRevision240.Preserves (GeneralDictionaryGroundCopy218Reobserve.revisionFor prior allocated reserved ordinary same) := by
 rcases prior with ⟨⟨data,interpretation⟩,packets,sites,edges,aliases⟩
 dsimp only at same
 subst data
 intro slot descriptor found point
 change (if slot = 6 then some GeneralDictionaryGroundCopy218Source.loose else if slot = 7 then some GeneralDictionaryGroundCopy218Source.exactCopy else none) = some descriptor at found
 change (if slot = 6 ∨ slot = 7 then some GeneralDictionaryGroundCopy218Source.exactCopy else none) = some descriptor
 split at found
 · cases Option.some.inj found
   have impossible := point (.type (2,3)) (by simp)
   exact False.elim (by cases impossible)
 · split at found
   · rename_i equal
     cases Option.some.inj found
     simp [equal]
   · cases found

end Yulang.GeneralDictionaryPointRevisions240
