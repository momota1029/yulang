import Yulang.GeneralDictionaryCompoundNoInstance238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundOperational238
open GeneralDictionaryJournalRefinement228Source GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPoint238 GeneralDictionaryCompoundObstruction238
open GeneralNominalVersionedJournal232

theorem not_committed : ¬ GeneralNominalVersionedInstallStep232.Committed point currentPlan := by
  intro committed
  exact no_current_packet _ inhabited (committed.1 _ inhabited).1

theorem not_installable (effect : Effect roles) (same : effect.plan = currentPlan) :
    ¬ GeneralNominalVersionedMixedKernel234.Installable registry point effect := by
  intro enabled
  obtain ⟨model,valid,held,_⟩ := enabled.common
  rw [same] at held
  exact no_current_packet model valid held

end Yulang.GeneralDictionaryCompoundOperational238
