import Yulang.GeneralDictionaryBinderFact257
namespace Yulang.GeneralDictionaryPastRaw257
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context atoms packet)
open GeneralDictionaryUpperHistory257 (history)
open CommonNominalFullCarrier

theorem raw_past (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalState.Models (context index).state assignment := by
 have blockN : PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block (history n)) :=
   fun atom member => valid.2.2 atom (GeneralDictionaryUpperHistory257.block_in_source n member)
 have smallN := (GeneralDictionaryFiveSlot257.models_exact n assignment).mp
   ((GeneralDictionaryCompactView257.recovered n assignment blockN).mpr valid)
 have small0 := (GeneralDictionaryNoModelRefinement257.all_iff_zero n assignment).mp smallN
 have smallIndex := (GeneralDictionaryNoModelRefinement257.all_iff_zero index assignment).mpr small0
 have compactIndex := (GeneralDictionaryFiveSlot257.models_exact index assignment).mpr smallIndex
 have blockIndex : PresenceNormalForm.All model assignment (GeneralPresenceDefinitionRewrite244.block (history index)) :=
   fun atom member => valid.2.2 atom (GeneralDictionaryHistoricalValues257.atoms_mono index n before
     (GeneralDictionaryUpperHistory257.block_in_source index member))
 exact (GeneralDictionaryCompactView257.recovered index assignment blockIndex).mp compactIndex

theorem ordinary_past (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalVersionedPlans231.Ordinary (packet index) assignment := by
 apply (GeneralNominalVersionedInstallation231.atoms_iff ..).mp
 intro atom member
 apply valid.2.2 atom
 apply GeneralDictionaryHistoricalValues257.atoms_mono (index+1) n (by omega)
 rw [GeneralDictionaryLooseIterationBook240.atoms_next]
 exact List.mem_append_right _ member
end Yulang.GeneralDictionaryPastRaw257
