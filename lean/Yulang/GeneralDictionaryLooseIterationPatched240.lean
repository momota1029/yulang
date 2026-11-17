import Yulang.GeneralDictionaryLooseFamilyNovel240
import Yulang.GeneralDictionaryLooseIterationPacketSupport240
import Yulang.GeneralNominalVersionedJournalFrame236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationPatched240
open GeneralDictionaryLooseFamilyNovel240 (bad)
open GeneralDictionaryLooseIterationBook240 (plan packet)
open GeneralDictionaryLooseLoopSource240 (model initial roles)
open GeneralDictionaryLooseFamilyNames240 (upper)
open GeneralNominalVersionedJournal232

theorem packet_holds (stage index : Nat) (later : stage < index) :
 GeneralNominalVersionedPlans231.Holds (plan stage) (bad index) := by
 apply (GeneralNominalVersionedPacketFrame236.holds_iff (plan stage) ?_).mp
   (GeneralDictionaryLooseIterationBook240.packet_holds stage)
 intro name member
 have different : name ≠ upper index := by
   intro same; subst name
   exact GeneralDictionaryLooseIterationPacketSupport240.packet_fresh stage index later member
 simp only [bad,different,ite_false]

theorem initial_support : GeneralNominalVersionedJournalFrame236.sources initial ⊆ [0,1,2,3,4] := by
 decide +kernel

theorem initial_model (index : Nat) : Models initial (bad index) := by
 apply (GeneralNominalVersionedJournalFrame236.models_iff initial ?_).mp
   GeneralDictionaryLooseLoopSource240.initial_model
 intro name member
 have bounded := initial_support member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at bounded
 have large := GeneralDictionaryLooseFamilyNames240.upper_above index
 have different : name ≠ upper index := by omega
 simp only [bad,different,ite_false]
end Yulang.GeneralDictionaryLooseIterationPatched240
