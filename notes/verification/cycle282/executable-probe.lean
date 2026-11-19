import Yulang.GeneralRebaseCompiledFixtures282

open Yulang
open GeneralRebaseLiveOwner282 (newest lookup)
open GeneralRebasePhaseKeys281 (owner)
open GeneralPresenceOrderedSort247 (sort)
open GeneralPresenceOrderedDedup247 (dedup)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralPresenceUsedSupport245 (typedReads)

#eval (newest [GeneralDictionaryVersionLoopBook239.plan 1,GeneralDictionaryVersionLoopBook239.plan 0]).length
#eval let p := GeneralDictionaryVersionLoopBook239.plan 1
  (lookup [p,GeneralDictionaryVersionLoopBook239.plan 0] (owner p)).map (fun q => q.packet.bindings) ==
    some p.packet.bindings
#eval (newest [GeneralDictionaryLooseIterationBook240.plan 1,GeneralDictionaryLooseIterationBook240.plan 0]).length
#eval let p := GeneralDictionaryLooseIterationBook240.plan 1
  (lookup [p,GeneralDictionaryLooseIterationBook240.plan 0] (owner p)).map (fun q => q.packet.bindings) ==
    some p.packet.bindings
#eval let block := packetEntries (GeneralDictionaryVersionLoopBook239.packet 1) ++
    packetEntries (GeneralDictionaryVersionLoopBook239.packet 0)
  (sort (dedup block)).map List.length
#eval let block := packetEntries (GeneralDictionaryLooseIterationBook240.packet 1) ++
    packetEntries (GeneralDictionaryLooseIterationBook240.packet 0)
  (sort (dedup block)).map List.length
#eval GeneralRebaseLoopConstant282.Version.simple.flatMap (fun row => typedReads row.2)
#eval GeneralRebaseLoopConstant282.Loose.simple.flatMap (fun row => typedReads row.2)
