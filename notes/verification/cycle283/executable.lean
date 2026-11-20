import Yulang.GeneralRebaseFrontierPairs283

open Yulang
open GeneralRebaseCacheCounterexamples283 (earlier full)
open GeneralRebaseDirtyHistory283 (select)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralRebaseSlice283 (build)
open GeneralRebaseSortedCache283 (push)
open GeneralRebaseAliasMemo283 (cache root)
open GeneralRebaseClassFrontier283 (fresh pairs)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralSourceState (Output)

#eval (changes earlier full).map Prod.fst
#eval (select (earlier.map Prod.fst) earlier [1]).map Prod.fst
#eval (build full [5]).keep.map Prod.fst
#eval GeneralRebaseOneSource283.one (.inter (.union (.var 7) (.var 7)) (.var 7))
#eval GeneralRebaseOneSource283.one (.union (.var 7) (.var 8))

#eval let old := push (packetEntries (GeneralDictionaryVersionLoopBook239.packet 0)) []
  let next := push (packetEntries (GeneralDictionaryVersionLoopBook239.packet 1)) old
  ((changes old next).length, (cache next []).map fun memo =>
    (root memo (GeneralDictionaryVersionLoopNames238.lower 2),root memo (GeneralDictionaryVersionLoopNames238.upper 1)))

#eval let old := push (packetEntries (GeneralDictionaryLooseIterationBook240.packet 0)) []
  let next := push (packetEntries (GeneralDictionaryLooseIterationBook240.packet 1)) old
  ((changes old next).length, (cache next []).map fun memo =>
    (root memo (GeneralDictionaryLooseFamilyNames240.lower 2),root memo (GeneralDictionaryLooseFamilyNames240.upper 1)))

def first : Output := ⟨5,12⟩
def second : Output := ⟨5,14⟩
#eval (fresh [first] [first,second]).map Output.target
#eval (pairs [first] [first,second]).map (fun (a,b) => (a.target,b.target))
#eval (GeneralRebaseFrontierPairs283.fast [first] [first,second]).map (fun (a,b) => (a.target,b.target))
#eval (GeneralRebaseFrontierPairs283.fast [first,second] [first,second]).length
