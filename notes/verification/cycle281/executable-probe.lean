import Yulang.GeneralRebaseLoopReplay281
import Yulang.GeneralRebasePhaseCache281

open Yulang
open GeneralRebaseAggregateTags281 (fixed versioned)
open GeneralRebaseLoopReplay281
open GeneralRebasePhaseCache281 (planKey prepend)
open GeneralRebasePhaseFixture281 (codec)
open GeneralRebasePhaseFixture281 (initialPlan)

#eval (Version.rows 0 |>.map (fixed (GeneralDictionaryVersionLoopBook239.packet 0)) |>.map Prod.fst) ==
  (Version.rows 1 |>.map (fixed (GeneralDictionaryVersionLoopBook239.packet 1)) |>.map Prod.fst)
#eval (Loose.rows 0 |>.map (fixed (GeneralDictionaryLooseIterationBook240.packet 0)) |>.map Prod.fst) ==
  (Loose.rows 1 |>.map (fixed (GeneralDictionaryLooseIterationBook240.packet 1)) |>.map Prod.fst)
#eval (Version.rows 0 |>.map (versioned (GeneralDictionaryVersionLoopBook239.packet 0)) |>.map Prod.fst) ==
  (Version.rows 1 |>.map (versioned (GeneralDictionaryVersionLoopBook239.packet 1)) |>.map Prod.fst)
#eval (Loose.rows 0 |>.map (versioned (GeneralDictionaryLooseIterationBook240.packet 0)) |>.map Prod.fst) ==
  (Loose.rows 1 |>.map (versioned (GeneralDictionaryLooseIterationBook240.packet 1)) |>.map Prod.fst)
#eval (planKey codec initialPlan).map Prod.snd
#eval (planKey codec (GeneralDictionaryVersionedPoint233.plan [] [] [])).map Prod.snd
#eval let seen := prepend codec [] initialPlan
  (prepend codec seen initialPlan).length
#eval let seen := prepend codec [] initialPlan
  (prepend codec seen (GeneralDictionaryVersionedPoint233.plan [] [] [])).length
