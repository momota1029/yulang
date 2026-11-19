import Yulang.GeneralRebaseFreshOnlyCache283

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 10500000
namespace Yulang.GeneralRebaseFreshOnlyFixtures283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseInstallCache283 (Valid add)
open GeneralRebaseFreshOnlyCache283 (quick quick_exact)
open GeneralRebaseFreshDelta283 (NoBackReads)
open GeneralRebaseIncrementalGate283 (changed)
open GeneralRebaseOptionalDelta283 (newLo newHi)
open GeneralNominalVersionedMixedSeedLedger237 (reachable)

namespace Version
open GeneralDictionaryVersionLoopIteration239 (state)
open GeneralRebaseVersionDelta283 (family_cache candidate_family distinct e only_two)
open GeneralRebaseLoopBase282.Version (decode_reach)

theorem quick_two (n : Nat) (defs : List (Entry Nat)) (valid : Valid defs (state n)) :
    (quick defs (e n)).length = 2 := by
  have clean := GeneralRebaseTwoWrites283.no_old_reads (family_cache n defs valid)
    (candidate_family n defs valid) distinct
  rw [quick_exact valid (reachable (decode_reach n)) rfl clean]
  exact GeneralRebaseTwoWrites283.two_count (family_cache n defs valid) (candidate_family n defs valid) distinct
end Version

namespace Loose
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralRebaseLooseDelta283 (family_cache candidate_family distinct e only_two)
open GeneralRebaseLoopBase282.Loose (decode_reach)

theorem quick_two (n : Nat) (defs : List (Entry Nat)) (valid : Valid defs (state n)) :
    (quick defs (e n)).length = 2 := by
  have clean := GeneralRebaseTwoWrites283.no_old_reads (family_cache n defs valid)
    (candidate_family n defs valid) distinct
  rw [quick_exact valid (reachable (decode_reach n)) rfl clean]
  exact GeneralRebaseTwoWrites283.two_count (family_cache n defs valid) (candidate_family n defs valid) distinct
end Loose

namespace Optional
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (effect installed)
open GeneralRebaseOptionalOverwrite282 (point_reached)
open GeneralRebaseOptionalDelta283 (clean selected)
open GeneralNominalCommonBridge (Assignment)

theorem quick_new_only (defs : List (Entry Nat)) (valid : Valid defs point) (row : Entry Nat) :
    row ∈ quick defs effect ↔ row = newLo ∨ row = newHi := by
  rw [quick_exact valid (reachable point_reached) (show effect.snapshot = point.core from rfl) (clean valid)]
  exact selected valid row

theorem same_semantics (defs : List (Entry Nat)) (valid : Valid defs point) (base : Assignment) :
    GeneralRebaseFreshOnlyCache283.evaluate defs effect (GeneralRebaseInstallCache283.interpret defs base) =
      GeneralRebaseHistoryOrder282.decode installed base :=
  GeneralRebaseFreshOnlyCache283.reads valid point_reached rfl (clean valid) base

end Optional

end Yulang.GeneralRebaseFreshOnlyFixtures283
