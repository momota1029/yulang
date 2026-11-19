import Yulang.GeneralRebaseTwoWrites283

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseLooseDelta283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseInstallCache283 (Valid add interpret descending)
open GeneralRebaseTwoWrites283 (Distinct)
open GeneralRebaseAliasFamily283 (Family lowerRow upperRow)
open GeneralDictionaryLooseFamilyNames240 (lower upper strict upper_injective separate upper_above)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseLoopSource240 (sourceRegistry initial)
open GeneralRebaseLooseAliases283 (family)
open GeneralRebaseLoopBase282.Loose (decode_reach)
open GeneralRebaseLooseMicro278 (installed)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralRebaseIncrementalGate283 (changed)
open GeneralRebaseCachedDriver283 (Move Initial reflects_acc)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev e (n : Nat) := GeneralDictionaryLooseIterationInstall240.chosen (stages n).shape

theorem distinct : Distinct lower upper := by
  refine ⟨strict,upper_injective,?_⟩
  intro i j equal
  cases i with
  | zero =>
    have high := upper_above j
    change 2 = upper j at equal
    omega
  | succ i => exact separate i j equal

theorem same_history (n : Nat) : history (installed n) = history (state (n+1)) := rfl

theorem history_delta (n : Nat) : (changes (history (state n)) (history (installed n))).length = 2 := by
  rw [same_history]
  exact GeneralRebaseTwoWrites283.two_count (family n) (family (n+1)) distinct

theorem family_cache (n : Nat) (defs : List (Entry Nat)) (valid : Valid defs (state n)) :
    Family defs n 2 4 lower upper (fun _ => 4) := by
  have source := family n
  refine ⟨fun row => (valid.content row).trans (source.cover row),source.low_base,source.upper_reads,?_,?_,?_⟩
  · exact fun row h => source.low_fresh row ((valid.content row).mp h)
  · exact fun row h => source.high_fresh row ((valid.content row).mp h)
  · exact GeneralRebaseSortedCache283.safe _ valid.increasing
      (descending valid (GeneralNominalVersionedMixedSeedLedger237.reachable (decode_reach n)))

theorem candidate_family (n : Nat) (defs : List (Entry Nat)) (valid : Valid defs (state n)) :
    Family (add defs (e n)) (n+1) 2 4 lower upper (fun _ => 4) := by
  have recorded := GeneralNominalVersionedMixedSeedLedger237.reachable (decode_reach n)
  have after : Valid (add defs (e n)) (installed n) := GeneralRebaseInstallCache283.add_valid valid recorded rfl
  have reached : Valid (add defs (e n)) (state (n+1)) :=
    GeneralRebaseInstallCache283.transport (state := installed n) (after := state (n+1)) rfl after
  exact family_cache (n+1) _ reached

theorem selected (n : Nat) (defs : List (Entry Nat)) (valid : Valid defs (state n))
    (row : Entry Nat) :
    row ∈ changes defs (add defs (e n)) ↔ row = lowerRow lower n ∨ row = upperRow upper (fun _ => 4) n :=
  GeneralRebaseTwoWrites283.exactly_two (family_cache n defs valid) (candidate_family n defs valid) distinct row

theorem only_two (n : Nat) (defs : List (Entry Nat)) (valid : Valid defs (state n)) :
    (changed defs (e n)).length = 2 := by
  unfold changed
  rw [List.length_map]
  exact GeneralRebaseTwoWrites283.two_count (family_cache n defs valid) (candidate_family n defs valid) distinct

theorem raw_loop_still_runs :
    ¬ Acc (fun later earlier => Move sourceRegistry GeneralDictionaryLooseLoopSource240.root earlier later) (Initial initial) := by
  intro halts
  have seen := decode_reach 0
  have valid := GeneralRebaseInstallCache283.initial_valid (GeneralNominalVersionedMixedSeedLedger237.reachable seen)
  exact (fun raw => GeneralDictionaryLooseIterationNontermination240.initial_no_acc (GeneralNominalPointErasure240.old_acc raw)) (reflects_acc (p := Initial initial) seen valid halts)

end Yulang.GeneralRebaseLooseDelta283
