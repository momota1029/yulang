import Yulang.GeneralRebaseArchiveUnbounded283

open Yulang
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralRebaseAliasMemo283 (cache root)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralRebaseInstallCache283 (Valid)

example (n : Nat) :
    (changes (history (GeneralDictionaryVersionLoopIteration239.state n))
      (history (GeneralRebaseVersionMicro278.installed n))).length = 2 :=
  GeneralRebaseVersionDelta283.history_delta n

example (n : Nat) :
    (changes (history (GeneralDictionaryLooseIterationIteration240.state n))
      (history (GeneralRebaseLooseMicro278.installed n))).length = 2 :=
  GeneralRebaseLooseDelta283.history_delta n

example (n : Nat) :
    ∃ memo, cache (history (GeneralDictionaryLooseIterationIteration240.state n)) [] = some memo ∧
      (∀ i ≤ n, root memo (GeneralDictionaryLooseFamilyNames240.lower i) = 2) ∧
      (∀ i < n, root memo (GeneralDictionaryLooseFamilyNames240.upper i) = 4) := by
  obtain ⟨memo,made,lo,hi,_⟩ := GeneralRebaseLooseAliases283.canonical n
  exact ⟨memo,made,lo,hi⟩

example (bound : Nat) :
    ∃ n, bound < (GeneralRebaseInstallCache283.initial (GeneralDictionaryLooseIterationIteration240.state n)).length :=
  GeneralRebaseArchiveUnbounded283.loose_no_uniform_bound bound

example (a : Assignment) (valid : Models GeneralRebaseCompiledDisplay277.after a) :
    ∃ family,
      let s := GeneralRebaseCompiledDisplay277.after
      let m := GeneralRebaseSliceJournal283.sliced (GeneralRebaseInstallCache283.initial s)
        (GeneralRebaseSliceJournal283.journalReads s ++ GeneralRebaseSliceEvidence283.reads family) a
      Models s m ∧ GeneralRebaseSliceEvidence283.Evidence family GeneralRebaseCompiledDisplay277.compiled
        s m GeneralNominalExamples.displayRoot (.node 1 [.node 3 []]) :=
  GeneralRebaseCachedFixtures283.Display.nonleaf a valid

example (defs) (valid : Valid defs GeneralDictionaryVersionedPointStage233.point)
    (base : Assignment) :
    GeneralRebaseFreshOnlyCache283.evaluate defs GeneralDictionaryVersionedSecondInstall233.effect
      (GeneralRebaseInstallCache283.interpret defs base) =
    GeneralRebaseHistoryOrder282.decode GeneralDictionaryVersionedSecondInstall233.installed base :=
  GeneralRebaseFreshOnlyFixtures283.Optional.same_semantics defs valid base

example (next : GeneralRebaseCachedDriver283.Snapshot GeneralDictionaryGroundCopy218Source.roles) :
    ¬ GeneralRebaseCachedDriver283.Move GeneralDictionaryGroundCopy218Source.sourceRegistry
      GeneralDictionaryGroundCopy218Source.root
      (GeneralRebaseCachedDriver283.Initial GeneralDictionaryMixedGround218FinalState235.finalState) next := by
  intro m
  exact GeneralDictionaryMixedGround218FinalRegression235.no_step next.raw
    (GeneralRebaseCachedDriver283.raw m)
