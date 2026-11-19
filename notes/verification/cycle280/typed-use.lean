import Yulang.GeneralRebaseStoredRegression280

open Yulang
open GeneralNominalExamples (displayRoot displayChild registry)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (compiled after)
open GeneralRebaseDisplayFrame276 (before)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseCompactMachine280 (CompactStep compact)
open GeneralRebaseArchiveReplay280 (strip restore)
open GeneralRebaseStoredStep280 (StoredStep)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

example (goal : State roles) :
    CompactStep compiled displayRoot before goal ↔ goal = compact after :=
  GeneralRebaseCompactRegression280.Display.one_step goal

example (goal : State roles) :
    StoredStep registry displayRoot (strip before) goal ↔ goal = strip after :=
  GeneralRebaseStoredRegression280.one_stored_step goal

example : (restore (strip after)).core.erased.current.edges = [(displayRoot,displayChild)] :=
  GeneralRebaseStoredRegression280.restored_edge

example (m : GeneralNominalCommonBridge.Assignment) (valid : Models (restore (strip after)) m) :
    (boundary roles).Evidence registry (restore (strip after)) m displayRoot (.node 1 [.node 3 []]) :=
  GeneralRebaseStoredRegression280.payload m valid

example (n : Nat) :
    restore (strip (GeneralDictionaryLooseIterationIteration240.state n)) =
      GeneralDictionaryLooseIterationIteration240.state n :=
  GeneralRebaseStoredRegression280.version240_lossless n

example {r : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles} {start after : State roles}
    (init : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start after) :
    restore (strip after) = after :=
  GeneralRebaseArchiveReplay280.source_roundtrip init path
