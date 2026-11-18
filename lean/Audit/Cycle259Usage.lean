import Yulang.GeneralRebaseBatchOrder259
import Yulang.GeneralRebaseDriverFixtures259
import Yulang.GeneralRebaseCheckedFixtures259
import Yulang.GeneralVersionRebaseCertificate259
import Yulang.GeneralVersionPublicProjection259
import Yulang.GeneralDictionaryRebaseRun259
import Yulang.GeneralDictionaryRebaseCertificate259
open Yulang
example : GeneralRebaseReportDecoder259.atom 2 = some 0 := GeneralRebaseReportDecoder259.source_atoms.1
example : GeneralRebaseReportDecoder259.atom 3 = none := by decide
example (n : Nat) : GeneralRebaseStep258.Step (GeneralDictionaryObservedRebase259.observeAt n)
 GeneralDictionaryRebaseStep258.initialState GeneralDictionaryRebaseStep258.finalState :=
 GeneralDictionaryObservedRebase259.initial_install n
example (n : Nat) : ¬ GeneralRebaseStep258.Step (GeneralDictionaryObservedRebase259.observeAt n)
 GeneralDictionaryRebaseStep258.finalState GeneralDictionaryRebaseStep258.finalState :=
 GeneralDictionaryObservedRebase259.stops n _
example (n : Nat) (boundary : GeneralNominalCommonBridge.Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary) :
 GeneralDictionaryRebaseCertificate259.Certificate n boundary :=
 GeneralDictionaryRebaseCertificate259.certificate n boundary source

example (n : Nat) : GeneralDictionaryRebaseRun259.run n GeneralDictionaryRebaseStep258.initialState = some GeneralDictionaryRebaseStep258.finalState := GeneralDictionaryRebaseRun259.initial_runs n
example (n : Nat) : GeneralDictionaryRebaseRun259.run n GeneralDictionaryRebaseStep258.finalState = none := GeneralDictionaryRebaseRun259.final_noop n

example (n : Nat) (rows : Nat → Common.Row) : GeneralNominalVersionedJournal232.Models
 (GeneralDictionaryVersionLoopIteration239.state n) (GeneralVersionRowsRaw259.withRows rows) :=
 GeneralVersionRowsStages259.all_stages rows n
example (boundary : GeneralNominalCommonBridge.Assignment)
 (valid : GeneralNominalState.Models GeneralDictionaryVersionLoopSource237.snapshot boundary) :
 ∃ assignment, GeneralVersionBoundaryCompletion259.Agree assignment boundary ∧
 ∀ n, GeneralNominalVersionedJournal232.Models (GeneralDictionaryVersionLoopIteration239.state n) assignment :=
 (GeneralVersionPublicProjection259.simultaneous_models boundary).mpr valid
example : GeneralDictionaryRebaseCurrent259.run GeneralDictionaryRebaseStep258.finalState = none :=
 GeneralDictionaryRebaseCurrent259.stops

example : GeneralVersionRebaseStep259.run GeneralVersionRebaseStep259.initialState = some GeneralVersionRebaseStep259.finalState := GeneralVersionRebaseStep259.run_first
example : GeneralVersionRebaseStep259.run GeneralVersionRebaseStep259.finalState = none := GeneralVersionRebaseStep259.run_stop
example (n : Nat) : ¬ GeneralNominalVersionedKernel232.Committed (GeneralDictionaryVersionLoopIteration239.state n) (GeneralDictionaryVersionLoopBook239.plan n) ∧ GeneralVersionRebaseStep259.run GeneralVersionRebaseStep259.finalState = none := GeneralVersionRebaseCertificate259.old_novel_new_noop n
example (state : GeneralRebaseStep258.State GeneralVersionRebaseStep259.facts) (boundary : GeneralNominalCommonBridge.Assignment) (source : GeneralNominalState.Models GeneralDictionaryVersionLoopSource237.snapshot boundary) : GeneralVersionRebaseModels259.Models state (GeneralVersionBoundaryCompletion259.complete boundary) := GeneralVersionRebaseModels259.completed state boundary source

example : GeneralRebaseCheckedFixtures259.looseRun GeneralDictionaryRebaseStep258.initialState = .ok (some GeneralDictionaryRebaseStep258.finalState) := GeneralRebaseCheckedFixtures259.loose_first
example : GeneralRebaseCheckedFixtures259.versionRun GeneralVersionRebaseStep259.finalState = .ok none := GeneralRebaseCheckedFixtures259.version_stop
example : GeneralRebaseCheckedWrite259.commit GeneralVersionRebaseStep259.initialState [.lower 0 1] = .error [.lower 0 1] := GeneralRebaseCheckedFixtures259.version_unsupported
example (state : GeneralRebaseStep258.State GeneralDictionaryRebaseStep258.facts) (boundary : GeneralNominalCommonBridge.Assignment) (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary) : GeneralDictionaryRebaseFacts259.Models state (GeneralDictionaryInitialFill258.complete boundary) := GeneralDictionaryRebaseFacts259.completed state boundary source

example (n : Nat) : GeneralRebaseSettle259.settle (GeneralDictionaryObservedRebase259.observeAt n) GeneralDictionaryRebaseStep258.initialState = .ok GeneralDictionaryRebaseStep258.finalState := GeneralRebaseDriverFixtures259.loose_initial n
example (n : Nat) : GeneralRebaseSettle259.settle (GeneralVersionRebaseStep259.observeAt n) GeneralVersionRebaseStep259.initialState = .ok GeneralVersionRebaseStep259.finalState := GeneralRebaseDriverFixtures259.version_initial n
example : GeneralRebaseScheduler259.scan GeneralVersionRebaseStep259.initialState [[],GeneralVersionRebaseStep259.facts] = .ok (some GeneralVersionRebaseStep259.finalState) := GeneralRebaseDriverFixtures259.skip_noop

example (state : GeneralRebaseStep258.State GeneralVersionRebaseStep259.facts) :
 GeneralRebaseSettle259.settle (fun _ => [[],GeneralVersionRebaseStep259.facts]) state =
 GeneralRebaseSettle259.settle (fun _ => [GeneralVersionRebaseStep259.facts,[]]) state :=
 GeneralRebaseBatchOrder259.swap state _ _ (by simp) (fun _ member => member)
example (state : GeneralRebaseStep258.State GeneralVersionRebaseStep259.facts) :
 GeneralRebaseSettle259.settle (fun _ => [GeneralVersionRebaseStep259.facts,GeneralVersionRebaseStep259.facts]) state =
 GeneralRebaseSettle259.settle (fun _ => [GeneralVersionRebaseStep259.facts]) state :=
 GeneralRebaseBatchOrder259.duplicate state _ (fun _ member => member)
