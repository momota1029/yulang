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
