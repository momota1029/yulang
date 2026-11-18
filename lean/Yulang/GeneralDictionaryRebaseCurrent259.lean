import Yulang.GeneralNominalTypeObservation259
namespace Yulang.GeneralDictionaryRebaseCurrent259
open GeneralRebaseStep258
open GeneralDictionaryRebaseStep258 (facts initialState finalState)
/-- Finite executable representative: inspect the fixed initial source once.
The old stage index/history is used only in the correspondence theorem. -/
def run (state : State facts) : Option (State facts) := GeneralDictionaryRebaseRun259.run 0 state

theorem all_stages (n : Nat) (state : State facts) : GeneralDictionaryRebaseRun259.run n state = run state := by
 rw [run,GeneralDictionaryRebaseRun259.run_exact,GeneralDictionaryRebaseRun259.run_exact]

theorem first : run initialState = some finalState := GeneralDictionaryRebaseRun259.initial_runs 0

theorem stops : run finalState = none := GeneralDictionaryRebaseRun259.final_noop 0

theorem certificate (n : Nat) (boundary : GeneralNominalCommonBridge.Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary) :
 run initialState = some finalState ∧ GeneralDictionaryRebaseCertificate259.Certificate n boundary :=
 ⟨first,GeneralDictionaryRebaseCertificate259.certificate n boundary source⟩
end Yulang.GeneralDictionaryRebaseCurrent259
