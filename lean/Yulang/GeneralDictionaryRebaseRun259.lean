import Yulang.GeneralDictionaryRebaseCertificate259
namespace Yulang.GeneralDictionaryRebaseRun259
open GeneralRebaseStep258
open GeneralDictionaryRebaseStep258 (facts initialState finalState)

/-- Decode the actual packet observation then perform the actual finite write.
No history list or fresh private name is stored in the resulting state. -/
def run (n : Nat) (state : State facts) : Option (State facts) := do
 let proposal ← GeneralRebaseReportDecoder259.compile
   (GeneralDictionaryReportProjection257.transport n
     (GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet n)))
 tryWrite state proposal

theorem run_exact (n : Nat) (state : State facts) : run n state = tryWrite state facts := by
 simp only [run,GeneralRebaseReportDecoder259.actual]
 rfl

theorem run_step (n : Nat) (before after : State facts) : run n before = some after ↔
 Step (GeneralDictionaryObservedRebase259.observeAt n) before after := by
 rw [run_exact,tryWrite_exact,GeneralDictionaryObservedRebase259.observed_exact]
 unfold Step GeneralDictionaryRebaseStep258.observe
 simp only [List.mem_singleton]
 constructor
 · intro pair; exact ⟨facts,rfl,pair⟩
 · rintro ⟨proposal,rfl,pair⟩; exact pair

theorem initial_runs (n : Nat) : run n initialState = some finalState :=
 (run_step n _ _).mpr (GeneralDictionaryObservedRebase259.initial_install n)

theorem final_noop (n : Nat) : run n finalState = none := by
 rw [run_exact]
 rfl

theorem repeat_noop (first last : Nat) : (run first initialState).bind (run last) = none := by
 rw [initial_runs]
 exact final_noop last

/-- Run returns the finite final state and the same reconstruction satisfies
actual source packet Holds and old/new model predicates. -/
theorem run_certificate (n : Nat) (boundary : GeneralNominalCommonBridge.Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary) :
 run n initialState = some finalState ∧ GeneralDictionaryRebaseCertificate259.Certificate n boundary :=
 ⟨initial_runs n,GeneralDictionaryRebaseCertificate259.certificate n boundary source⟩
end Yulang.GeneralDictionaryRebaseRun259
