import Yulang.GeneralRebaseReportDecoder259
namespace Yulang.GeneralDictionaryObservedRebase259
open GeneralRebaseStep258
open GeneralDictionaryRebaseStep258 (facts initialState finalState)

/-- Read the actual inspection result at completed stage n, transport source
slots, decode fixed-basis facts. n is not stored in the new finite state. -/
def observeAt (n : Nat) : Observer facts := fun _ =>
 (GeneralRebaseReportDecoder259.compile (GeneralDictionaryReportProjection257.transport n
   (GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet n)))).toList

theorem observed_exact (n : Nat) : observeAt n = GeneralDictionaryRebaseStep258.observe := by
 funext state
 simp only [observeAt,GeneralRebaseReportDecoder259.actual,Option.toList_some,
   GeneralDictionaryRebaseStep258.observe]

/-- A relation allowing any actual family observation. It does not claim a
source compiler for arbitrary programs or simulate old administrative steps. -/
def ObservedStep (before after : State facts) : Prop := ∃ n, Step (observeAt n) before after

theorem step_exact (before after : State facts) : ObservedStep before after ↔
 Step GeneralDictionaryRebaseStep258.observe before after := by
 constructor
 · rintro ⟨n,step⟩; simpa only [observed_exact] using step
 · intro step; exact ⟨0,by simpa only [observed_exact] using step⟩

theorem initial_install (n : Nat) : Step (observeAt n) initialState finalState := by
 rw [observed_exact]; exact GeneralDictionaryRebaseStep258.first_step

theorem stops (n : Nat) (after : State facts) : ¬ Step (observeAt n) finalState after := by
 rw [observed_exact]; exact GeneralDictionaryRebaseStep258.final_stops after

theorem decreasing (step : ObservedStep before after) : after.remaining.length < before.remaining.length :=
 decreases _ ((step_exact _ _).mp step)

theorem terminating (state : State facts) : Acc (fun after before => ObservedStep before after) state := by
 have equal : (fun after before => ObservedStep before after) =
   (fun after before => Step GeneralDictionaryRebaseStep258.observe before after) := by
   funext after before; exact propext (step_exact before after)
 rw [equal]
 exact GeneralDictionaryRebaseStep258.terminating state

theorem no_two (middle last : State facts) : ¬ (ObservedStep initialState middle ∧ ObservedStep middle last) := by
 simp only [step_exact]
 exact GeneralDictionaryRebaseStep258.no_two_steps middle last
end Yulang.GeneralDictionaryObservedRebase259
