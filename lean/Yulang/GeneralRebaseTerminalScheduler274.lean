import Yulang.GeneralRebaseTerminalPayload274

set_option maxRecDepth 21000
set_option maxHeartbeats 7100000
namespace Yulang.GeneralRebaseTerminalScheduler274
open GeneralRebaseTerminalMachine274 (Stage Step next owner)
open GeneralNominalRebaseScheduler242 (State)
open GeneralDictionaryRebase230Scheduler242 (initial observed final compile discover)
open GeneralDictionaryRebase230Service241 (ownerAt oldBlock newBlock)
open GeneralDictionaryRebase230Executor242 (next_initial next_observed next_final)

def scheduler : Stage → Option (State 1 1)
 | .source => none
 | .installed => some initial
 | .observed => some observed
 | .terminal => some final

theorem after_install (a b : Stage) (step : Step a b) (previous : a ≠ .source) :
 ∃ cur nextState, scheduler a = some cur ∧ scheduler b = some nextState ∧
   GeneralNominalRebaseExecutor242.next ownerAt compile discover cur = some nextState := by
 rcases GeneralRebaseTerminalBridge274.phase_edges step with ⟨rfl,_⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · exact False.elim (previous rfl)
 · exact ⟨initial,observed,rfl,rfl,next_initial⟩
 · exact ⟨observed,final,rfl,rfl,next_observed⟩

theorem stopped :
 (scheduler .terminal).bind (GeneralNominalRebaseExecutor242.next ownerAt compile discover) = none :=
 next_final

theorem logical_cells :
 initial.table.blocks GeneralDictionaryRebase230Service241.owner = oldBlock ∧
 observed.table.blocks GeneralDictionaryRebase230Service241.owner = oldBlock ∧
 final.table.blocks GeneralDictionaryRebase230Service241.owner = newBlock :=
 ⟨rfl,rfl,GeneralDictionaryRebase230Scheduler242.final_block⟩

end Yulang.GeneralRebaseTerminalScheduler274
