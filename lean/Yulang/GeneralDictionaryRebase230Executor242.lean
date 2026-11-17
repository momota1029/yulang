import Yulang.GeneralDictionaryRebase230Scheduler242
import Yulang.GeneralNominalRebaseExecutor242
namespace Yulang.GeneralDictionaryRebase230Executor242
open GeneralDictionaryRebase230Scheduler242
open GeneralDictionaryRebase230Service241 (ownerAt owner newBlock)
open GeneralNominalRebaseExecutor242

theorem next_initial : next ownerAt compile discover initial = some observed := rfl

theorem next_observed : next ownerAt compile discover observed = some final := rfl

theorem next_final : next ownerAt compile discover final = none := rfl

theorem run_eq_final : run ownerAt compile discover initial = final := rfl

theorem run_block : (run ownerAt compile discover initial).table.blocks owner = newBlock := by
 rw [run_eq_final]
 exact final_block

theorem run_models : GeneralNominalRebaseStore241.Models
 (run ownerAt compile discover initial).table.baseAtoms
 (run ownerAt compile discover initial).table.owners
 (run ownerAt compile discover initial).table.blocks GeneralDictionaryRebase230Private241.rebased := by
 rw [run_eq_final]
 exact final_models
end Yulang.GeneralDictionaryRebase230Executor242
