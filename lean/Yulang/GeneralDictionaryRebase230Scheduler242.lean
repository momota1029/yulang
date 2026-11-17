import Yulang.GeneralDictionaryRebase230Service241
import Yulang.GeneralNominalRebaseSchedulerOrder242
set_option backward.isDefEq.respectTransparency false
/-! The actual 230 merge blocks in the checked finite scheduler. A real new
observation bit invalidates a clean owner; service installs the current block.
This two-step path is not yet a path of the complete source boundary. -/
namespace Yulang.GeneralDictionaryRebase230Scheduler242
open GeneralNominalRebaseScheduler242
open GeneralDictionaryRebase230Service241 (owner ownerAt oldBlock newBlock)
open GeneralDictionaryRebase230Private241 (publicAtoms rebased)
open GeneralDictionaryOptionalInstall229 (model actual)
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralDictionaryOptionalInitial229 (registry declaration)

def compile (facts : Facts 1) (_ : Fin 1) : GeneralNominalRebaseStore241.Block :=
 if facts 0 then newBlock else oldBlock

def discover (_ : Facts 1) : Facts 1 := fun _ => true

def initial : State 1 1 where
 work := ⟨fun _ => false,fun _ => false⟩
 table := ⟨publicAtoms,[owner],fun _ => oldBlock⟩
def observed : State 1 1 := refresh initial (fun index => initial.work.facts index || discover initial.work.facts index)
def final : State 1 1 := service ownerAt compile observed 0

theorem owner_injective : Function.Injective ownerAt := by
 intro first last _
 apply Fin.ext
 omega

theorem initial_consistent : Consistent ownerAt compile initial := by intro index _; rfl

theorem learn_step : Step ownerAt compile discover initial observed :=
 .learn initial ⟨0,rfl,rfl⟩

theorem service_step : Step ownerAt compile discover observed final := .service observed 0 rfl

theorem path : B4Target.Steps (Step ownerAt compile discover) initial final :=
 .tail (.tail .refl learn_step) service_step

theorem final_clean : Clean final := by
 intro index
 have zero : index = 0 := by apply Fin.ext; omega
 subst index
 simp [final,service,GeneralNominalRebaseMachine241.service,GeneralNominalRebaseProgress241.drain]

theorem final_closed : Closed discover final := by intro index _; rfl

theorem final_stopped : ¬ ∃ next, Step ownerAt compile discover final next :=
 halted_iff.mpr ⟨final_clean,final_closed⟩

theorem final_block : final.table.blocks owner = newBlock := by
 have exactBlock := clean_table (trace_consistent owner_injective initial_consistent path) final_clean 0
 exact exactBlock

theorem initial_models : GeneralNominalRebaseStore241.Models
 initial.table.baseAtoms initial.table.owners initial.table.blocks model := by
 refine ⟨GeneralDictionaryRebase230Private241.old_public,?_⟩
 intro key member
 exact GeneralDictionaryRebase230Private241.old_merges

theorem final_models : GeneralNominalRebaseStore241.Models
 final.table.baseAtoms final.table.owners final.table.blocks rebased := by
 refine ⟨GeneralDictionaryRebase230Private241.retained_public,?_⟩
 intro key member
 have same : key = owner := List.mem_singleton.mp member
 rw [same,final_block]
 exact GeneralDictionaryRebase230Private241.new_merges

theorem final_source : GeneralNominalState.Models snapshot rebased :=
 GeneralDictionaryRebase230Private241.raw_models

theorem final_actual : rebased actual = model actual :=
 GeneralDictionaryRebase230Private241.agrees actual (by simp [GeneralDictionaryRebase230Private241.pool])

theorem final_capture : GeneralNominalRebaseProjection241.CapturedFits snapshot registry root.identity
 declaration GeneralDictionaryRebase230Private241.newBindings (fun _ => actual) rebased :=
 GeneralDictionaryRebase230Private241.actual_fits

theorem rank_initial : GeneralNominalRebaseProgress241.rank initial.work = 2 := rfl

theorem rank_observed : GeneralNominalRebaseProgress241.rank observed.work = 1 := rfl

theorem rank_final : GeneralNominalRebaseProgress241.rank final.work = 0 := rfl

theorem no_old_and_new : ¬ PresenceNormalForm.All CommonNominalFullCarrier.model rebased oldBlock :=
 GeneralDictionaryRebase230Private241.rejects_stale

theorem discover_monotone : GeneralNominalRebaseSchedulerOrder242.Monotone discover :=
 fun _ _ _ _ _ => rfl

theorem all_terminal_blocks
 (trace : B4Target.Steps (Step ownerAt compile discover) initial last)
 (halted : ¬ ∃ next, Step ownerAt compile discover last next) : last.table.blocks owner = newBlock := by
 have conditions := halted_iff.mp halted
 have same := GeneralNominalRebaseSchedulerOrder242.tables_unique owner_injective discover_monotone
   initial_consistent trace path conditions.1 final_clean conditions.2 final_closed 0
 exact same.trans final_block
end Yulang.GeneralDictionaryRebase230Scheduler242
