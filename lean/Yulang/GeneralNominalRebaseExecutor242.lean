import Yulang.GeneralNominalRebaseScheduler242
/-! Executable finite search and a rank-bounded recursive executor. No external
fuel assumption or source-level operation simulation is hidden in its result. -/
namespace Yulang.GeneralNominalRebaseExecutor242
open GeneralNominalRebaseScheduler242
open GeneralNominalRebaseStore241 (Owner Block)
open GeneralNominalRebaseProgress241 (rank)
variable {factCount ownerCount : Nat}
variable (ownerAt : Fin ownerCount → Owner) (compile : Facts factCount → Fin ownerCount → Block)
 (discover : Facts factCount → Facts factCount)

def next (state : State factCount ownerCount) : Option (State factCount ownerCount) :=
 match (List.finRange factCount).find? (fun index => !state.work.facts index && discover state.work.facts index) with
 | some _ => some (refresh state (fun index => state.work.facts index || discover state.work.facts index))
 | none => match (List.finRange ownerCount).find? state.work.dirty with
   | some index => some (service ownerAt compile state index)
   | none => none

variable {ownerAt compile discover}
theorem next_sound (found : next ownerAt compile discover before = some after) :
 Step ownerAt compile discover before after := by
 unfold next at found
 split at found
 · rename_i index selected
   cases found
   have valid := List.find?_some selected
   have split : before.work.facts index = false ∧ discover before.work.facts index = true := by simpa using valid
   exact .learn before ⟨index,split⟩
 · split at found
   · rename_i index selected
     cases found
     exact .service before index (List.find?_some selected)
   · cases found

theorem next_none (missing : next ownerAt compile discover before = none) : Clean before ∧ Closed discover before := by
 unfold next at missing
 split at missing
 · cases missing
 · rename_i noFact
   split at missing
   · cases missing
   · rename_i noDirty
     constructor
     · intro index
       have absent := List.find?_eq_none.mp noDirty index (List.mem_finRange index)
       simpa using absent
     · intro index discovered
       have absent := List.find?_eq_none.mp noFact index (List.mem_finRange index)
       simpa [discovered] using absent

variable (ownerAt compile discover)
def runFuel : Nat → State factCount ownerCount → State factCount ownerCount
 | 0,state => state
 | fuel+1,state => match next ownerAt compile discover state with
   | none => state
   | some after => runFuel fuel after

def run (state : State factCount ownerCount) : State factCount ownerCount :=
 runFuel ownerAt compile discover (rank state.work) state

variable {ownerAt compile discover}
theorem runFuel_correct (fuel : Nat) (state : State factCount ownerCount) (enough : rank state.work ≤ fuel) :
 B4Target.Steps (Step ownerAt compile discover) state (runFuel ownerAt compile discover fuel state) ∧
 Clean (runFuel ownerAt compile discover fuel state) ∧ Closed discover (runFuel ownerAt compile discover fuel state) := by
 induction fuel generalizing state with
 | zero =>
   have halted : ¬ ∃ after, Step ownerAt compile discover state after := by
     rintro ⟨after,action⟩
     have strict := rank_decreases action
     omega
   exact ⟨.refl,halted_iff.mp halted⟩
 | succ fuel ih =>
   cases selected : next ownerAt compile discover state with
   | none =>
     simpa only [runFuel,selected] using And.intro (B4Target.Steps.refl (step := Step ownerAt compile discover) (s := state)) (next_none selected)
   | some after =>
     have action := next_sound selected
     have strict := rank_decreases action
     have result := ih after (by omega)
     have compose : B4Target.Steps (Step ownerAt compile discover) state (runFuel ownerAt compile discover fuel after) := by
       have one : B4Target.Steps (Step ownerAt compile discover) state after := .tail .refl action
       have join : ∀ {a b c : State factCount ownerCount},
           B4Target.Steps (Step ownerAt compile discover) a b →
           B4Target.Steps (Step ownerAt compile discover) b c →
           B4Target.Steps (Step ownerAt compile discover) a c := by
         intro a b c first last
         induction last with
         | refl => exact first
         | tail path step previous => exact .tail previous step
       exact join one result.1
     simpa only [runFuel,selected] using And.intro compose result.2

theorem correct (state : State factCount ownerCount) :
 B4Target.Steps (Step ownerAt compile discover) state (run ownerAt compile discover state) ∧
 Clean (run ownerAt compile discover state) ∧ Closed discover (run ownerAt compile discover state) :=
 runFuel_correct _ state (Nat.le_refl _)

theorem table_exact (injective : Function.Injective ownerAt)
 (known : Consistent ownerAt compile state) :
 ∀ index, (run ownerAt compile discover state).table.blocks (ownerAt index) =
 compile (run ownerAt compile discover state).work.facts index :=
 clean_table (trace_consistent injective known (correct state).1) (correct state).2.1
end Yulang.GeneralNominalRebaseExecutor242
