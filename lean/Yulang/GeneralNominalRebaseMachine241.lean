import Yulang.GeneralNominalRebaseStore241
import Yulang.GeneralNominalRebaseProgress241

/-! A finite work state paired with an owner block table. Service accepts an
arbitrary replacement block: these structural progress laws do not establish
semantic projection preservation, which requires a separate block contract. -/
namespace Yulang.GeneralNominalRebaseMachine241
open GeneralNominalRebaseStore241 (Owner Block)

structure State (factCount ownerCount : Nat) where
 work : GeneralNominalRebaseProgress241.State factCount ownerCount
 table : GeneralNominalRebaseStore241.State

variable {factCount ownerCount : Nat}
variable (ownerAt : Fin ownerCount → Owner)

def learn (state : State factCount ownerCount)
 (work : GeneralNominalRebaseProgress241.State factCount ownerCount) : State factCount ownerCount :=
 ⟨work,state.table⟩

def service (state : State factCount ownerCount) (index : Fin ownerCount) (block : Block) : State factCount ownerCount :=
 ⟨GeneralNominalRebaseProgress241.drain state.work index,
 GeneralNominalRebaseStore241.rebase state.table (ownerAt index) block⟩

inductive Step : State factCount ownerCount → State factCount ownerCount → Prop
 | learn (before : State factCount ownerCount)
   (work : GeneralNominalRebaseProgress241.State factCount ownerCount)
   (retained : ∀ index, before.work.facts index = true → work.facts index = true)
   (newFact : ∃ index, before.work.facts index = false ∧ work.facts index = true) :
   Step before (learn before work)
 | service (before : State factCount ownerCount) (index : Fin ownerCount) (block : Block)
   (pending : before.work.dirty index = true) : Step before (service ownerAt before index block)

variable {ownerAt} {before after : State factCount ownerCount}

theorem simulation (action : Step ownerAt before after) :
 GeneralNominalRebaseProgress241.Step before.work after.work := by
 cases action with
 | learn work retained newFact => exact .fact before.work work retained newFact
 | service index block pending => exact .clear before.work index pending

theorem rank_decreases (action : Step ownerAt before after) :
 GeneralNominalRebaseProgress241.rank after.work < GeneralNominalRebaseProgress241.rank before.work :=
 GeneralNominalRebaseProgress241.rank_decreases (simulation action)

theorem accessible (ownerAt : Fin ownerCount → Owner) (state : State factCount ownerCount) :
 Acc (fun after before => Step ownerAt before after) state := by
 have lift : ∀ work : GeneralNominalRebaseProgress241.State factCount ownerCount,
     Acc (fun after before => GeneralNominalRebaseProgress241.Step before after) work →
     ∀ current : State factCount ownerCount, current.work = work →
       Acc (fun after before => Step ownerAt before after) current := by
   intro work accessible
   induction accessible with
   | intro work _ ih =>
     intro current same
     constructor
     intro next action
     exact ih next.work (same ▸ simulation action) next rfl
 exact lift state.work (GeneralNominalRebaseProgress241.accessible state.work) state rfl

theorem wellFounded (ownerAt : Fin ownerCount → Owner) :
 WellFounded (fun after before : State factCount ownerCount => Step ownerAt before after) :=
 ⟨accessible ownerAt⟩

theorem public_unchanged (action : Step ownerAt before after) : after.table.baseAtoms = before.table.baseAtoms := by
 cases action <;> rfl

theorem owners_unchanged (action : Step ownerAt before after) : after.table.owners = before.table.owners := by
 cases action <;> rfl

theorem learn_table (state : State factCount ownerCount) (work) : (learn state work).table = state.table := rfl

theorem service_at (state : State factCount ownerCount) (index : Fin ownerCount) (block : Block) :
 (service ownerAt state index block).table.blocks (ownerAt index) = block :=
 GeneralNominalRebaseStore241.replace_at

theorem service_other (state : State factCount ownerCount) (index : Fin ownerCount) (block : Block)
 (different : other ≠ ownerAt index) :
 (service ownerAt state index block).table.blocks other = state.table.blocks other :=
 GeneralNominalRebaseStore241.replace_other different

theorem outside_unchanged (action : Step ownerAt before after)
 (outside : ∀ index, other ≠ ownerAt index) : after.table.blocks other = before.table.blocks other := by
 cases action with
 | learn => rfl
 | service index block pending => exact service_other before index block (outside index)

theorem registered_preserved (action : Step ownerAt before after)
 (registered : ∀ index, ownerAt index ∈ before.table.owners) : ∀ index, ownerAt index ∈ after.table.owners := by
 rw [owners_unchanged action]
 exact registered

theorem no_self_step (state : State factCount ownerCount) : ¬ Step ownerAt state state :=
 fun action => Nat.lt_irrefl _ (rank_decreases action)

end Yulang.GeneralNominalRebaseMachine241
