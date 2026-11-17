import Yulang.GeneralNominalRebaseMachine241
import Yulang.B4TargetV2
namespace Yulang.GeneralNominalRebaseScheduler242
open GeneralNominalRebaseStore241 (Owner Block)
variable {factCount ownerCount : Nat}
abbrev Facts (n : Nat) := Fin n → Bool
variable (ownerAt : Fin ownerCount → Owner)
variable (compile : Facts factCount → Fin ownerCount → Block)
abbrev State (factCount ownerCount : Nat) := GeneralNominalRebaseMachine241.State factCount ownerCount

def refresh (state : State factCount ownerCount) (facts : Facts factCount) : State factCount ownerCount :=
 GeneralNominalRebaseMachine241.learn state ⟨facts,fun _ => true⟩
def service (state : State factCount ownerCount) (index : Fin ownerCount) : State factCount ownerCount :=
 GeneralNominalRebaseMachine241.service ownerAt state index (compile state.work.facts index)
def Consistent (state : State factCount ownerCount) : Prop :=
 ∀ index, state.work.dirty index = false → state.table.blocks (ownerAt index) = compile state.work.facts index
def Clean (state : State factCount ownerCount) : Prop := ∀ index, state.work.dirty index = false
def Closed (discover : Facts factCount → Facts factCount) (state : State factCount ownerCount) : Prop :=
 ∀ index, discover state.work.facts index = true → state.work.facts index = true
inductive Step (discover : Facts factCount → Facts factCount) : State factCount ownerCount → State factCount ownerCount → Prop
 | learn (before : State factCount ownerCount)
   (novel : ∃ index, before.work.facts index = false ∧ discover before.work.facts index = true) :
   Step discover before (refresh before (fun index => before.work.facts index || discover before.work.facts index))
 | service (before : State factCount ownerCount) (index : Fin ownerCount) (pending : before.work.dirty index = true) :
   Step discover before (service ownerAt compile before index)
variable {ownerAt compile} {before after : State factCount ownerCount} {discover : Facts factCount → Facts factCount}
theorem simulation (action : Step ownerAt compile discover before after) : GeneralNominalRebaseMachine241.Step ownerAt before after := by
 cases action with
 | learn novel =>
   apply GeneralNominalRebaseMachine241.Step.learn
   · intro index held; simp only [held,Bool.true_or]
   · obtain ⟨index,old,new⟩ := novel
     exact ⟨index,old,by simp only [old,new,Bool.false_or]⟩
 | service index pending => exact GeneralNominalRebaseMachine241.Step.service before index _ pending

theorem refresh_consistent (state : State factCount ownerCount) (facts : Facts factCount) :
 Consistent ownerAt compile (refresh state facts) := by
 intro index clear
 cases clear

theorem service_consistent (injective : Function.Injective ownerAt)
 (known : Consistent ownerAt compile before) (index : Fin ownerCount) :
 Consistent ownerAt compile (service ownerAt compile before index) := by
 intro other clear
 by_cases same : other = index
 · subst other; exact GeneralNominalRebaseMachine241.service_at (ownerAt := ownerAt) before index _
 · have distinct : ownerAt other ≠ ownerAt index := fun equal => same (injective equal)
   change (GeneralNominalRebaseMachine241.service ownerAt before index (compile before.work.facts index)).table.blocks (ownerAt other) = compile before.work.facts other
   rw [GeneralNominalRebaseMachine241.service_other (ownerAt := ownerAt) before index _ distinct]
   exact known other (by simpa only [service,GeneralNominalRebaseMachine241.service,GeneralNominalRebaseProgress241.drain,same,ite_false] using clear)

theorem step_consistent (injective : Function.Injective ownerAt)
 (known : Consistent ownerAt compile before)
 (action : Step ownerAt compile discover before after) : Consistent ownerAt compile after := by
 cases action with
 | learn => exact refresh_consistent _ _
 | service index pending => exact service_consistent injective known index

theorem trace_consistent (injective : Function.Injective ownerAt)
 (known : Consistent ownerAt compile before)
 (path : B4Target.Steps (Step ownerAt compile discover) before after) : Consistent ownerAt compile after := by
 induction path with
 | refl => exact known
 | tail path step ih => exact step_consistent injective ih step

theorem clean_table (known : Consistent ownerAt compile before) (clean : Clean before) :
 ∀ index, before.table.blocks (ownerAt index) = compile before.work.facts index := fun index => known index (clean index)

theorem halted_iff : (¬ ∃ after, Step ownerAt compile discover before after) ↔ Clean before ∧ Closed discover before := by
 constructor
 · intro halted
   constructor
   · intro index
     cases value : before.work.dirty index with
     | false => rfl
     | true => exact False.elim (halted ⟨_,.service before index value⟩)
   · intro index present
     cases value : before.work.facts index with
     | false => exact False.elim (halted ⟨_,.learn before ⟨index,value,present⟩⟩)
     | true => rfl
 · rintro ⟨clean,closed⟩ ⟨after,action⟩
   cases action with
   | learn novel =>
     obtain ⟨index,absent,present⟩ := novel
     have held := closed index present
     rw [absent] at held
     cases held
   | service index pending =>
     rw [clean index] at pending
     cases pending

theorem rank_decreases (action : Step ownerAt compile discover before after) :
 GeneralNominalRebaseProgress241.rank after.work < GeneralNominalRebaseProgress241.rank before.work := GeneralNominalRebaseMachine241.rank_decreases (simulation action)

theorem accessible (state : State factCount ownerCount) : Acc (fun after before => Step ownerAt compile discover before after) state := by
 have auxiliary : ∀ current : State factCount ownerCount, Acc (fun after before => GeneralNominalRebaseMachine241.Step ownerAt before after) current →
   Acc (fun after before => Step ownerAt compile discover before after) current := by
   intro current valid
   induction valid with
   | intro current _ ih => exact Acc.intro current (fun after action => ih after (simulation action))
 exact auxiliary state (GeneralNominalRebaseMachine241.accessible ownerAt state)

theorem terminal_exists (state : State factCount ownerCount) :
 ∃ last, B4Target.Steps (Step ownerAt compile discover) state last ∧ Clean last ∧ Closed discover last := by
 classical
 have auxiliary : ∀ current : State factCount ownerCount, Acc (fun after before => Step ownerAt compile discover before after) current →
   ∃ last, B4Target.Steps (Step ownerAt compile discover) current last ∧ Clean last ∧ Closed discover last := by
   intro current valid
   induction valid with
   | intro current _ ih =>
     by_cases next : ∃ after, Step ownerAt compile discover current after
     · obtain ⟨after,action⟩ := next
       obtain ⟨last,path,clean,closed⟩ := ih after action
       have first : B4Target.Steps (Step ownerAt compile discover) current after := .tail .refl action
       have join : ∀ {a b c : State factCount ownerCount}, B4Target.Steps (Step ownerAt compile discover) a b →
           B4Target.Steps (Step ownerAt compile discover) b c → B4Target.Steps (Step ownerAt compile discover) a c := by
         intro a b c one two
         induction two with
         | refl => exact one
         | tail path step ih => exact .tail ih step
       exact ⟨last,join first path,clean,closed⟩
     · exact ⟨current,.refl,(halted_iff.mp next).1,(halted_iff.mp next).2⟩
 exact auxiliary state (accessible state)

theorem completion (injective : Function.Injective ownerAt) (known : Consistent ownerAt compile before) :
 ∃ last, B4Target.Steps (Step ownerAt compile discover) before last ∧ Closed discover last ∧
   ∀ index, last.table.blocks (ownerAt index) = compile last.work.facts index := by
 obtain ⟨last,path,clean,closed⟩ := terminal_exists (ownerAt := ownerAt) (compile := compile) (discover := discover) before
 exact ⟨last,path,closed,clean_table (trace_consistent injective known path) clean⟩
end Yulang.GeneralNominalRebaseScheduler242
