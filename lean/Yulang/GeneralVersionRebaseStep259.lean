import Yulang.GeneralVersionReportProjection259
namespace Yulang.GeneralVersionRebaseStep259
open GeneralRebaseStep258
open GeneralDictionaryVersionLoopBook239 (context packet allocations reservations atoms)

def facts : List Fact := [.installed 0,.lower 0 0,.upper 0 0,.binder 0,.binder 1]
def atom (slot : Fin 4) : Option Nat := if slot.val = 2 then some 0 else none
abbrev initialState := initial facts
abbrev finalState := done facts

def proposal (n : Nat) : Option Proposal := GeneralRebaseFiniteReport259.compile 0 atom
 (GeneralVersionReportProjection259.transport n (GeneralNominalPacketSupport.report (packet n)))

theorem proposal_exact (n : Nat) : proposal n = some facts := by
 unfold proposal
 rw [GeneralVersionReportProjection259.actual_report]
 rw [show GeneralNominalPacketSupport.report (packet 0) =
 GeneralDictionaryVersionLoopFamilyPacket238.calculated 0 (allocations 0) (reservations 0) (atoms 0) from
 GeneralDictionaryVersionLoopFamilyPacket238.report_exact ..]
 decide

def observeAt (n : Nat) : Observer facts := fun _ => (proposal n).toList
/-- Finite executable representative from the initial actual report. -/
def run (state : State facts) : Option (State facts) := (proposal 0).bind (tryWrite state)

theorem observe_exact (n : Nat) : observeAt n = fun _ => [facts] := by
 funext state; simp only [observeAt,proposal_exact,Option.toList_some]

theorem run_exact (state : State facts) : run state = tryWrite state facts := by
 simp only [run,proposal_exact,Option.bind_some]

theorem write_initial : write initialState facts = finalState := by apply state_ext; decide

theorem run_first : run initialState = some finalState := by
 rw [run_exact]
 apply (tryWrite_exact ..).mpr
 exact ⟨write_initial.symm,by decide⟩

theorem first_step (n : Nat) : Step (observeAt n) initialState finalState :=
 ⟨facts,by simp [observe_exact],write_initial.symm,by decide⟩

theorem stop (n : Nat) (after : State facts) : ¬ Step (observeAt n) finalState after := by
 intro step
 obtain ⟨proposal,_,equal,changed⟩ := step
 apply changed; rw [equal]; rfl

theorem run_stop : run finalState = none := by rw [run_exact]; rfl

theorem terminating (n : Nat) (state : State facts) : Acc (fun after before => Step (observeAt n) before after) state :=
 accessible _ _

theorem first_unique (n : Nat) (after : State facts) (step : Step (observeAt n) initialState after) : after = finalState := by
 obtain ⟨proposal,member,equal,_⟩ := step
 have same : proposal = facts := by simpa only [observe_exact,List.mem_singleton] using member
 subst proposal
 exact equal.trans write_initial

theorem no_two (first last : Nat) (middle after : State facts) :
 ¬ (Step (observeAt first) initialState middle ∧ Step (observeAt last) middle after) := by
 rintro ⟨one,two⟩
 rw [first_unique first middle one] at two
 exact stop last after two
end Yulang.GeneralVersionRebaseStep259
