import Yulang.GeneralRebaseCheckedFixtures259
namespace Yulang.GeneralRebaseScheduler259
open GeneralRebaseStep258 GeneralRebaseCheckedWrite259
variable {basis : List Fact}

/-- Skip already installed proposals, but report the first unsupported one.
A later proposal is inspected only if no earlier proposal made progress. -/
def scan (state : State basis) : List Proposal → Except (List Fact) (Option (State basis))
 | [] => .ok none
 | proposal :: rest =>
   match commit state proposal with
   | .error missing => .error missing
   | .ok none => scan state rest
   | .ok (some after) => .ok (some after)

def next (observe : Observer basis) (state : State basis) := scan state (observe state)

theorem scan_installed (state : State basis) (proposals : List Proposal) (after : State basis)
 (result : scan state proposals = .ok (some after)) :
 ∃ proposal ∈ proposals, commit state proposal = .ok (some after) := by
 induction proposals with
 | nil => cases result
 | cons proposal rest ih =>
   unfold scan at result
   split at result
   · cases result
   · obtain ⟨found,member,valid⟩ := ih result
     exact ⟨found,List.mem_cons_of_mem _ member,valid⟩
   · rename_i installed equal
     cases Except.ok.inj result
     exact ⟨proposal,List.mem_cons_self,equal⟩

theorem next_step (observe : Observer basis) (before after : State basis)
 (result : next observe before = .ok (some after)) : Step observe before after := by
 obtain ⟨proposal,member,installed⟩ := scan_installed before (observe before) after result
 have run := ((accepted before proposal (some after)).mp installed).2
 obtain ⟨same,different⟩ := (tryWrite_exact before proposal after).mp run
 exact ⟨proposal,member,same,different⟩

theorem scan_none (state : State basis) (proposals : List Proposal) :
 scan state proposals = .ok none ↔ ∀ proposal ∈ proposals, commit state proposal = .ok none := by
 induction proposals with
 | nil => simp [scan]
 | cons proposal rest ih =>
   simp only [scan]
   split
   · rename_i missing failed
     constructor
     · intro impossible; cases impossible
     · intro all; have same := all proposal List.mem_cons_self; rw [failed] at same; cases same
   · rename_i unchanged
     rw [ih]
     constructor
     · intro all found member
       rcases List.mem_cons.mp member with rfl | member
       · exact unchanged
       · exact all found member
     · intro all found member; exact all found (List.mem_cons_of_mem _ member)
   · rename_i after changed
     constructor
     · intro impossible; cases impossible
     · intro all; have same := all proposal List.mem_cons_self; rw [changed] at same; cases same

theorem terminal (observe : Observer basis) (state : State basis)
 (result : next observe state = .ok none) : ∀ after, ¬ Step observe state after := by
 have all := (scan_none state (observe state)).mp result
 intro after ⟨proposal,member,same,different⟩
 have noWrite := ((accepted state proposal none).mp (all proposal member)).2
 have writes := (tryWrite_exact state proposal after).mpr ⟨same,different⟩
 rw [noWrite] at writes
 cases writes
end Yulang.GeneralRebaseScheduler259
