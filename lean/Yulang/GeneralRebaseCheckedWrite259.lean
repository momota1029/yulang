import Yulang.GeneralDictionaryRebaseFacts259
namespace Yulang.GeneralRebaseCheckedWrite259
open GeneralRebaseStep258
open GeneralRebaseFactSemantics259
variable {basis : List Fact}

def outside (basis : List Fact) (proposal : Proposal) : List Fact :=
 proposal.filter (fun fact => !basis.contains fact)

/-- Error means an unsupported internal fact, not a language-level rejection.
No partial write is performed when a proposed fact lies outside the fixed basis. -/
def commit (state : State basis) (proposal : Proposal) : Except (List Fact) (Option (State basis)) :=
 let missing := outside basis proposal
 if missing = [] then .ok (tryWrite state proposal) else .error missing

theorem outside_member (fact : Fact) (proposal : Proposal) :
 fact ∈ outside basis proposal ↔ fact ∈ proposal ∧ fact ∉ basis := by simp [outside]

theorem closed_iff (proposal : Proposal) : outside basis proposal = [] ↔ proposal ⊆ basis := by
 constructor
 · intro empty fact member
   by_cases included : fact ∈ basis
   · exact included
   · have present := (outside_member fact proposal).mpr ⟨member,included⟩
     rw [empty] at present
     cases present
 · intro included
   apply List.eq_nil_iff_forall_not_mem.mpr
   intro fact member
   obtain ⟨proposed,missing⟩ := (outside_member fact proposal).mp member
   exact missing (included proposed)

theorem accepted (state : State basis) (proposal : Proposal) (result : Option (State basis)) :
 commit state proposal = .ok result ↔ proposal ⊆ basis ∧ tryWrite state proposal = result := by
 unfold commit
 dsimp only
 split
 · rename_i empty
   simp only [Except.ok.injEq]
   exact ⟨fun equal => ⟨(closed_iff proposal).mp empty,equal⟩,And.right⟩
 · rename_i missing
   constructor
   · intro impossible; cases impossible
   · rintro ⟨closed,_⟩; exact False.elim (missing ((closed_iff proposal).mpr closed))

theorem supported (state : State basis) (proposal : Proposal) (closed : proposal ⊆ basis) :
 commit state proposal = .ok (tryWrite state proposal) := (accepted ..).mpr ⟨closed,rfl⟩

/-- Every reported unsupported fact really occurs in the proposal and lies
outside basis. The error path cannot carry a newly written state. -/
theorem unsupported (state : State basis) (proposal : Proposal) (missing : List Fact)
 (failed : commit state proposal = .error missing) :
 missing ≠ [] ∧ ∀ fact ∈ missing, fact ∈ proposal ∧ fact ∉ basis := by
 unfold commit at failed
 dsimp only at failed
 split at failed
 · cases failed
 · rename_i nonempty
   cases Except.error.inj failed
   exact ⟨nonempty,fun fact member => (outside_member fact proposal).mp member⟩

theorem accepted_models (base : α → Prop) (holds : α → Fact → Prop)
 (before after : State basis) (proposal : Proposal) (installed : commit before proposal = .ok (some after))
 (assignment : α) : Models base holds after assignment ↔
 Models base holds before assignment ∧ ∀ fact ∈ proposal, holds assignment fact := by
 obtain ⟨closed,run⟩ := (accepted ..).mp installed
 obtain ⟨rfl,_⟩ := (tryWrite_exact ..).mp run
 rw [write_exact]
 constructor
 · rintro ⟨old,new⟩; exact ⟨old,fun fact member => new fact (closed member) member⟩
 · rintro ⟨old,new⟩; exact ⟨old,fun fact _ member => new fact member⟩
end Yulang.GeneralRebaseCheckedWrite259
