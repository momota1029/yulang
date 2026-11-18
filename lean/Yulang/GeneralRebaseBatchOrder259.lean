import Yulang.GeneralRebaseBatchTerminal259
namespace Yulang.GeneralRebaseBatchOrder259
open GeneralRebaseStep258 GeneralRebaseWriteAlgebra259 GeneralRebaseSettle259
variable {basis : List Fact}

theorem write_membership (state : State basis) (first last : Proposal)
 (same : ∀ fact, fact ∈ first ↔ fact ∈ last) : write state first = write state last := by
 apply state_ext
 change state.remaining.filter _ = state.remaining.filter _
 congr 1
 funext fact
 have equal := same fact
 by_cases one : fact ∈ first <;> by_cases two : fact ∈ last <;> simp_all

theorem batch_membership (state : State basis) (first last : List Proposal)
 (same : ∀ proposal, proposal ∈ first ↔ proposal ∈ last) : batch state first = batch state last := by
 rw [batch_exact,batch_exact]
 apply write_membership
 intro fact
 constructor
 · intro member
   obtain ⟨proposal,outer,inner⟩ := List.mem_flatten.mp member
   exact List.mem_flatten.mpr ⟨proposal,(same proposal).mp outer,inner⟩
 · intro member
   obtain ⟨proposal,outer,inner⟩ := List.mem_flatten.mp member
   exact List.mem_flatten.mpr ⟨proposal,(same proposal).mpr outer,inner⟩

/-- Order and duplicate independence of a fixed supported proposal batch.
No confluence claim is made for arbitrary state-dependent observation. -/
theorem settle_membership (state : State basis) (first last : List Proposal)
 (same : ∀ proposal, proposal ∈ first ↔ proposal ∈ last)
 (closed : ∀ proposal ∈ first, proposal ⊆ basis) :
 settle (fun _ => first) state = settle (fun _ => last) state := by
 rw [GeneralRebaseBatchTerminal259.settle_batch state first closed,
   GeneralRebaseBatchTerminal259.settle_batch state last (fun proposal member => closed proposal ((same proposal).mpr member))]
 exact congrArg Except.ok (batch_membership state first last same)

theorem swap (state : State basis) (first last : Proposal)
 (one : first ⊆ basis) (two : last ⊆ basis) :
 settle (fun _ => [first,last]) state = settle (fun _ => [last,first]) state := by
 apply settle_membership
 · intro proposal; simp only [List.mem_cons,List.not_mem_nil,or_false]; exact or_comm
 · intro proposal member
   rcases List.mem_cons.mp member with rfl | member
   · exact one
   · cases List.mem_singleton.mp member; exact two

theorem duplicate (state : State basis) (proposal : Proposal) (closed : proposal ⊆ basis) :
 settle (fun _ => [proposal,proposal]) state = settle (fun _ => [proposal]) state := by
 apply settle_membership
 · intro fact; simp
 · intro found member
   have same : found = proposal := by simpa using member
   subst found; exact closed
end Yulang.GeneralRebaseBatchOrder259
