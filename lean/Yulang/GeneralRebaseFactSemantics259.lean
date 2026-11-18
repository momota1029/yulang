import Yulang.GeneralVersionRebaseCertificate259
namespace Yulang.GeneralRebaseFactSemantics259
open GeneralRebaseStep258
deriving instance ReflBEq for Fact
deriving instance LawfulBEq for Fact
variable {basis : List Fact}

theorem present_iff (state : State basis) (fact : Fact) :
 fact ∈ present state ↔ fact ∈ basis ∧ fact ∉ state.remaining := by
 simp [present]

theorem present_write (state : State basis) (proposal : Proposal) (fact : Fact) :
 fact ∈ present (write state proposal) ↔
 fact ∈ present state ∨ (fact ∈ basis ∧ fact ∈ proposal) := by
 simp only [present_iff,write,List.mem_filter]
 by_cases inside : fact ∈ basis <;> by_cases remaining : fact ∈ state.remaining <;>
   by_cases proposed : fact ∈ proposal <;> simp_all

def Models (base : α → Prop) (holds : α → Fact → Prop) (state : State basis) (assignment : α) : Prop :=
 base assignment ∧ ∀ fact ∈ present state, holds assignment fact

/-- Exact meaning of the implemented finite write; unsupported facts outside
basis are deliberately ignored, so the basis restriction is explicit. -/
theorem write_exact (base : α → Prop) (holds : α → Fact → Prop)
 (state : State basis) (proposal : Proposal) (assignment : α) :
 Models base holds (write state proposal) assignment ↔
 Models base holds state assignment ∧ ∀ fact ∈ basis, fact ∈ proposal → holds assignment fact := by
 constructor
 · rintro ⟨source,valid⟩
   refine ⟨⟨source,?_⟩,?_⟩
   · intro fact present; exact valid fact ((present_write state proposal fact).mpr (Or.inl present))
   · intro fact inside proposed; exact valid fact ((present_write state proposal fact).mpr (Or.inr ⟨inside,proposed⟩))
 · rintro ⟨⟨source,prior⟩,new⟩
   refine ⟨source,?_⟩
   intro fact present
   rcases (present_write state proposal fact).mp present with old | ⟨inside,proposed⟩
   · exact prior fact old
   · exact new fact inside proposed

theorem initial_exact (base : α → Prop) (holds : α → Fact → Prop) (assignment : α) :
 Models base holds (initial basis) assignment ↔ base assignment := by
 have empty : present (initial basis) = [] := by
   apply List.eq_nil_iff_forall_not_mem.mpr
   intro fact member
   obtain ⟨inside,outside⟩ := (present_iff (initial basis) fact).mp member
   exact outside inside
 simp only [Models,empty,List.not_mem_nil,false_implies,implies_true,and_true]

theorem done_exact (base : α → Prop) (holds : α → Fact → Prop) (assignment : α) :
 Models base holds (done basis) assignment ↔ base assignment ∧ ∀ fact ∈ basis, holds assignment fact := by
 have all : present (done basis) = basis := by simp [present,done]
 simp only [Models,all]
end Yulang.GeneralRebaseFactSemantics259
