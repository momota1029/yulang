import Yulang.GeneralDictionaryCompletedReadback258
namespace Yulang.GeneralRebaseStep258

/-- Fixed owner slots, fixed basis atoms and fixed binder facts. The finite
basis is supplied by a source layout; its general producer is still open. -/
inductive Fact where
 | lower (owner atom : Nat)
 | upper (owner atom : Nat)
 | binder (index : Nat)
 | installed (owner : Nat)
 deriving DecidableEq, BEq, Repr

structure State (basis : List Fact) where
 remaining : List Fact
 canonical : remaining.Sublist basis

variable {basis : List Fact}

theorem state_ext (first last : State basis) (same : first.remaining = last.remaining) : first = last := by
 cases first; cases last; cases same; rfl

def initial (basis : List Fact) : State basis := ⟨basis,List.Sublist.refl _⟩
def done (basis : List Fact) : State basis := ⟨[],List.nil_sublist _⟩
abbrev Proposal := List Fact

def write (state : State basis) (proposal : Proposal) : State basis :=
 ⟨state.remaining.filter (fun fact => !proposal.contains fact),
   (List.filter_sublist ..).trans state.canonical⟩

/-- An observer supplies actual eligible proposals. Generic source inspection
and its soundness/completeness bridge are NOT hidden in this definition. -/
abbrev Observer (basis : List Fact) := State basis → List Proposal

def tryWrite (state : State basis) (proposal : Proposal) : Option (State basis) :=
 if (write state proposal).remaining = state.remaining then none else some (write state proposal)

def Step (observe : Observer basis) (before after : State basis) : Prop :=
 ∃ proposal ∈ observe before, after = write before proposal ∧ after.remaining ≠ before.remaining

theorem tryWrite_exact (state : State basis) (proposal : Proposal) (after : State basis) :
 tryWrite state proposal = some after ↔ after = write state proposal ∧ after.remaining ≠ state.remaining := by
 unfold tryWrite
 split
 · rename_i same
   constructor
   · intro impossible; cases impossible
   · rintro ⟨rfl,different⟩; exact False.elim (different same)
 · rename_i different
   constructor
   · intro equal; cases Option.some.inj equal; exact ⟨rfl,different⟩
   · rintro ⟨rfl,_⟩; rfl

theorem filter_strict (values : List Fact) (keep : Fact → Bool)
 (changed : values.filter keep ≠ values) : (values.filter keep).length < values.length := by
 induction values with
 | nil => exact False.elim (changed rfl)
 | cons first rest ih =>
   by_cases kept : keep first = true
   · have tail : rest.filter keep ≠ rest := by
       intro equal
       apply changed
       simp only [List.filter_cons,kept,ite_true,equal]
     simpa only [List.filter_cons,kept,ite_true,List.length_cons] using Nat.succ_lt_succ (ih tail)
   · have small := List.length_filter_le keep rest
     simp only [List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte, List.length_cons]
     omega

theorem decreases (observe : Observer basis) (step : Step observe before after) :
 after.remaining.length < before.remaining.length := by
 obtain ⟨proposal,_,rfl,changed⟩ := step
 exact filter_strict before.remaining _ changed

/-- Structural termination of the novelty-gated finite write relation.
Language faithfulness still requires a source-derived correct observer. -/
theorem accessible (observe : Observer basis) (state : State basis) :
 Acc (fun after before => Step observe before after) state := by
 generalize equal : state.remaining.length = measure
 induction measure using Nat.strongRecOn generalizing state with
 | ind measure ih =>
   apply Acc.intro
   intro after step
   have smaller := decreases observe step
   rw [equal] at smaller
   exact ih _ smaller after rfl

theorem no_self_step (observe : Observer basis) (state : State basis) : ¬ Step observe state state := by
 intro step
 exact Nat.lt_irrefl _ (decreases observe step)

def present (state : State basis) : List Fact := basis.filter (fun fact => !state.remaining.contains fact)

def lowerAtoms (state : State basis) (owner : Nat) : List Nat := (present state).filterMap fun fact =>
 match fact with | .lower key atom => if key = owner then some atom else none | _ => none

def upperAtoms (state : State basis) (owner : Nat) : List Nat := (present state).filterMap fun fact =>
 match fact with | .upper key atom => if key = owner then some atom else none | _ => none

def binderFacts (state : State basis) : List Nat := (present state).filterMap fun fact =>
 match fact with | .binder index => some index | _ => none
end Yulang.GeneralRebaseStep258
