import Std

/-! A finite Boolean work calculus. A new fact may reset dirty work; absent
facts strictly decrease. With unchanged facts, exactly one dirty owner is
cleared. No source language or operational-kernel correspondence is claimed. -/
namespace Yulang.GeneralNominalRebaseProgress241

def count : {size : Nat} → (Fin size → Bool) → Nat
 | 0, _ => 0
 | size+1, values => (if values 0 then 1 else 0) + count (fun index : Fin size => values index.succ)

theorem count_le (values : Fin size → Bool) : count values ≤ size := by
 induction size with
 | zero => exact Nat.le_refl _
 | succ size ih =>
   have tail := ih (fun index => values index.succ)
   simp only [count]
   split <;> omega

theorem count_mono (first last : Fin size → Bool)
 (included : ∀ index, first index = true → last index = true) : count first ≤ count last := by
 induction size with
 | zero => exact Nat.le_refl _
 | succ size ih =>
   have tail := ih (fun i => first i.succ) (fun i => last i.succ) (fun i => included i.succ)
   have head := included 0
   simp only [count]
   cases one : first 0 <;> cases two : last 0 <;> simp_all only [Bool.false_eq_true,ite_false,ite_true]
   all_goals omega

theorem count_strict (first last : Fin size → Bool)
 (included : ∀ index, first index = true → last index = true)
 (added : ∃ index, first index = false ∧ last index = true) : count first < count last := by
 induction size with
 | zero => obtain ⟨index,_⟩ := added; exact Fin.elim0 index
 | succ size ih =>
   obtain ⟨index,old,new⟩ := added
   revert old new
   refine Fin.cases ?_ (fun index => ?_) index
   · intro old new
     have tail := count_mono (fun i => first i.succ) (fun i => last i.succ) (fun i => included i.succ)
     simp only [count,old,new,Bool.false_eq_true,ite_false,ite_true]
     omega
   · intro old new
     have tail := ih (fun i => first i.succ) (fun i => last i.succ)
       (fun i => included i.succ) ⟨index,old,new⟩
     have head := included 0
     simp only [count]
     cases one : first 0 <;> cases two : last 0 <;> simp_all only [Bool.false_eq_true,ite_false,ite_true]
     all_goals omega

structure State (factCount ownerCount : Nat) where
 facts : Fin factCount → Bool
 dirty : Fin ownerCount → Bool


def absent (state : State factCount ownerCount) : Nat := factCount - count state.facts

def rank (state : State factCount ownerCount) : Nat := absent state * (ownerCount + 1) + count state.dirty

def drain (state : State factCount ownerCount) (owner : Fin ownerCount) : State factCount ownerCount :=
 ⟨state.facts,fun index => if index = owner then false else state.dirty index⟩

inductive Step : State factCount ownerCount → State factCount ownerCount → Prop
 | fact (before after : State factCount ownerCount)
   (retained : ∀ index, before.facts index = true → after.facts index = true)
   (newFact : ∃ index, before.facts index = false ∧ after.facts index = true) : Step before after
 | clear (before : State factCount ownerCount) (owner : Fin ownerCount)
   (pending : before.dirty owner = true) : Step before (drain before owner)

def LexLess (after before : State factCount ownerCount) : Prop :=
 absent after < absent before ∨ (absent after = absent before ∧ count after.dirty < count before.dirty)

theorem drain_dirty (state : State factCount ownerCount) (owner : Fin ownerCount)
 (pending : state.dirty owner = true) : count (drain state owner).dirty < count state.dirty := by
 apply count_strict
 · intro index held
   change (if index = owner then false else state.dirty index) = true at held
   split at held
   · cases held
   · exact held
 · exact ⟨owner,by simp [drain],pending⟩

variable {factCount ownerCount : Nat} {before after : State factCount ownerCount}

theorem lex_decreases (action : Step before after) : LexLess after before := by
 cases action with
 | fact before retained newFact =>
   have strict := count_strict before.facts after.facts retained newFact
   have bounded := count_le after.facts
   exact Or.inl (by unfold absent; omega)
 | clear owner pending =>
   exact Or.inr ⟨rfl,drain_dirty before owner pending⟩

theorem rank_decreases (action : Step before after) : rank after < rank before := by
 have decrease := lex_decreases action
 have afterBound := count_le after.dirty
 have beforeBound := count_le before.dirty
 unfold rank
 rcases decrease with first | ⟨same,last⟩
 · have mult := Nat.mul_le_mul_right (ownerCount+1) (Nat.succ_le_of_lt first)
   simp only [Nat.succ_mul] at mult
   omega
 · rw [same]
   omega

theorem accessible (state : State factCount ownerCount) : Acc (fun after before => Step before after) state := by
 have auxiliary : ∀ measure, ∀ current : State factCount ownerCount, rank current = measure →
     Acc (fun after before => Step before after) current := by
   intro measure
   induction measure using Nat.strongRecOn with
   | ind measure ih =>
     intro current exactRank
     constructor
     intro next action
     exact ih (rank next) (exactRank ▸ rank_decreases action) next rfl
 exact auxiliary (rank state) state rfl

theorem wellFounded (factCount ownerCount : Nat) :
 WellFounded (fun after before : State factCount ownerCount => Step before after) := ⟨accessible⟩

theorem no_self_step (state : State factCount ownerCount) : ¬ Step state state :=
 fun action => Nat.lt_irrefl _ (rank_decreases action)

end Yulang.GeneralNominalRebaseProgress241
