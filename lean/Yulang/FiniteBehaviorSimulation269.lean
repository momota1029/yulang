import Yulang.FiniteRankBehavior269

namespace Yulang.FiniteBehaviorSimulation269
open FiniteRankBehavior269 (Code Tracks catalogue)
open GeneralRebaseFiniteSlices268 (exact_slices)

theorem up (h : Tracks label move depth source code) : Tracks label move (depth+1) source code := by
 induction depth generalizing source code with
 | zero =>
   cases code with
   | node view children =>
     obtain ⟨same,empty,terminal⟩ := h
     subst children
     exact ⟨same,fun _ step => False.elim (terminal _ step),fun _ none => False.elim (List.not_mem_nil none)⟩
 | succ d ih =>
   cases code with
   | node view children =>
     obtain ⟨same,complete,sound⟩ := h
     refine ⟨same,?_,?_⟩
     · intro after step
       obtain ⟨branch,inside,atBranch⟩ := complete after step
       exact ⟨branch,inside,ih atBranch⟩
     · intro branch inside
       obtain ⟨after,step,atBranch⟩ := sound branch inside
       exact ⟨after,step,ih atBranch⟩

theorem covers (h : Tracks label move depth source code) (step : move source after) :
 ∃ child ∈ code.children, Tracks label move depth after child := by
 cases depth with
 | zero =>
   cases code with
   | node _ _ => exact False.elim (h.2.2 _ step)
 | succ d =>
   cases code with
   | node _ _ =>
     obtain ⟨child,inside,real⟩ := h.2.1 after step
     exact ⟨child,inside,up real⟩

theorem backs (h : Tracks label move depth source code) (listed : child ∈ code.children) :
 ∃ after, move source after ∧ Tracks label move depth after child := by
 cases depth with
 | zero =>
   cases code with
   | node _ children =>
     have empty : children = [] := h.2.1
     subst children
     cases listed
 | succ d =>
   cases code with
   | node _ _ =>
     obtain ⟨after,step,real⟩ := h.2.2 child listed
     exact ⟨after,step,up real⟩

theorem terminal (h : Tracks label move depth source code) :
 code.children = [] ↔ ∀ after, ¬ move source after := by
 constructor
 · intro empty after step
   obtain ⟨child,member,_⟩ := covers h step
   rw [empty] at member
   cases member
 · intro final
   cases heq : code.children with
   | nil => rfl
   | cons child rest =>
     have listed : child ∈ code.children := heq.symm ▸ List.mem_cons_self
     obtain ⟨after,step,_⟩ := backs h listed
     exact False.elim (final after step)

def Related (label : Source → Label) (move : Source → Source → Prop) (depth : Nat)
 (one two : Source) : Prop :=
 ∃ code, Tracks label move depth one code ∧ Tracks label move depth two code

theorem symmetric (same : Related label move depth one two) : Related label move depth two one := by
 obtain ⟨code,left,right⟩ := same
 exact ⟨code,right,left⟩

theorem label_eq (same : Related label move depth one two) : label one = label two := by
 obtain ⟨code,left,right⟩ := same
 exact (FiniteRankBehavior269.at_label left).trans (FiniteRankBehavior269.at_label right).symm

theorem bisim (same : Related label move depth one two) (step : move one after) :
 ∃ companion, move two companion ∧ Related label move depth after companion := by
 obtain ⟨code,left,right⟩ := same
 obtain ⟨child,listed,real⟩ := covers left step
 obtain ⟨companion,follows,compReal⟩ := backs right listed
 exact ⟨companion,follows,child,real,compReal⟩

end Yulang.FiniteBehaviorSimulation269
