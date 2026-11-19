import Yulang.FiniteBehaviorKeyGraph269

namespace Yulang.FiniteBehaviorCheckedRun269
open FiniteRankBehavior269 (Code Tracks at_label)
open FiniteBehaviorSimulation269 (backs terminal)
open FiniteBehaviorDriver269 (Trace drive)
open FiniteBehaviorKeyGraph269 (Graph rank valid valid_exact compile Realizes tracks)

theorem execute (observe : Source → Label) (move : Source → Source → Prop) (rank : Source → Nat)
 (decrease : ∀ before after, move before after → rank after < rank before)
 (fuel : Nat) (concrete : Source) (code : Code Label) (tracked : Tracks observe move depth concrete code)
 (enough : rank concrete ≤ fuel) :
 let result := drive fuel code
 ∃ finish, Trace move result.1 concrete finish ∧ observe finish = result.2.label ∧
  (∀ next, ¬ move finish next) ∧ result.1 + rank finish ≤ rank concrete := by
 dsimp only
 induction fuel generalizing concrete code with
 | zero =>
   refine ⟨concrete,.nil _,at_label tracked,?_,by simp [drive]⟩
   intro next advance
   have small := decrease concrete next advance
   omega
 | succ fuel ih =>
   cases heq : code.children with
   | nil =>
     refine ⟨concrete,?_,?_,(terminal tracked).mp heq,?_⟩
     · simpa only [drive,heq] using (Trace.nil (step := move) concrete)
     · simpa only [drive,heq] using at_label tracked
     · simp [drive,heq]
   | cons selected rest =>
     have member : selected ∈ code.children := heq.symm ▸ List.mem_cons_self
     obtain ⟨after,chosen,atChild⟩ := backs tracked member
     have smaller := decrease concrete after chosen
     obtain ⟨finish,trace,obs,halt,budget⟩ := ih after selected atChild (by omega)
     refine ⟨finish,?_,?_,halt,?_⟩
     · simp only [drive,heq]
       exact .cons chosen trace
     · simpa only [drive,heq] using obs
     · simp only [drive,heq]
       omega

theorem from_checked_graph (g : Graph n Label) (checked : valid g = true)
 (key : Source → Fin n) (observe : Source → Label) (move : Source → Source → Prop)
 (spec : Realizes g key observe move) (fuel : Nat) (source : Source) (enough : rank g (key source) ≤ fuel) :
 let result := drive fuel (compile g fuel (key source))
 ∃ after, Trace move result.1 source after ∧ observe after = result.2.label ∧
   (∀ future, ¬ move after future) ∧ result.1 + rank g (key after) ≤ rank g (key source) :=
 execute observe move (rank g ∘ key) (fun before after advance =>
   (valid_exact g).mp checked _ _ (spec.forward before after advance)) fuel source _
   (tracks g checked key observe move spec fuel source enough) enough

end Yulang.FiniteBehaviorCheckedRun269
