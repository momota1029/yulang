import Yulang.FiniteBehaviorClassifier269

namespace Yulang.FiniteBehaviorDriver269
open FiniteRankBehavior269 (Code)
open FiniteBehaviorClassifier269 (Basis classify child_iff terminal_iff)

def Advances (first last : Code Label) : Prop := last ∈ first.children

inductive Trace (step : α → α → Prop) : Nat → α → α → Prop where
 | nil (s : α) : Trace step 0 s s
 | cons : step first middle → Trace step n middle last → Trace step (n+1) first last

theorem reflect_trace (basis : Basis Source Label)
 (abstractPath : Trace Advances count code last) (source : Source) (known : classify basis source = code) :
 ∃ finish, Trace basis.move count source finish ∧ classify basis finish = last := by
 induction abstractPath generalizing source with
 | nil => exact ⟨source,.nil _,known⟩
 | @cons first middle endCode n next _ ih =>
   have member : middle ∈ (classify basis source).children := known.symm ▸ next
   obtain ⟨after,progress,reps⟩ := (child_iff basis source middle).mp member
   obtain ⟨finish,path,exactCode⟩ := ih after reps
   exact ⟨finish,.cons progress path,exactCode⟩

theorem simulate_trace (basis : Basis Source Label)
 (source : Trace basis.move count first last) :
 Trace Advances count (classify basis first) (classify basis last) := by
 induction source with
 | nil => exact .nil _
 | cons next _ ih => exact .cons ((child_iff basis _ _).mpr ⟨_,next,rfl⟩) ih

/-- Consume a standalone behavior code, repeatedly choosing its first child.
With a certified rank bound this returns a genuinely weak-terminal outcome.
No concrete witness is computed by this recursion. -/
def drive : Nat → Code Label → Nat × Code Label
 | 0,s => (0,s)
 | fuel+1,s =>
   match s.children with
   | [] => (0,s)
   | c :: _ =>
     let result := drive fuel c
     (result.1+1,result.2)

theorem drive_correct (basis : Basis Source Label) (fuel : Nat) (source : Source)
 (enough : basis.rank source ≤ fuel) :
 let result := drive fuel (classify basis source)
 ∃ final, Trace basis.move result.1 source final ∧ classify basis final = result.2 ∧
   (∀ after, ¬ basis.move final after) ∧ result.1 + basis.rank final ≤ basis.rank source := by
 dsimp only
 induction fuel generalizing source with
 | zero =>
   refine ⟨source,.nil _,rfl,?_,by simp [drive]⟩
   intro after step
   have strict := basis.decreases source after step
   omega
 | succ fuel ih =>
   cases choice : (classify basis source).children with
   | nil =>
     refine ⟨source,?_,?_,(terminal_iff basis source).mp choice,?_⟩ <;> simp [drive,choice]
     exact .nil _
   | cons child rest =>
     have member : child ∈ (classify basis source).children := choice.symm ▸ List.mem_cons_self
     obtain ⟨after,step,atChild⟩ := (child_iff basis source child).mp member
     have strict := basis.decreases source after step
     obtain ⟨final,trace,atFinal,terminal,budget⟩ := ih after (by omega)
     refine ⟨final,?_,?_,terminal,?_⟩
     · simp only [drive,choice,←atChild]
       exact .cons step trace
     · simpa only [drive,choice,←atChild] using atFinal
     · simp only [drive,choice,←atChild]
       omega

end Yulang.FiniteBehaviorDriver269
