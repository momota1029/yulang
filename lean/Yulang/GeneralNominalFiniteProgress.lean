import Yulang.B4Skeleton

/-! A relation-parametric finite missing-fact measure. Facts may carry semantic
predicates; monotonicity and a newly established listed fact are explicit. -/
namespace Yulang.GeneralNominalFiniteProgress

noncomputable def remaining (holds : State → Fact → Prop) (basis : List Fact) (state : State) : Nat := by
  classical
  exact basis.foldr (fun fact count => if holds state fact then count else count+1) 0

theorem remaining_monotone (holds : State → Fact → Prop) (basis : List Fact)
    (growth : ∀ fact, holds before fact → holds after fact) :
    remaining holds basis after ≤ remaining holds basis before := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons fact rest ih =>
    change (if holds after fact then remaining holds rest after else remaining holds rest after+1) ≤
      (if holds before fact then remaining holds rest before else remaining holds rest before+1)
    by_cases old : holds before fact
    · simp only [old,growth fact old,ite_true]; exact ih
    · by_cases now : holds after fact <;> simp only [old,now,ite_true,ite_false] <;> omega

theorem remaining_decreases (holds : State → Fact → Prop) (basis : List Fact)
    (growth : ∀ fact, holds before fact → holds after fact)
    (member : fact ∈ basis) (old : ¬ holds before fact) (now : holds after fact) :
    remaining holds basis after < remaining holds basis before := by
  classical
  induction basis with
  | nil => cases member
  | cons head rest ih =>
    change (if holds after head then remaining holds rest after else remaining holds rest after+1) <
      (if holds before head then remaining holds rest before else remaining holds rest before+1)
    rcases List.mem_cons.mp member with rfl | member
    · have tail := remaining_monotone holds rest growth
      simp only [old,now,ite_true,ite_false]; omega
    · have tail := ih member
      by_cases was : holds before head
      · simp only [was,growth head was,ite_true]; exact tail
      · by_cases is : holds after head <;> simp only [was,is,ite_true,ite_false] <;> omega

theorem accessible (step : State → State → Prop) (start : State) (holds : State → Fact → Prop) (basis : List Fact)
    (growth : ∀ before after, step before after → ∀ fact, holds before fact → holds after fact)
    (progress : ∀ before after, B4Target.Steps step start before → step before after →
      ∃ fact ∈ basis, ¬ holds before fact ∧ holds after fact) :
    Acc (fun next current => step current next) start := by
  have all : ∀ current, B4Target.Steps step start current → Acc (fun next current => step current next) current := by
    intro current
    induction current using (measure (remaining holds basis)).wf.induction with
    | h current ih =>
      intro path
      refine Acc.intro current ?_
      intro next update
      obtain ⟨fact,member,old,now⟩ := progress current next path update
      exact ih next (remaining_decreases holds basis (growth current next update) member old now) (.tail path update)
  exact all start .refl

end Yulang.GeneralNominalFiniteProgress
