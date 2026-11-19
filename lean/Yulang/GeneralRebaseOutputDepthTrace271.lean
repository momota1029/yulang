import Yulang.GeneralRebaseOutputDepthSuccessor271

namespace Yulang.GeneralRebaseOutputDepthTrace271
open GeneralDictionaryOutputDepth252 (registry root initial)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseOutputDepthSuccessor271 (owner output support every_weak source_weak projected_install)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Stutter Lull Weak lull_same)
open B4Target (Steps)

abbrev roles := GeneralDictionaryOutputDepth252.roles

def observe (s : State roles) := project [owner] [output] s

theorem at_zero (a b : State roles) (zero : (observe a).remaining = [])
 (actual : Step registry root a b) : Stutter registry root [owner] [output] a b := by
 refine ⟨actual,?_⟩
 change observe b = observe a
 by_cases unchanged : observe b = observe a
 · exact unchanged
 · have impossible := GeneralRebaseSourceProjection264.strict_decrease [owner] [output] actual unchanged
   change (observe b).remaining.length < (observe a).remaining.length at impossible
   rw [zero] at impossible
   exact False.elim ((Nat.not_lt_zero _) impossible)

theorem after_weak_is_silent (first : State roles)
 (progress : Weak registry root [owner] [output] initial first)
 (path : Steps (Step registry root) first last) :
 Lull registry root [owner] [output] first last ∧ (observe last).remaining = [] := by
 induction path with
 | refl => exact ⟨.refl,every_weak _ progress⟩
 | @tail current nextState _ next ih =>
   have silent := at_zero _ _ ih.2 next
   exact ⟨.tail ih.1 silent,(congrArg GeneralRebaseStep258.State.remaining silent.2).trans ih.2⟩

theorem classify_all (last : State roles) (path : Steps (Step registry root) initial last) :
 Lull registry root [owner] [output] initial last ∨
 ∃ hit, Weak registry root [owner] [output] initial hit ∧
   Lull registry root [owner] [output] hit last ∧ (observe last).remaining = [] := by
 induction path with
 | refl => exact Or.inl .refl
 | @tail current nextState _ next ih =>
   rcases ih with quiet | ⟨hit,progress,suffix,zero⟩
   · by_cases changed : observe nextState = observe current
     · exact Or.inl (.tail quiet ⟨next,changed⟩)
     · have step : Weak registry root [owner] [output] initial _ := ⟨_,quiet,next,changed⟩
       exact Or.inr ⟨_,step,.refl,every_weak _ step⟩
   · have silent := at_zero _ _ zero next
     exact Or.inr ⟨hit,progress,.tail suffix silent,(congrArg GeneralRebaseStep258.State.remaining silent.2).trans zero⟩

theorem no_followup (target : State roles) (after : Steps (Step registry root) installed target) :
 observe target = GeneralRebaseStep258.done support := by
 have hit := (after_weak_is_silent installed source_weak after).2
 exact GeneralRebaseStep258.state_ext _ _ hit

end Yulang.GeneralRebaseOutputDepthTrace271
