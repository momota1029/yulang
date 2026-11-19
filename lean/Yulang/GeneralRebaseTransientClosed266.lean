import Yulang.GeneralRebaseTransientRegression266

namespace Yulang.GeneralRebaseTransientClosed266
open GeneralRebaseStep258
open GeneralRebaseTransientRegression266 (a b basis beginState chooseA chooseB unordered_same order_matters)
open GeneralRebaseClosedObserver259 (Closed)
open GeneralRebaseSettle259 (settle)

theorem closedA : Closed chooseA := by
 intro state proposal member fact included
 unfold chooseA at member
 split at member
 · rcases (List.mem_cons.mp member) with equal | rest
   · cases equal
     cases List.mem_singleton.mp included
     exact List.mem_cons_self
   · have equal := List.mem_singleton.mp rest
     cases equal
     cases List.mem_singleton.mp included
     exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
 · cases member

theorem closedB : Closed chooseB := by
 intro state proposal found
 exact closedA state proposal ((unordered_same state proposal).mpr found)

theorem same_steps (first last : State basis) :
 Step chooseA first last ↔ Step chooseB first last := by
 constructor
 · rintro ⟨proposal,member,square,different⟩
   exact ⟨proposal,(unordered_same first proposal).mp member,square,different⟩
 · rintro ⟨proposal,member,square,different⟩
   exact ⟨proposal,(unordered_same first proposal).mpr member,square,different⟩

/-- Closure and identical unordered transition relations alone do not imply
order-independent settlement for state-dependent observers. -/
theorem counterexample :
 ∃ (one two : Observer basis) (start : State basis),
  Closed one ∧ Closed two ∧ (∀ first last, Step one first last ↔ Step two first last) ∧
  settle one start ≠ settle two start :=
 ⟨chooseA,chooseB,beginState,closedA,closedB,same_steps,order_matters⟩

end Yulang.GeneralRebaseTransientClosed266
