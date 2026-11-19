import Yulang.GeneralRebasePersistentObserver266

namespace Yulang.GeneralRebaseTransientRegression266
open GeneralRebaseStep258
open GeneralRebasePersistentObserver266 (Persistent)
open GeneralRebaseSettle259 (settle)

def a : Fact := .binder 0
def b : Fact := .binder 1
private def resultRemaining {facts : List Fact} :
 Except (List Fact) (State facts) → Option (List Fact)
 | .ok state => some state.remaining
 | .error _ => none

def basis : List Fact := [a,b]
def beginState : State basis := initial basis
def chooseA : Observer basis := fun state => if state.remaining = basis then [[a],[b]] else []
def chooseB : Observer basis := fun state => if state.remaining = basis then [[b],[a]] else []

theorem first_result : resultRemaining (settle chooseA beginState) = some [b] := by decide +kernel
theorem second_result : resultRemaining (settle chooseB beginState) = some [a] := by decide +kernel

/-- These are the same unordered proposals at every state. Reordering still
changes the outcome because the observer can discard still-pending proposals. -/
theorem unordered_same (state : State basis) (proposal : Proposal) :
 proposal ∈ chooseA state ↔ proposal ∈ chooseB state := by
 unfold chooseA chooseB
 split <;> simp_all [or_comm]

theorem order_matters : settle chooseA beginState ≠ settle chooseB beginState := by
 intro equal
 have projected : resultRemaining (settle chooseA beginState) =
    resultRemaining (settle chooseB beginState) := congrArg resultRemaining equal
 rw [first_result,second_result] at projected
 have impossible : (some [b] : Option (List Fact)) ≠ some [a] := by decide +kernel
 exact impossible projected

theorem not_persistent : ¬ Persistent chooseA := by
 intro stable
 let after := write beginState [a]
 have initialB : [b] ∈ chooseA beginState := by decide +kernel
 have pending : b ∈ after.remaining := by decide +kernel
 obtain ⟨later,admitted,_⟩ := stable beginState after (List.filter_sublist ..)
   [b] initialB b (List.mem_singleton_self _) pending
 have none : chooseA after = [] := by decide +kernel
 rw [none] at admitted
 cases admitted

end Yulang.GeneralRebaseTransientRegression266
