import Yulang.GeneralRebasePositiveMeaning266

namespace Yulang.GeneralRebasePositiveRegression266
open GeneralRebaseStep258
open GeneralRebasePositiveRules266 (Rule observe)
open GeneralRebaseBudget258 (Runs)
open GeneralRebaseSettle259 (settle)

def seed : Fact := .binder 0
def middle : Fact := .binder 1
def finish : Fact := .binder 2
private def resultRemaining {facts : List Fact} :
 Except (List Fact) (State facts) → Option (List Fact)
 | .ok state => some state.remaining
 | .error _ => none

def basis : List Fact := [seed,middle,finish]
def start : State basis := initial basis
def first : State basis := write start [seed]
def second : State basis := write first [middle]
def last : State basis := write second [finish]

def r0 : Rule := ⟨[],seed⟩
def r1 : Rule := ⟨[seed],middle⟩
def r2 : Rule := ⟨[seed,middle],finish⟩
def rules : List Rule := [r2,r1,r0]
def inverse : List Rule := [r0,r1,r2]

theorem observations :
 observe rules start = [[seed]] ∧ observe rules first = [[middle]] ∧
 observe rules second = [[finish]] ∧ observe rules last = [] := by decide +kernel

theorem three_steps : Runs (observe rules) 3 start last := by
 have one : Step (observe rules) start first :=
   ⟨[seed],by rw [observations.1]; exact List.mem_singleton_self _,
     rfl,by decide +kernel⟩
 have two : Step (observe rules) first second :=
   ⟨[middle],by rw [observations.2.1]; exact List.mem_singleton_self _,
     rfl,by decide +kernel⟩
 have three : Step (observe rules) second last :=
   ⟨[finish],by rw [observations.2.2.1]; exact List.mem_singleton_self _,
     rfl,by decide +kernel⟩
 exact .next one (.next two (.next three (.nil _)))

theorem executes :
 resultRemaining (settle (observe rules) start) = some [] := by decide +kernel

theorem settled_state : settle (observe rules) start = .ok last := by
 cases result : settle (observe rules) start with
 | error msg =>
   have impossible := executes
   rw [result] at impossible
   cases impossible
 | ok actual =>
   have exactRemaining := executes
   rw [result] at exactRemaining
   have empty : actual.remaining = [] := Option.some.inj exactRemaining
   have allConsumed : last.remaining = [] := by decide +kernel
   rw [state_ext actual last (empty.trans allConsumed.symm)]

theorem order_reversal : settle (observe inverse) start = .ok last := by
 rw [GeneralRebasePositiveRules266.order_independent inverse rules
    (fun rule => by simp [inverse,rules,or_comm,or_left_comm])]
 exact settled_state

end Yulang.GeneralRebasePositiveRegression266
