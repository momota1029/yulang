import Yulang.LoopEffectExamples

open Yulang.LoopEffects Yulang.LoopEffectExamples

private def check (name : String) (actual expected : List Event × Nat × Status) : IO Unit := do
  if actual = expected then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}: {repr actual}; expected {repr expected}")

def main : IO Unit := do
  check "redo retains current state and the first event"
    (observe (machine.run 3 initial)) ([.tick 7 0 1], 1, .exhausted)
  check "redo same item, next advances, last ends traversal"
    (observe (machine.run 9 initial)) ([.tick 7 0 1, .tick 7 1 2, .tick 8 2 3], 3, .returned)
  check "resuming a finite prefix appends effects without replay"
    (observe (machine.extend 6 (machine.run 3 initial)))
    ([.tick 7 0 1, .tick 7 1 2, .tick 8 2 3], 3, .returned)
  check "protected redo remains pending with unchanged state"
    (observe (machine.run 20 protectedRedo)) ([], 11, .blocked)
  check "external interpreter sees signed occurrence"
    (observe (machine.run 20 protectedExternal)) ([], 11, .blocked)
  check "normal finite traversal returns unit and discards Bool body values"
    (observe ((pureMachine (fun item => item % 2 = 0)).run 10 ⟨17, .pull [1, 2, 3, 4]⟩))
    ([], 17, .returned)
  check "last exits an unbounded cursor"
    (observe (unbounded.run 9 ⟨12, .pull 0⟩)) ([], 12, .returned)
  check "infinite redo consumes its budget without inventing completion"
    (observe (perpetual.run 100 perpetualStart)) ([], 23, .exhausted)
