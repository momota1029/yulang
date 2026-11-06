import Yulang.JunctionEffects

/-!
# Junction truth, effect ordering, and protected requests

The external operation records a string and resumes with `Unit`. The examples
therefore distinguish short-circuiting and ordered multi-shot evaluation from
an unordered truth-table calculation. All equalities concern actual trees.
-/

namespace Yulang.JunctionEffectExamples

open Directed SignatureRequests JunctionEffects

def external : Signature Unit := ⟨fun _ => String, fun _ => Unit⟩

abbrev Action := Tree 1 (signature external) Bool

def trace (event : String) (next : Action) : Action :=
  .request (raw (.external ())) event (fun _ => next)

def comparison : Action :=
  (chooseAll external ([1, 2, 3] : List Nat)).bind
    (fun left => (chooseAny external ([2, 3, 4] : List Nat)).map
      (fun right => decide (left < right)))

theorem example_from_spec : run external comparison = .pure true :=
  (run_all_any external ([1, 2, 3] : List Nat) ([2, 3, 4] : List Nat)
    (fun left right => decide (left < right))).trans (by rfl)

theorem any_empty_is_false :
    run (n := 1) external ((chooseAny external ([] : List Nat)).map (fun _ => true)) = .pure false :=
  run_any external [] _

theorem all_empty_is_true :
    run (n := 1) external ((chooseAll external ([] : List Nat)).map (fun _ => false)) = .pure true :=
  run_all external [] _

def disjoinStops : Action :=
  .request (raw .disjoin) () (fun selected : Bool =>
    if selected then trace "true branch" (.pure true)
    else trace "unreachable false branch" (.pure false))

def disjoinUsesBoth : Action :=
  .request (raw .disjoin) () (fun selected : Bool =>
    if selected then trace "true branch" (.pure false)
    else trace "false branch" (.pure true))

def conjoinStops : Action :=
  .request (raw .conjoin) () (fun selected : Bool =>
    if selected then trace "true branch" (.pure false)
    else trace "unreachable false branch" (.pure true))

theorem disjoin_stops_after_true :
    run external disjoinStops = trace "true branch" (.pure true) := by rfl

theorem disjoin_runs_true_then_false :
    run external disjoinUsesBoth = trace "true branch" (trace "false branch" (.pure true)) := by rfl

theorem conjoin_stops_after_false :
    run external conjoinStops = trace "true branch" (.pure false) := by rfl

def earlyFinish : Action :=
  (finish (Value := Nat) external false).bind
    (fun _ => trace "unreachable after ret" (.pure true))

theorem ret_discards_remaining_code : run external earlyFinish = .pure false := by rfl

def protectedChoice : Action :=
  .request (release (0 : Fin 1) allowNone (raw .disjoin)) () (fun selected : Bool => .pure selected)

theorem negative_debt_preserved : run external protectedChoice = protectedChoice := by rfl

/-- This observer handles only the external trace operation. A residual
junction request is reported as unresolved instead of receiving a fake reply. -/
def observe : Action → List String × Option Bool
  | .pure value => ([], some value)
  | .request ⟨.external _, _⟩ event resume =>
      let rest := observe (resume ())
      (event :: rest.1, rest.2)
  | .request _ _ _ => ([], none)

end Yulang.JunctionEffectExamples
