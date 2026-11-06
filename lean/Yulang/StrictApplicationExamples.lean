import Yulang.StrictApplication
import Yulang.OperationalTypingExamples

/-!
# Strict application retains effects of discarded arguments

The first example is exactly the historical unused-argument expression.
Its old computation-argument result is retained for comparison; the strict
checker and evaluator retain the request. A second expression checks the
observable function-expression, argument, then body order with three distinct
operation keys. These are resolved programs, not parsed surface programs.
-/

namespace Yulang.StrictApplicationExamples

open Directed OperationalTyping
open OperationalTypingExamples (Program atomPure atomEffect unusedArgument)

theorem unused_argument_inferred :
    StrictApplication.infer Env.nil unusedArgument = some atomEffect := rfl

theorem unused_argument_evaluated :
    StrictApplication.eval Env.nil unusedArgument =
      .request (raw 0) 2 (fun _ => .pure (7 : Nat)) := rfl

theorem unused_argument_bounded :
    Computation.BoundedBy [raw 0] (StrictApplication.eval Env.nil unusedArgument) :=
  StrictApplication.closed_inferred_bound unusedArgument atomEffect unused_argument_inferred

theorem unused_argument_not_pure :
    ¬ Computation.BoundedBy [] (StrictApplication.eval Env.nil unusedArgument) := by
  rw [unused_argument_evaluated]
  exact fun bounded => List.not_mem_nil bounded.1

def orderedApplication : Program .atom :=
  .app
    (.letE (.request 1 (.lit 10)) (.lam atomPure (.request 3 (.lit 30))))
    (.request 2 (.lit 20))

def orderedType : CTy 1 Nat .atom := ⟨.atom, [raw 1, raw 2, raw 3]⟩

theorem ordered_application_inferred :
    StrictApplication.infer Env.nil orderedApplication = some orderedType := rfl

theorem ordered_application_evaluated :
    StrictApplication.eval Env.nil orderedApplication =
      .request (raw 1) 10 (fun _ =>
        .request (raw 2) 20 (fun _ =>
          .request (raw 3) 30 (fun response => .pure response))) := rfl

theorem ordered_application_bounded :
    Computation.BoundedBy [raw 1, raw 2, raw 3]
      (StrictApplication.eval Env.nil orderedApplication) :=
  StrictApplication.closed_inferred_bound orderedApplication orderedType ordered_application_inferred

/-- Two-let lowering keeps the argument in its original environment. -/
def capturedArgument : Program .atom :=
  .letE (.lit 42) (.app (.lam atomPure (.var .here)) (.var .here))

theorem captured_argument_evaluated :
    StrictApplication.eval Env.nil capturedArgument = .pure (42 : Nat) := rfl

theorem captured_argument_lowered :
    OperationalTyping.eval Env.nil (StrictApplication.compile capturedArgument) = .pure (42 : Nat) := rfl

end Yulang.StrictApplicationExamples
