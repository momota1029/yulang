import Yulang.SourceDataOrderLaws

/-!
# Exact source traces for hidden fields, strict defaults and failure prefixes

These run the actual original AST. Traces distinguish value storage from
evaluation: the hidden string and an unused fallback are visited, while an
earlier failure prevents subsequent visits. Unsupported application remains
an explicit boundary of this data evaluator.
-/

namespace Yulang.SourceDataOrderExamples

open Inference SourceDataRuntime SourceDataOrder

def retainedTail : Expr := .record 1 (.lit .bool) .emptyRecord
def hiddenTail : Expr := .record 0 (.lit .str) retainedTail
def hiddenRecord : Expr := .record 0 (.lit .int) hiddenTail

def hiddenOrder : Trace :=
  [hiddenRecord, .lit .int, hiddenTail, .lit .str, retainedTail, .lit .bool, .emptyRecord]

theorem hidden_trace_and_result :
    run [] hiddenRecord = ⟨hiddenOrder, .ok (.record [(0, .base .int), (1, .base .bool)])⟩ := rfl

theorem hidden_runtime_result :
    SourceDataRuntime.eval [] hiddenRecord = .ok (.record [(0, .base .int), (1, .base .bool)]) := by
  rw [← run_result, hidden_trace_and_result]

def failingHiddenTail : Expr := .record 0 (.var 7) .emptyRecord
def failingHidden : Expr := .record 0 (.lit .int) failingHiddenTail

theorem hidden_failure_is_not_erased :
    run [] failingHidden =
      ⟨[failingHidden, .lit .int, failingHiddenTail, .var 7], .error (.unboundVariable 7)⟩ := rfl

def baseRecord : Expr := .record 0 (.lit .int) .emptyRecord
def presentDefault : Expr := .recordDefault 0 baseRecord (.lit .str)
def absentDefault : Expr := .recordDefault 1 baseRecord (.lit .bool)

theorem present_default_visits_fallback :
    run [] presentDefault =
      ⟨[presentDefault, baseRecord, .lit .int, .emptyRecord, .lit .str],
        .ok (.record [(0, .base .int)])⟩ := rfl

theorem absent_default_appends_after_base :
    run [] absentDefault =
      ⟨[absentDefault, baseRecord, .lit .int, .emptyRecord, .lit .bool],
        .ok (.record [(0, .base .int), (1, .base .bool)])⟩ := rfl

def failingFallback : Expr := .recordDefault 0 baseRecord (.var 9)
def failingBase : Expr := .recordDefault 0 (.var 3) (.lit .str)

theorem existing_field_does_not_suppress_fallback_failure :
    run [] failingFallback =
      ⟨[failingFallback, baseRecord, .lit .int, .emptyRecord, .var 9],
        .error (.unboundVariable 9)⟩ := rfl

theorem base_failure_stops_before_fallback :
    run [] failingBase = ⟨[failingBase, .var 3], .error (.unboundVariable 3)⟩ := rfl

def invalidBase : Expr := .recordDefault 0 (.lit .int) (.lit .str)
def invalidBaseFailingFallback : Expr := .recordDefault 0 (.lit .int) (.var 4)

theorem record_shape_check_follows_fallback :
    run [] invalidBase = ⟨[invalidBase, .lit .int, .lit .str], .error .expectedRecord⟩ := rfl

theorem fallback_error_precedes_record_shape_check :
    run [] invalidBaseFailingFallback =
      ⟨[invalidBaseFailingFallback, .lit .int, .var 4], .error (.unboundVariable 4)⟩ := rfl

def unusedLet : Expr := .letE (.var 7) (.lit .bool)
def twiceRead : Expr := .letE (.lit .int) (.pair (.var 0) (.var 0))
def failingPair : Expr := .pair (.var 5) (.lit .bool)

theorem unused_definition_still_fails :
    run [] unusedLet = ⟨[unusedLet, .var 7], .error (.unboundVariable 7)⟩ := rfl

theorem two_reads_one_definition :
    run [] twiceRead =
      ⟨[twiceRead, .lit .int, .pair (.var 0) (.var 0), .var 0, .var 0],
        .ok (.pair (.base .int) (.base .int))⟩ := rfl

theorem pair_failure_is_left_prefix :
    run [] failingPair = ⟨[failingPair, .var 5], .error (.unboundVariable 5)⟩ := rfl

def unsupportedApplication : Expr := .app (.lam (.lit .int)) (.var 8)

theorem application_is_outside_data_evaluator :
    run [] unsupportedApplication = ⟨[unsupportedApplication], .error .unsupported⟩ := rfl

theorem complete_success_order : (run [] hiddenRecord).trace = writtenOrder hiddenRecord :=
  successful_run_trace [] hiddenRecord _ hidden_runtime_result

end Yulang.SourceDataOrderExamples
