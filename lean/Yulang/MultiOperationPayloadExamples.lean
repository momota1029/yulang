import Yulang.MultiOperationPayloadInference

/-! Q1 regressions: partial dispatch, retained rows, a guarded wildcard,
two refutable arms, shallow resumption and decision-41 rejection. -/

namespace Yulang.MultiOperationPayloadExamples

open Directed OperationalTyping MultiOperationPayloadHandlers

def trueOnly : Fin 1 → Arm Nat Bool := fun _ => ⟨0, .test id, none⟩

def guardedWildcard : Fin 1 → Arm Nat Bool :=
  fun _ => ⟨0, .irrefutable, some (fun _ => true)⟩

def bothBooleans : Fin 2 → Arm Nat Bool :=
  fun index => ⟨0, .test (if index.val = 0 then id else Bool.not), none⟩

def wildcard : Fin 1 → Arm Nat Bool := fun _ => ⟨0, .irrefutable, none⟩

theorem true_selected : select trueOnly (raw (n := n) 0) true = some 0 := by
  simp [select, trueOnly, eligible, Capturable, raw, Arm.matches, PayloadPattern.matches,
    List.finRange, List.ofFn_succ]

theorem false_missed : select trueOnly (raw (n := n) 0) false = none := by
  simp [select, trueOnly, eligible, Capturable, raw, Arm.matches, PayloadPattern.matches,
    List.finRange, List.ofFn_succ]

theorem guarded_wildcard_not_subtracted : removedKeys guardedWildcard = [] := by decide

/-- Unlike case coverage (Q8), collectively exhaustive refutable handler
arms still do not certify key subtraction (Q1). -/
theorem refutable_cover_not_subtracted : removedKeys bothBooleans = [] := by decide

theorem boolean_cover_dispatches (payload : Bool) :
    ∃ index, select bothBooleans (raw (n := n) 0) payload = some index := by
  cases payload
  · refine ⟨1, ?_⟩
    simp [select, bothBooleans, eligible, Capturable, raw, Arm.matches, PayloadPattern.matches,
      List.finRange, List.ofFn_succ]
  · refine ⟨0, ?_⟩
    simp [select, bothBooleans, eligible, Capturable, raw, Arm.matches, PayloadPattern.matches,
      List.finRange, List.ofFn_succ]

theorem false_request_forwarded (resume : Bool → Computation n Nat Bool Bool Bool) :
    handle trueOnly Computation.pure (fun _ _ _ => .pure true)
      (.request (raw 0) false resume) =
      .request (raw 0) false
        (fun response => handle trueOnly Computation.pure (fun _ _ _ => .pure true) (resume response)) :=
  handle_missed _ _ _ _ _ _ false_missed

/-- Even a second matching request escapes after the first arm resumes. -/
theorem true_resume_is_shallow (resume : Bool → Computation n Nat Bool Bool Bool) (response : Bool) :
    handle trueOnly Computation.pure (fun _ _ continuation => continuation response)
      (.request (raw 0) true resume) = resume response :=
  handle_selected _ _ _ _ _ _ 0 true_selected

def partialProgram (payload : Bool) : MultiOperationHandlerTyping.Expr n Nat Bool [] .atom :=
  .partialHandler trueOnly .atom (.request 0 (.lit payload)) (.var .here) (fun _ => .lit true)

def totalProgram (payload : Bool) : MultiOperationHandlerTyping.Expr n Nat Bool [] .atom :=
  .partialHandler wildcard .atom (.request 0 (.lit payload)) (.var .here) (fun _ => .lit true)

theorem partial_infers_retained_key (payload : Bool) :
    MultiOperationHandlerTyping.infer Env.nil (partialProgram (n := n) payload) =
      some ⟨.atom, [raw 0]⟩ := by
  simp [partialProgram, MultiOperationHandlerTyping.infer,
    MultiOperationHandlerTyping.Expr.lit, MultiOperationHandlerTyping.Expr.var,
    StrictApplication.infer, StrictApplication.compile, OperationalTyping.infer,
    MultiOperationHandlerTyping.collectOptions, MultiOperationHandlerTyping.collectRows,
    removedKeys, trueOnly, Arm.total, residual, Capturable, CTy.pure, checkV,
    List.finRange, List.ofFn_succ, operationTypes]

theorem total_infers_empty_row (payload : Bool) :
    MultiOperationHandlerTyping.infer Env.nil (totalProgram (n := n) payload) =
      some ⟨.atom, []⟩ := by
  simp [totalProgram, MultiOperationHandlerTyping.infer,
    MultiOperationHandlerTyping.Expr.lit, MultiOperationHandlerTyping.Expr.var,
    StrictApplication.infer, StrictApplication.compile, OperationalTyping.infer,
    MultiOperationHandlerTyping.collectOptions, MultiOperationHandlerTyping.collectRows,
    removedKeys, wildcard, Arm.total, residual, Capturable, raw, CTy.pure, checkV,
    List.finRange, List.ofFn_succ, operationTypes]

theorem partial_typed (payload : Bool) :
    MultiOperationHandlerTyping.Typing Env.nil (partialProgram (n := n) payload) ⟨.atom, [raw 0]⟩ :=
  (MultiOperationHandlerTyping.infer_exact _ _ _).mp (partial_infers_retained_key payload)

theorem partial_operationally_valid (payload : Bool) :
    Valid (⟨.atom, [raw 0]⟩ : CTy n Nat .atom)
      (MultiOperationHandlerTyping.eval Env.nil (partialProgram payload)) :=
  MultiOperationHandlerTyping.inferred_operationally_valid _ _ _
    (partial_infers_retained_key payload) Env.nil (fun index => nomatch index)

theorem partial_false_exposes_request :
    MultiOperationHandlerTyping.eval Env.nil (partialProgram (n := n) false) =
      .request (raw 0) false (fun response => .pure response) := by
  simp [partialProgram, MultiOperationHandlerTyping.eval,
    MultiOperationHandlerTyping.Expr.lit, MultiOperationHandlerTyping.Expr.var,
    StrictApplication.eval,
    handle, false_missed, Computation.bind, Env.cons, Env.nil]

theorem total_returns_from_checker (payload : Bool) :
    ∃ value, MultiOperationHandlerTyping.eval Env.nil (totalProgram (n := n) payload) = .pure value := by
  obtain ⟨value, returned, _⟩ := MultiOperationHandlerTyping.closed_empty_row_returns
    (totalProgram (n := n) payload) .atom
    ((MultiOperationHandlerTyping.infer_exact _ _ _).mp (total_infers_empty_row payload))
  exact ⟨value, returned⟩

def deniedPartial (payload : Bool) : MultiOperationPayloadInference.Handler n Nat Bool [] .atom where
  input := .atom
  count := 1
  permission := allowNone
  arms := trueOnly
  target := .atom
  action := .request 0 (.lit payload)
  onReturn := .var .here
  onArm := fun _ => .lit true

/-- An unmatched payload does not make an unpermitted written arm legal. -/
theorem denied_partial_rejected (payload : Bool) :
    MultiOperationPayloadInference.infer Env.nil (deniedPartial (n := n) payload) = none :=
  MultiOperationPayloadInference.denied_arm_rejected _ _ ⟨0, by change 0 < 1; decide⟩ rfl

end Yulang.MultiOperationPayloadExamples
