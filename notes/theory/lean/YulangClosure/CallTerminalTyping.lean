import YulangClosure.ControlTyping

namespace YulangClosure.Control

/-- With no Call frames, a returned head has the Call's Original result type. -/
theorem returned_call_state_typed
    {W : Type} {sig : Signature} {s : CallState W}
    {result : Ty} {v : TypedCall.Value}
    (ht : CallStateTyped sig s result)
    (hempty : s.frames = []) (hhead : s.head = .returned v) :
    TypedCall.ValueTyped Original.emptyContext v s.resultType := by
  rcases ht with ⟨activeType, htypedHead, hframes, _⟩
  rw [hempty] at hframes
  cases hframes
  rw [hhead] at htypedHead
  cases htypedHead with
  | returned hvalue => exact hvalue

/-- An empty Call stack exposes the payload type and the continuation's
response binder without identifying the independent suffix's result type. -/
theorem requested_call_state_typed
    {W : Type} {sig : Signature} {s : CallState W}
    {result : Ty} {op : TypedCall.OperationInstance}
    {payload : TypedCall.Value} {continuation : TypedCall.Comp}
    (ht : CallStateTyped sig s result)
    (hempty : s.frames = []) (hhead : s.head = .requested op payload continuation) :
    TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
    TypedCall.CompTyped
      (Original.extend Original.emptyContext op.responseType)
      continuation s.resultType := by
  rcases ht with ⟨activeType, htypedHead, hframes, _⟩
  rw [hempty] at hframes
  cases hframes
  rw [hhead] at htypedHead
  cases htypedHead with
  | requested hpayload hcontinuation => exact ⟨hpayload, hcontinuation⟩

end YulangClosure.Control
