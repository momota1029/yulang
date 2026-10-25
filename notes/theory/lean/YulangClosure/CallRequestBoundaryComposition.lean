import YulangClosure.CallRequestBoundary
import YulangClosure.CallUnwindTypingRepair
import YulangClosure.CallCaptureResponse

namespace YulangClosure.Control

/-- A request reached by an actual typed Call prefix has a realized, exact
boundary. An explicitly supplied typed response produces the typed plugging
of the captured frames. This does not assert source/native response existence. -/
theorem initial_call_request_boundary_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {s : CallState W}
    {op : TypedCall.OperationInstance} {payload response : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (hv : TypedCall.ValueTyped Original.emptyContext response op.responseType) :
    let t := s.requestBoundary md (s.frames.length + 1)
    YulangClosure.Prefix (CallControlStep md) (n + (s.frames.length + 1))
      (CallState.initial term world suffix) t ∧
    CallStateTyped sig t result ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    t.frames = [] ∧
    t.resultType = term.resultType ∧
    t.literalSuffix = suffix ∧
    TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
    TypedCall.CompTyped (Original.extend Original.emptyContext op.responseType)
      (CallState.captureFrames s.frames k) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k) response) term.resultType ∧
    plugResponse (CallState.captureFrames s.frames k) response =
      TypedCall.plugFrames s.frames (plugResponse k response) ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames (plugResponse k response)) term.resultType := by
  let t := s.requestBoundary md (s.frames.length + 1)
  have hsegment : YulangClosure.Prefix (CallControlStep md) (s.frames.length + 1) s t :=
    (call_request_state_prefix_iff md hhead _ t).2 ⟨Nat.le_refl _, rfl⟩
  have hfull := call_prefix_append hp hsegment
  have hstart := call_state_typed_start term world suffix hsuffix
  obtain ⟨ht, hresult, hliteral⟩ := call_state_typed_prefix_preservation hstart hfull
  have heq := call_request_state_boundary_complete md hhead
  have hrequested : t.head = .requested op payload (CallState.captureFrames s.frames k) := by
    exact congrArg CallState.head heq
  have hempty : t.frames = [] := congrArg CallState.frames heq
  have hterminal := requested_call_state_typed ht hempty hrequested
  have hcaptured : TypedCall.CompTyped
      (Original.extend Original.emptyContext op.responseType)
      (CallState.captureFrames s.frames k) term.resultType := by
    simpa only [hresult, CallState.initial] using hterminal.2
  have hresponse : TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k) response) term.resultType :=
    plugResponse_captureFrames_typed (frames := []) .nil hcaptured hv
  have hcancellation := plugResponse_captureFrames s.frames k response
  have hplugged : TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames (plugResponse k response)) term.resultType := by
    rw [← hcancellation]
    exact hresponse
  exact ⟨hfull, ht, hrequested, hempty, hresult, hliteral,
    hterminal.1, hcaptured, hresponse, hcancellation, hplugged⟩

/-- Every actual completed request trace has that same boundary and typed
response result, even when its terminal operation/payload/code are unspecified. -/
theorem actual_call_request_completed_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n m : Nat} {s t : CallState W}
    {op : TypedCall.OperationInstance} {payload response : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (hpost : YulangClosure.Prefix (CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k')
    (hv : TypedCall.ValueTyped Original.emptyContext response op.responseType) :
    m = s.frames.length + 1 ∧
    t = s.requestBoundary md (s.frames.length + 1) ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k) response) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames (plugResponse k response)) term.resultType := by
  have hlength := (call_request_completion_iff hhead hpost).1 hcomplete
  have hexact := ((call_request_state_prefix_iff md hhead m t).1 hpost).2
  rw [hlength] at hexact
  obtain ⟨_, htyped, hrequested, _, _, hliteral, _, _, hresponse, _, hplugged⟩ :=
    initial_call_request_boundary_response hsuffix hp hhead hv
  exact ⟨hlength, hexact, hexact ▸ hrequested, hexact ▸ htyped,
    hexact ▸ hliteral, hresponse, hplugged⟩

end YulangClosure.Control
