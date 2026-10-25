import YulangClosure.NativeLiteralReadback

namespace YulangClosure.Control

/-- The operation-instance interpretation remains an explicit source bridge.
All original actual prefix, suffix, metadata, world and request quantifiers are
retained. Neither response typing nor successful decoding is a hypothesis. -/
theorem actual_call_request_completed_native_literal_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n m : Nat} {s t : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (hpost : YulangClosure.Prefix (CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k')
    {expected : Original.Base} {role : NativeLiteral.Role}
    {sameValue : Prop} (datum : NativeLiteral.Datum)
    (haccept : NativeLiteral.Accepted (some expected) role sameValue datum)
    (hproducer : NativeLiteral.WellFormed datum)
    (hinstance : op.responseType = .base expected) :
    ∃ l : Original.Literal,
    NativeLiteral.readback datum = some l ∧ l.base = expected ∧
    TypedCall.ValueTyped Original.emptyContext (TypedCall.literalResponse l) op.responseType ∧
    m = s.frames.length + 1 ∧
    t = s.requestBoundary md (s.frames.length + 1) ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k) (TypedCall.literalResponse l)) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames (plugResponse k (TypedCall.literalResponse l))) term.resultType := by
  obtain ⟨l, hl, hb, _⟩ := NativeLiteral.accepted_readback haccept hproducer
  have hbase : l.base = expected := (Option.some.inj hb).symm
  have hresponse : op.responseType = .base l.base := by
    rw [hbase]
    exact hinstance
  exact ⟨l, hl, hbase, TypedCall.literalResponse_operation_typed l op hresponse,
    actual_call_request_completed_literal_response hsuffix hp hhead hpost hcomplete l hresponse⟩

/-- Distinct accepted integer replies remain distinct at the response binder;
this does not require an arbitrary continuation to observe that distinction. -/
example : plugResponse (.ret (.var 0)) (TypedCall.literalResponse (.int 11)) ≠
    plugResponse (.ret (.var 0)) (TypedCall.literalResponse (.int 23)) := by
  intro h
  cases h

end YulangClosure.Control
