import YulangClosure.PrimitiveOperationInstance

namespace YulangClosure.Control

/-- Candidate application to the complete original actual formal Call theorem.
The response equality is derived from the retained declaration interpretation.
The original actual prefix, suffix, world, metadata, completion and all existing
conclusions are preserved. Native execution-to-formal-prefix equality, source
observation authentication and declaration retention remain explicit OPEN
correspondence obligations; hrequest is not evidence of those Rust facts. -/
theorem actual_call_request_completed_declared_literal_response
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
    {Key Effect Hole : Type} [DecidableEq Key]
    (keys : List Key) (declaration : PrimitiveOperation.Declaration Key Effect Hole)
    (hrequest : PrimitiveOperation.request keys declaration = some op)
    (hexpected : PrimitiveOperation.expected declaration = some expected) :
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
  have hi : op.responseType = .base expected :=
    PrimitiveOperation.interpret_response hrequest hexpected
  exact actual_call_request_completed_native_literal_response
    hsuffix hp hhead hpost hcomplete datum haccept hproducer hi

end YulangClosure.Control
