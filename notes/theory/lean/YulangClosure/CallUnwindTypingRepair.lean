import YulangClosure.CallFiniteTyping
import YulangClosure.CallRequestUnwind
import YulangClosure.CallFailureUnwind

namespace YulangClosure.Control

/-- Concatenate two actual finite prefixes of the same transition relation. -/
theorem call_prefix_append
    {C : Type} {step : C → C → Prop}
    {n m : Nat} {a b c : C}
    (hfirst : YulangClosure.Prefix step n a b)
    (hsecond : YulangClosure.Prefix step m b c) :
    YulangClosure.Prefix step (n + m) a c := by
  induction hsecond with
  | refl => simpa using hfirst
  | @snoc m b middle c hprefix hstep ih =>
      exact .snoc (ih hfirst) hstep

/-- A supplied finite prefix to a requesting state can be extended through
all actual Call frames while preserving the existing typing invariant. -/
theorem call_request_unwind_initial_typed
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {s : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {continuation : TypedCall.Comp}
    {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload continuation observed) :
    ∃ t : CallState W,
      YulangClosure.Prefix (CallControlStep md)
        (n + (s.frames.length + 1))
        (CallState.initial term world suffix) t ∧
      t.head = .requested op payload
        (CallState.captureFrames s.frames continuation) ∧
      t.frames = [] ∧
      CallStateTyped sig t result ∧
      t.resultType = term.resultType ∧
      t.literalSuffix = suffix ∧
      t.callView = s.callView ∧
      t.receiptSlots = s.receiptSlots ∧
      t.viewContext = observed ∧
      TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
      TypedCall.CompTyped
        (Original.extend Original.emptyContext op.responseType)
        (CallState.captureFrames s.frames continuation) t.resultType := by
  have hinitial : CallStateTyped sig (CallState.initial term world suffix) result :=
    call_state_typed_start term world suffix hsuffix
  rcases call_state_typed_prefix_preservation hinitial hp with
    ⟨hs, hresult, hliteral⟩
  have hresult0 : s.resultType = term.resultType :=
    hresult.trans (by rfl)
  have hliteral0 : s.literalSuffix = suffix :=
    hliteral.trans (by rfl)
  rcases s with ⟨worldS, headS, framesS, callViewS, resultTypeS,
    scopeContextS, viewContextS, receiptSlotsS, literalSuffixS⟩
  cases hhead
  obtain ⟨worldT, scopesT, hunwind⟩ :=
    call_request_unwind_exists md worldS op payload continuation observed
      framesS callViewS resultTypeS scopeContextS viewContextS receiptSlotsS
      literalSuffixS
  let t : CallState W :=
    ⟨worldT, .requested op payload (CallState.captureFrames framesS continuation),
      [], callViewS, resultTypeS, scopesT, observed, receiptSlotsS, literalSuffixS⟩
  have htrace := call_prefix_append hp hunwind
  have htypedT : CallStateTyped sig t result := by
    exact (call_state_typed_prefix_preservation hinitial htrace).1
  have hterminal := requested_call_state_typed htypedT rfl rfl
  refine ⟨t, ?_, rfl, rfl, htypedT, ?_, ?_, rfl, rfl, rfl, hterminal.1, ?_⟩
  · simpa [t, Nat.add_assoc] using htrace
  · simpa only [t] using hresult0
  · simpa only [t] using hliteral0
  · simpa [t] using hterminal.2

/-- A supplied finite prefix to an active failure can be extended through
all actual Call frames while preserving the existing typing invariant. -/
theorem call_failure_unwind_initial_typed
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {s : CallState W}
    {reason : Original.Failure}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .active (.fail reason)) :
    ∃ t : CallState W,
      YulangClosure.Prefix (CallControlStep md)
        (n + (s.frames.length + 1))
        (CallState.initial term world suffix) t ∧
      t.head = .failed reason ∧
      t.frames = [] ∧
      CallStateTyped sig t result ∧
      t.resultType = term.resultType ∧
      t.literalSuffix = suffix ∧
      t.callView = s.callView ∧
      t.scopeContext = s.scopeContext ∧
      t.viewContext = s.viewContext ∧
      t.receiptSlots = s.receiptSlots := by
  have hinitial : CallStateTyped sig (CallState.initial term world suffix) result :=
    call_state_typed_start term world suffix hsuffix
  rcases call_state_typed_prefix_preservation hinitial hp with
    ⟨hs, hresult, hliteral⟩
  have hresult0 : s.resultType = term.resultType :=
    hresult.trans (by rfl)
  have hliteral0 : s.literalSuffix = suffix :=
    hliteral.trans (by rfl)
  rcases s with ⟨worldS, headS, framesS, callViewS, resultTypeS,
    scopeContextS, viewContextS, receiptSlotsS, literalSuffixS⟩
  cases hhead
  obtain ⟨worldT, hunwind⟩ :=
    call_failure_unwind_exists md worldS reason framesS callViewS resultTypeS
      scopeContextS viewContextS receiptSlotsS literalSuffixS
  let t : CallState W :=
    ⟨worldT, .failed reason, [], callViewS, resultTypeS, scopeContextS,
      viewContextS, receiptSlotsS, literalSuffixS⟩
  have htrace := call_prefix_append hp hunwind
  have htypedT : CallStateTyped sig t result := by
    exact (call_state_typed_prefix_preservation hinitial htrace).1
  refine ⟨t, ?_, rfl, rfl, htypedT, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simpa [t, Nat.add_assoc] using htrace
  · simpa only [t] using hresult0
  · simpa only [t] using hliteral0

end YulangClosure.Control
