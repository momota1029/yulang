import YulangClosure.CallPrefixTyping
import YulangClosure.CallTerminalTyping

namespace YulangClosure.Control

theorem call_state_typed_start
    {W : Type} {sig : Signature}
    (term : TypedCall.CallTerm) (world : W)
    (suffix : List Frame) {result : Ty}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result) :
    CallStateTyped sig (CallState.initial term world suffix) result := by
  exact ⟨term.resultType, .call term, .nil, hsuffix⟩

theorem initial_call_prefix_terminal_typing
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {target : CallState W}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) target) :
    CallStateTyped sig target result ∧
      target.resultType = term.resultType ∧ target.literalSuffix = suffix ∧
      (∀ v, target.frames = [] → target.head = .returned v →
        TypedCall.ValueTyped Original.emptyContext v target.resultType) ∧
      (∀ op payload continuation, target.frames = [] →
        target.head = .requested op payload continuation →
        TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
        TypedCall.CompTyped
          (Original.extend Original.emptyContext op.responseType)
          continuation target.resultType) := by
  have hstart :
      CallStateTyped sig (CallState.initial term world suffix) result :=
    call_state_typed_start term world suffix hsuffix
  rcases call_state_typed_prefix_preservation hstart hp with
    ⟨htarget, hresult, hliteralSuffix⟩
  refine ⟨htarget, hresult, hliteralSuffix, ?_, ?_⟩
  · intro v hempty hhead
    exact returned_call_state_typed htarget hempty hhead
  · intro op payload continuation hempty hhead
    exact requested_call_state_typed htarget hempty hhead

end YulangClosure.Control
