import YulangClosure.CallStepTypingRepair

namespace YulangClosure.Control

/-- A supplied finite prefix of the existing Call relation preserves typing,
the result type, and the literal independently typed suffix, including at
length zero. No progress or terminal reachability is asserted. -/
theorem call_state_typed_prefix_preservation
    {W : Type} {sig : Signature} {md : Metadata W}
    {n : Nat} {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hp : YulangClosure.Prefix (CallControlStep md) n s t) :
    CallStateTyped sig t result ∧
      t.resultType = s.resultType ∧
      t.literalSuffix = s.literalSuffix := by
  revert ht
  induction hp with
  | refl =>
      intro ht
      exact ⟨ht, rfl, rfl⟩
  | snoc hp hstep ih =>
      intro ht
      rcases ih ht with ⟨hmiddle, hresult, hsuffix⟩
      rcases call_state_typed_step_preservation hmiddle hstep with
        ⟨htarget, hstepResult, hstepSuffix⟩
      exact ⟨htarget, hstepResult.trans hresult, hstepSuffix.trans hsuffix⟩

end YulangClosure.Control
