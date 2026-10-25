import YulangClosure.CallRequestUnwind

namespace YulangClosure.Control

/-- Insert the response binder outside the bind body's own value binder.
The body's bound value stays at index zero; its ambient indices move past
the response binder. -/
private theorem captureBind_response_typed
    {env : Original.Context} {response a b : Original.Ty}
    {continuation body : TypedCall.Comp}
    (hk : TypedCall.CompTyped
      (Original.extend env response) continuation a)
    (hb : TypedCall.CompTyped (Original.extend env a) body b) :
    TypedCall.CompTyped (Original.extend env response)
      (CallState.captureBind continuation body) b := by
  apply TypedCall.CompTyped.bind hk
  apply TypedCall.renameCallComp_typed hb
  intro index
  cases index <;> rfl

/-- Capture a typed frame list under one additional response binder, following
the actual innermost-frame-first order of `CallState.captureFrames`. -/
private theorem captureFrames_typed_env
    {env : Original.Context} {frames : List TypedCall.ContextFrame}
    {response a b : Original.Ty}
    (hframes : TypedCall.ContextTyping env frames a b)
    (k : TypedCall.Comp)
    (hk : TypedCall.CompTyped (Original.extend env response) k a) :
    TypedCall.CompTyped (Original.extend env response)
      (CallState.captureFrames frames k) b := by
  induction hframes generalizing k with
  | nil =>
      simpa only [CallState.captureFrames] using hk
  | bind hbody _ ih =>
      simpa only [CallState.captureFrames] using
        (ih _ (captureBind_response_typed hk hbody))
  | adapter hbody _ ih =>
      simpa only [CallState.captureFrames] using
        (ih _ (captureBind_response_typed hk hbody))
  | scope _ ih =>
      simpa only [CallState.captureFrames] using
        (ih _ (TypedCall.CompTyped.scope hk))
  | expose effectView resultView _ ih =>
      simpa only [CallState.captureFrames] using
        (ih _ (TypedCall.CompTyped.expose effectView resultView hk))

/-- Existing typed Call frames preserve continuation typing when captured
under the response binder. This is a syntax typing judgment, with no claim
that a source/native resumption supplies a response. -/
theorem captureFrames_typed
    {frames : List TypedCall.ContextFrame}
    {response a b : Original.Ty}
    {k : TypedCall.Comp}
    (hframes :
      TypedCall.ContextTyping Original.emptyContext frames a b)
    (hk : TypedCall.CompTyped
      (Original.extend Original.emptyContext response) k a) :
    TypedCall.CompTyped
      (Original.extend Original.emptyContext response)
      (CallState.captureFrames frames k) b := by
  exact captureFrames_typed_env hframes k hk

end YulangClosure.Control
