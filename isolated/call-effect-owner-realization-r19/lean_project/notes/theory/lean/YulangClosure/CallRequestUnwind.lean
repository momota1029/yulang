import YulangClosure.ControlSyntax

namespace YulangClosure.Control

/-- Capture the innermost remaining Call frame before capturing its tail.
Bind and adapter frames use the actual response-binder lifting operation. -/
def CallState.captureFrames :
    List TypedCall.ContextFrame → TypedCall.Comp → TypedCall.Comp
  | [], continuation => continuation
  | .bind body :: frames, continuation =>
      captureFrames frames (CallState.captureBind continuation body)
  | .adapter _ _ body :: frames, continuation =>
      captureFrames frames (CallState.captureBind continuation body)
  | .scope owner :: frames, continuation =>
      captureFrames frames (.scope owner continuation)
  | .expose effectView resultView :: frames, continuation =>
      captureFrames frames (.expose effectView resultView continuation)

/-- Prepend one actual step to a snoc-oriented finite prefix. -/
private theorem prefix_prepend
    {C : Type} {step : C → C → Prop} {n : Nat} {b c : C}
    (hp : YulangClosure.Prefix step n b c) :
    ∀ {a : C}, step a b → YulangClosure.Prefix step (n + 1) a c := by
  induction hp with
  | refl b =>
      intro a hfirst
      exact .snoc (.refl a) hfirst
  | snoc hp hlast ih =>
      intro a hfirst
      exact .snoc (ih hfirst) hlast

/-- Every represented requesting state can propagate through its actual Call
frames and finish the request in exactly one step per frame plus one final
step. The final world and scope context are existential witnesses. -/
theorem call_request_unwind_exists
    {W : Type} (md : Metadata W)
    (world : W)
    (op : TypedCall.OperationInstance)
    (payload : TypedCall.Value)
    (continuation : TypedCall.Comp)
    (observed : List TypedCall.ViewOccurrence)
    (frames : List TypedCall.ContextFrame)
    (view : TypedCall.CallView)
    (result : Original.Ty)
    (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence)
    (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    ∃ (world' : W) (scopes' : List Nat),
      YulangClosure.Prefix (CallControlStep md) (frames.length + 1)
        ⟨world, .requesting op payload continuation observed,
          frames, view, result, scopes, views, receipts, suffix⟩
        ⟨world', .requested op payload
            (CallState.captureFrames frames continuation),
          [], view, result, scopes', observed, receipts, suffix⟩ := by
  induction frames generalizing world continuation scopes with
  | nil =>
      refine ⟨world, scopes, ?_⟩
      exact .snoc (.refl _)
        (.finishRequest world op payload continuation observed view result scopes
          views receipts suffix)
  | cons frame frames ih =>
      cases frame with
      | bind body =>
          obtain ⟨world', scopes', htail⟩ :=
            ih world (CallState.captureBind continuation body) scopes
          refine ⟨world', scopes', ?_⟩
          simpa only [List.length_cons, CallState.captureFrames] using
            (prefix_prepend htail
              (.requestBind world op payload continuation body observed frames
                view result scopes views receipts suffix))
      | adapter input output body =>
          obtain ⟨world', scopes', htail⟩ :=
            ih world (CallState.captureBind continuation body) scopes
          refine ⟨world', scopes', ?_⟩
          simpa only [List.length_cons, CallState.captureFrames] using
            (prefix_prepend htail
              (.requestAdapter world op payload continuation observed input output
                body frames view result scopes views receipts suffix))
      | scope owner =>
          obtain ⟨world', scopes', htail⟩ :=
            ih (md.suspendScope world owner) (.scope owner continuation)
              (owner :: scopes)
          refine ⟨world', scopes', ?_⟩
          simpa only [List.length_cons, CallState.captureFrames] using
            (prefix_prepend htail
              (.requestScope world owner op payload continuation observed frames
                view result scopes views receipts suffix))
      | expose effectView resultView =>
          obtain ⟨world', scopes', htail⟩ :=
            ih (md.suspendView world effectView.identity)
              (.expose effectView resultView continuation) scopes
          refine ⟨world', scopes', ?_⟩
          simpa only [List.length_cons, CallState.captureFrames] using
            (prefix_prepend htail
              (.requestExpose world effectView resultView op payload continuation
                observed frames view result scopes views receipts suffix))

end YulangClosure.Control
