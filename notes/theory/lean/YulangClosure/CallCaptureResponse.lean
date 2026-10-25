import YulangClosure.CallResponseCancellation
import YulangClosure.CallCaptureTyping

namespace YulangClosure.Control

/-- Supplying the response cancels the response binder across every captured
Call frame, in the existing innermost-frame-first order. -/
theorem plugResponse_captureFrames
    (frames : List TypedCall.ContextFrame)
    (k : TypedCall.Comp) (v : TypedCall.Value) :
    plugResponse (CallState.captureFrames frames k) v =
      TypedCall.plugFrames frames (plugResponse k v) := by
  induction frames generalizing k with
  | nil => rfl
  | cons frame frames ih =>
      cases frame with
      | bind body =>
          calc
            plugResponse (CallState.captureFrames
                (.bind body :: frames) k) v =
                plugResponse (CallState.captureFrames frames
                  (CallState.captureBind k body)) v := rfl
            _ = TypedCall.plugFrames frames
                (plugResponse (CallState.captureBind k body) v) := ih _
            _ = TypedCall.plugFrames frames
                (.bind (plugResponse k v) body) := by
                  rw [captureBind_response_cancellation]
            _ = TypedCall.plugFrames (.bind body :: frames)
                (plugResponse k v) := rfl
      | adapter input output body =>
          calc
            plugResponse (CallState.captureFrames
                (.adapter input output body :: frames) k) v =
                plugResponse (CallState.captureFrames frames
                  (CallState.captureBind k body)) v := rfl
            _ = TypedCall.plugFrames frames
                (plugResponse (CallState.captureBind k body) v) := ih _
            _ = TypedCall.plugFrames frames
                (.bind (plugResponse k v) body) := by
                  rw [captureBind_response_cancellation]
            _ = TypedCall.plugFrames (.adapter input output body :: frames)
                (plugResponse k v) := rfl
      | scope owner =>
          exact ih (TypedCall.Comp.scope owner k)
      | expose effectView resultView =>
          exact ih (TypedCall.Comp.expose effectView resultView k)

private theorem responseSubstitution_typed
    {response : Original.Ty} {v : TypedCall.Value}
    (hv : TypedCall.ValueTyped Original.emptyContext v response) :
    ∀ i ty,
      Original.extend Original.emptyContext response i = some ty →
      TypedCall.ValueTyped Original.emptyContext (responseSubstitution v i) ty := by
  intro i ty hi
  cases i with
  | zero =>
      have hty : ty = response := Option.some.inj hi.symm
      subst ty
      simpa [responseSubstitution] using hv
  | succ i =>
      simp [Original.extend, Original.emptyContext] at hi

/-- A typed response turns the captured continuation into a closed, typed
plugging of the original frame list. This is syntax typing only. -/
theorem plugResponse_captureFrames_typed
    {frames : List TypedCall.ContextFrame}
    {response a b : Original.Ty}
    {k : TypedCall.Comp} {v : TypedCall.Value}
    (hframes :
      TypedCall.ContextTyping Original.emptyContext frames a b)
    (hk : TypedCall.CompTyped
      (Original.extend Original.emptyContext response) k a)
    (hv : TypedCall.ValueTyped Original.emptyContext v response) :
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames frames (plugResponse k v)) b := by
  rw [← plugResponse_captureFrames]
  apply TypedCall.substituteCallComp_typed
    (captureFrames_typed hframes hk)
  exact responseSubstitution_typed hv

end YulangClosure.Control
