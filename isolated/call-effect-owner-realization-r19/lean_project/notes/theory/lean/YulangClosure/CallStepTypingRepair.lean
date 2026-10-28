import YulangClosure.ControlTyping
import YulangClosure.CallEntryTypingRepair
import YulangClosure.CallPeelingTyping

namespace YulangClosure.Control

/-- Insert the response binder outside the bind body's own value binder.
The response remains at index zero in the captured continuation. -/
private theorem captureBind_typed
    {response a b : Original.Ty} {continuation body : TypedCall.Comp}
    (hk : TypedCall.CompTyped
      (Original.extend Original.emptyContext response) continuation a)
    (hb : TypedCall.CompTyped
      (Original.extend Original.emptyContext a) body b) :
    TypedCall.CompTyped (Original.extend Original.emptyContext response)
      (CallState.captureBind continuation body) b := by
  apply TypedCall.CompTyped.bind hk
  apply TypedCall.renameCallComp_typed hb
  intro index
  cases index <;> rfl

/-- The actual return transition substitutes its value for the frame binder. -/
private theorem returnBody_typed
    {a b : Original.Ty} {value : TypedCall.Value} {body : TypedCall.Comp}
    (hb : TypedCall.CompTyped
      (Original.extend Original.emptyContext a) body b)
    (hv : TypedCall.ValueTyped Original.emptyContext value a) :
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.substituteCallComp
        (fun index => if index = 0 then value else .var (index - 1)) body) b := by
  apply TypedCall.substituteCallComp_typed hb
  intro index ty hi
  cases index with
  | zero =>
      simp only [Original.extend, Option.some.injEq] at hi
      subst ty
      exact hv
  | succ index => exact .var hi

/-- Initial interface frames and the one receiver scope are type preserving. -/
private theorem initialFrames_typed
    (interfaces : List TypedCall.InterfacePlan) (owner : Nat) (a : Original.Ty) :
    TypedCall.ContextTyping Original.emptyContext
      ((interfaces.map fun interface =>
        TypedCall.ContextFrame.expose interface.ports.callEffectView
          interface.ports.resultView) ++ [.scope owner]) a a := by
  induction interfaces with
  | nil => exact .scope .nil
  | cons interface interfaces ih => exact .expose _ _ ih

/-- Typing of each existing transition, with an independently typed suffix.
This proves neither progress nor coverage of all typed Call computations. -/
private theorem call_step_typed
    {W : Type} {sig : Signature} {md : Metadata W}
    {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hstep : CallControlStep md s t) : CallStateTyped sig t result := by
  rcases ht with ⟨a, hh, hframes, hsuffix⟩
  cases hstep with
  | start term world suffix =>
      cases hh
      have hcarrier : TypedCall.ValueTyped Original.emptyContext
          term.argument.underlying (.thunk term.inputType) := by
        rw [← term.argumentIsThunk]
        exact term.argument.typed
      exact ⟨_, .enter term.functionTyped hcarrier (.nil _),
        initialFrames_typed term.callView.interfaces.reverse
          term.callView.receiverOwner term.resultType, hsuffix⟩
  | peelWrap =>
      cases hh with
      | enter hfunction hcarrier hpending =>
          cases hfunction with
          | wrap hinner hinput houtput hrinput hroutput =>
              exact ⟨_, .enter hinner
                (TypedCall.delayArgument_typed _ hcarrier hinput houtput)
                (TypedCall.AdaptersTyped.cons _ _ _ _ _ hrinput hroutput hpending),
                hframes, hsuffix⟩
  | attachReceipt =>
      cases hh with
      | enter hfunction hcarrier hpending =>
          exact ⟨_, .received hfunction hcarrier hpending, hframes, hsuffix⟩
  | enterLambda world mode receipt argument bodyResult leafResult body entryConsumer
      functionTyped carrier pending frames view resultType scopes views receipts suffix =>
      cases hh with
      | received hfunction hcarrier hpending =>
          cases hfunction with
          | lambdaValue receipt argument bodyResult leafResult body consumer
              hbody hconsumer hresult =>
              rw [← hresult] at hpending
              exact ⟨_, .active (TypedCall.callEntryBody_typed .value entryConsumer _
                hcarrier hbody hconsumer hpending), hframes, hsuffix⟩
          | lambdaComputation receipt argument bodyResult leafResult body consumer
              hbody hconsumer hresult =>
              rw [← hresult] at hpending
              exact ⟨_, .active (TypedCall.callEntryBody_typed .computation entryConsumer _
                hcarrier hbody hconsumer hpending), hframes, hsuffix⟩
  | enterBind =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | bind hfirst hbody =>
              exact ⟨_, .active hfirst, .bind hbody hframes, hsuffix⟩
  | enterOriginal =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | original hbody =>
              exact ⟨_, .originalState ⟨_, hbody, .nil⟩, hframes, hsuffix⟩
  | originalStep world source target step frames view resultType scopes views receipts suffix =>
      cases hh with
      | originalState hsource =>
          exact ⟨_, .originalState (Original.step_preservation step hsource),
            hframes, hsuffix⟩
  | originalExit =>
      cases hh with
      | originalState hsource =>
          rcases hsource with ⟨b, hcomp, hsourceFrames⟩
          cases hsourceFrames
          cases hcomp with
          | ret hvalue =>
              exact ⟨_, .active (.ret (.original hvalue)), hframes, hsuffix⟩
  | enterScope =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | scope hbody => exact ⟨_, .active hbody, .scope hframes, hsuffix⟩
  | enterExpose world enteredEffect enteredResult body frames view resultType
      scopes views receipts suffix =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | expose effectView resultView hbody =>
              exact ⟨_, .active hbody, .expose enteredEffect enteredResult hframes, hsuffix⟩
  | emitRequest =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | request hpayload hcontinuation =>
              exact ⟨_, .requesting hpayload hcontinuation, hframes, hsuffix⟩
  | forceDelay =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | force hvalue =>
              cases hvalue with
              | delay hbody => exact ⟨_, .active hbody, hframes, hsuffix⟩
  | forceEmbeddedOriginalDelay =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | force hvalue =>
              cases hvalue with
              | original hvalue =>
                  cases hvalue with
                  | delay hbody =>
                      exact ⟨_, .originalState ⟨_, hbody, .nil⟩, hframes, hsuffix⟩
  | returnBind =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | ret hvalue =>
              cases hframes with
              | bind hbody htail =>
                  exact ⟨_, .active (returnBody_typed hbody hvalue), htail, hsuffix⟩
  | returnAdapter =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | ret hvalue =>
              cases hframes with
              | adapter hbody htail =>
                  exact ⟨_, .active (returnBody_typed hbody hvalue), htail, hsuffix⟩
  | returnScope =>
      cases hframes with
      | scope htail => exact ⟨_, hh, htail, hsuffix⟩
  | returnExpose =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | ret hvalue =>
              cases hframes with
              | expose effectView resultView htail =>
                  exact ⟨_, .active (.ret (.view hvalue)), htail, hsuffix⟩
  | requestBind =>
      cases hh with
      | requesting hpayload hcontinuation =>
          cases hframes with
          | bind hbody htail =>
              exact ⟨_, .requesting hpayload (captureBind_typed hcontinuation hbody),
                htail, hsuffix⟩
  | requestAdapter =>
      cases hh with
      | requesting hpayload hcontinuation =>
          cases hframes with
          | adapter hbody htail =>
              exact ⟨_, .requesting hpayload (captureBind_typed hcontinuation hbody),
                htail, hsuffix⟩
  | requestScope =>
      cases hh with
      | requesting hpayload hcontinuation =>
          cases hframes with
          | scope htail =>
              exact ⟨_, .requesting hpayload (.scope hcontinuation), htail, hsuffix⟩
  | requestExpose world capturedEffect capturedResult opInstance payload
      continuation observed frames view resultType scopes views receipts suffix =>
      cases hh with
      | requesting hpayload hcontinuation =>
          cases hframes with
          | expose effectView resultView htail =>
              exact ⟨_, .requesting hpayload
                (.expose capturedEffect capturedResult hcontinuation), htail, hsuffix⟩
  | failBind =>
      cases hframes with
      | bind hbody htail => exact ⟨_, .active .fail, htail, hsuffix⟩
  | failAdapter =>
      cases hframes with
      | adapter hbody htail => exact ⟨_, .active .fail, htail, hsuffix⟩
  | failScope =>
      cases hframes with
      | scope htail => exact ⟨_, .active .fail, htail, hsuffix⟩
  | failExpose =>
      cases hframes with
      | expose effectView resultView htail => exact ⟨_, .active .fail, htail, hsuffix⟩
  | finishReturn =>
      cases hh with
      | active hcomp =>
          cases hcomp with
          | ret hvalue => exact ⟨_, .returned hvalue, hframes, hsuffix⟩
  | finishRequest =>
      cases hh with
      | requesting hpayload hcontinuation =>
          exact ⟨_, .requested hpayload hcontinuation, hframes, hsuffix⟩
  | finishFailure =>
      exact ⟨_, .failed _ _, hframes, hsuffix⟩

/-- Every already represented Call step preserves the Call typing judgment,
the result type, and the literal independently typed Control suffix.
No progress, world, source/native, or complete-Call adequacy claim is made. -/
theorem call_state_typed_step_preservation
    {W : Type} {sig : Signature} {md : Metadata W}
    {s t : CallState W} {result : Ty}
    (ht : CallStateTyped sig s result)
    (hstep : CallControlStep md s t) :
    CallStateTyped sig t result ∧
      t.resultType = s.resultType ∧
      t.literalSuffix = s.literalSuffix := by
  refine ⟨call_step_typed ht hstep, ?_⟩
  cases hstep <;> exact ⟨rfl, rfl⟩

end YulangClosure.Control
