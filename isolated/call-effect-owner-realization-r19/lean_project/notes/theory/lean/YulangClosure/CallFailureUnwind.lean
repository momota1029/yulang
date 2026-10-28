import YulangClosure.ControlSyntax

namespace YulangClosure.Control

/-- Prepending one existing transition adds exactly one prefix step. -/
private theorem prependFailureUnwindStep
    {C : Type} {step : C → C → Prop}
    {n : Nat} {first middle last : C}
    (hstep : step first middle)
    (hp : YulangClosure.Prefix step n middle last) :
    YulangClosure.Prefix step (n + 1) first last := by
  revert hstep
  induction hp with
  | refl =>
      intro hstep
      exact .snoc (.refl _) hstep
  | snoc hp hlast ih =>
      intro hstep
      exact .snoc (ih hstep) hlast

/-- Every represented failure can consume its Call frames using the existing
total cleanup witnesses, then finalize in one additional transition. -/
theorem call_failure_unwind_exists
    {World : Type} (md : Metadata World)
    (world : World) (reason : Original.Failure)
    (frames : List TypedCall.ContextFrame)
    (view : TypedCall.CallView) (result : Original.Ty)
    (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence)
    (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    ∃ nextWorld : World,
      YulangClosure.Prefix (CallControlStep md) (frames.length + 1)
        ⟨world, .active (.fail reason), frames,
          view, result, scopes, views, receipts, suffix⟩
        ⟨nextWorld, .failed reason, [],
          view, result, scopes, views, receipts, suffix⟩ := by
  induction frames generalizing world with
  | nil =>
      refine ⟨world, ?_⟩
      exact .snoc (.refl _)
        (.finishFailure world reason view result scopes views receipts suffix)
  | cons frame frames ih =>
      obtain ⟨middleWorld, hcleanup⟩ :=
        md.failWorld_total world (CallState.contextControlFrame frame)
      have hstep : CallControlStep md
          ⟨world, .active (.fail reason), frame :: frames,
            view, result, scopes, views, receipts, suffix⟩
          ⟨middleWorld, .active (.fail reason), frames,
            view, result, scopes, views, receipts, suffix⟩ := by
        cases frame with
        | bind body =>
            exact .failBind world reason body middleWorld hcleanup
              frames view result scopes views receipts suffix
        | scope owner =>
            exact .failScope world reason owner middleWorld hcleanup
              frames view result scopes views receipts suffix
        | expose effectView resultView =>
            exact .failExpose world reason effectView resultView middleWorld
              hcleanup frames view result scopes views receipts suffix
        | adapter input output body =>
            exact .failAdapter world reason input output body middleWorld
              hcleanup frames view result scopes views receipts suffix
      obtain ⟨nextWorld, hrest⟩ := ih middleWorld
      refine ⟨nextWorld, ?_⟩
      simpa only [List.length_cons] using
        (prependFailureUnwindStep hstep hrest)

end YulangClosure.Control
