import YulangClosure.CallFiniteTyping
import YulangClosure.CallViewedForceReachability
import YulangClosure.CallViewedForceStuck

namespace YulangClosure.Control

/-- A typed, actually reachable Call state whose View-wrapped Force head has
no successor in the present Call relation. The independent literal suffix is
retained and typed at the Call's unit result. This is a formal-relation
obstruction only; it does not establish source/frontend reachability. -/
theorem reachable_typed_viewed_force_stuck
    {W : Type} {sig : Signature} {md : Metadata W}
    (world : W) (occurrence : TypedCall.ViewOccurrence)
    (suffix : List Frame) {result : Ty}
    (hsuffix : FramesTyped sig suffix (.original (.base .unit)) result) :
    let target := viewedForceTarget world occurrence suffix
    CallStateTyped sig target result ∧
      target.head = .active
        (.force (.view (.delay (.ret (.original .unit))) occurrence)) ∧
      ¬ ∃ next, CallControlStep md target next := by
  let target := viewedForceTarget world occurrence suffix
  have hprefix :
      Prefix (CallControlStep md) 5
        (CallState.initial (viewedForceCallTerm occurrence) world suffix) target := by
    simpa [target] using viewed_force_prefix md world occurrence suffix
  have htyped := initial_call_prefix_terminal_typing
    (term := viewedForceCallTerm occurrence) (world := world)
    (suffix := suffix) (result := result) hsuffix hprefix
  have hhead : target.head = .active
      (.force (.view (.delay (.ret (.original .unit))) occurrence)) := by
    rfl
  exact ⟨htyped.1, hhead, viewed_force_no_successor hhead⟩

end YulangClosure.Control
