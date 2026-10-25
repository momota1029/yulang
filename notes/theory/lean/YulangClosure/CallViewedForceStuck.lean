import YulangClosure.ControlSyntax

namespace YulangClosure.Control

/-- A Force whose operand retains a View has no successor in the current
Call control relation, independently of typing, frames, or metadata laws. -/
theorem viewed_force_no_successor
    {W : Type} {md : Metadata W} {s : CallState W}
    {value : TypedCall.Value} {occurrence : TypedCall.ViewOccurrence}
    (hhead : s.head = .active (.force (.view value occurrence))) :
    ¬ ∃ t, CallControlStep md s t := by
  rintro ⟨t, hstep⟩
  cases hstep <;> simp [CallState.initial] at hhead

end YulangClosure.Control
