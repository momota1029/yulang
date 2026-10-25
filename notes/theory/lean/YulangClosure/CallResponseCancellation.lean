import YulangClosure.ControlSyntax

namespace YulangClosure.Control

/-- Supply the response at index zero and remove that binder. -/
abbrev responseSubstitution (v : TypedCall.Value) : Nat → TypedCall.Value :=
  fun i => if i = 0 then v else .var (i - 1)

abbrev plugResponse (k : TypedCall.Comp) (v : TypedCall.Value) :
    TypedCall.Comp := TypedCall.substituteCallComp (responseSubstitution v) k

/-- A pointwise inverse remains an inverse under one actual Call binder. -/
private theorem lift_inverse
    (s : Nat → TypedCall.Value) (r : Nat → Nat)
    (hinv : ∀ i, s (r i) = .var i) :
    ∀ i, TypedCall.liftCallSubstitution s (TypedCall.upCall r i) = .var i := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      change TypedCall.renameCallValue Nat.succ (s (r i)) = .var (i + 1)
      exact congrArg (TypedCall.renameCallValue Nat.succ) (hinv i)

mutual
  /-- This inverse law concerns Call syntax, including open delayed bodies.
  Embedded Original syntax is retained by both actual traversals. -/
  private theorem substitute_rename_value_cancel
      (value : TypedCall.Value) (s : Nat → TypedCall.Value) (r : Nat → Nat)
      (hinv : ∀ i, s (r i) = .var i) :
      TypedCall.substituteCallValue s (TypedCall.renameCallValue r value) =
        value := by
    cases value with
    | var i => exact hinv i
    | original value => rfl
    | delay body =>
        exact congrArg TypedCall.Value.delay
          (substitute_rename_comp_cancel body s r hinv)
    | view value occurrence =>
        exact congrArg (fun value => TypedCall.Value.view value occurrence)
          (substitute_rename_value_cancel value s r hinv)

  private theorem substitute_rename_comp_cancel
      (body : TypedCall.Comp) (s : Nat → TypedCall.Value) (r : Nat → Nat)
      (hinv : ∀ i, s (r i) = .var i) :
      TypedCall.substituteCallComp s (TypedCall.renameCallComp r body) =
        body := by
    cases body with
    | original body => rfl
    | ret value =>
        exact congrArg TypedCall.Comp.ret
          (substitute_rename_value_cancel value s r hinv)
    | bind first body =>
        have hfirst := substitute_rename_comp_cancel first s r hinv
        have hbody := substitute_rename_comp_cancel body
            (TypedCall.liftCallSubstitution s) (TypedCall.upCall r)
            (lift_inverse s r hinv)
        simp only [TypedCall.renameCallComp, TypedCall.substituteCallComp,
          hfirst, hbody]
    | force value =>
        exact congrArg TypedCall.Comp.force
          (substitute_rename_value_cancel value s r hinv)
    | scope owner body =>
        exact congrArg (TypedCall.Comp.scope owner)
          (substitute_rename_comp_cancel body s r hinv)
    | expose effectView resultView body =>
        exact congrArg (TypedCall.Comp.expose effectView resultView)
          (substitute_rename_comp_cancel body s r hinv)
    | request opInstance payload continuation =>
        have hpayload := substitute_rename_value_cancel payload s r hinv
        have hcontinuation := substitute_rename_comp_cancel continuation
            (TypedCall.liftCallSubstitution s) (TypedCall.upCall r)
            (lift_inverse s r hinv)
        simp only [TypedCall.renameCallComp, TypedCall.substituteCallComp,
          hpayload, hcontinuation]
    | fail reason => rfl
end

/-- Supplying a response cancels the response binder inserted outside the
bind body's own binder. No typing or closedness premise is needed. -/
theorem captureBind_response_cancellation
    (k body : TypedCall.Comp) (v : TypedCall.Value) :
    plugResponse (CallState.captureBind k body) v =
      .bind (plugResponse k v) body := by
  change TypedCall.Comp.bind (plugResponse k v)
      (TypedCall.substituteCallComp
        (TypedCall.liftCallSubstitution (responseSubstitution v))
        (TypedCall.renameCallComp (TypedCall.upCall Nat.succ) body)) =
    TypedCall.Comp.bind (plugResponse k v) body
  apply congrArg (TypedCall.Comp.bind (plugResponse k v))
  apply substitute_rename_comp_cancel
  intro i
  cases i <;> rfl

end YulangClosure.Control
