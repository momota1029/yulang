import YulangClosure.HigherOrderEntry

namespace YulangClosure.HigherOrder.Safety
open YulangClosure.HigherOrder

/-! Candidate operational research model. Events retain metadata syntactically;
no theorem below identifies this ledger with receipt/path/owner behavior. -/

inductive ThunkForm : Value → Prop where
  | delay (body : Comp) : ThunkForm (.delay body)
  | view : ThunkForm v → ThunkForm (.view v occurrence)

inductive CallableForm : Value → Prop where
  | lambda (mode receipt a b r body consumer) :
      CallableForm (.lambda mode receipt a b r body consumer)
  | wrap : CallableForm f → CallableForm (.wrap f input output)
  | view : CallableForm v → CallableForm (.view v occurrence)

inductive UnionForm : Value → Prop where
  | left (v : Value) : UnionForm (.inLeft v)
  | right (v : Value) : UnionForm (.inRight v)
  | view : UnionForm v → UnionForm (.view v occurrence)

inductive IntersectionForm : Value → Prop where
  | both (v : Value) : IntersectionForm (.both v)
  | view : IntersectionForm v → IntersectionForm (.view v occurrence)

theorem thunk_canonical (h : ValueTyped emptyContext v (.thunk a)) : ThunkForm v := by
  cases h with
  | var h => cases h
  | delay _ => exact .delay _
  | view h => exact .view (thunk_canonical h)

theorem callable_canonical (h : ValueTyped emptyContext v (.callable a b)) : CallableForm v := by
  cases h with
  | var h => cases h
  | lambdaValue _ _ => exact .lambda _ _ _ _ _ _ _
  | lambdaComputation _ _ => exact .lambda _ _ _ _ _ _ _
  | wrap h _ _ => exact .wrap (callable_canonical h)
  | view h => exact .view (callable_canonical h)

theorem union_canonical (h : ValueTyped emptyContext v (.union a b)) : UnionForm v := by
  cases h with
  | var h => cases h
  | inLeft _ => exact .left _
  | inRight _ => exact .right _
  | view h => exact .view (union_canonical h)

theorem intersection_canonical (h : ValueTyped emptyContext v (.intersection a b)) :
    IntersectionForm v := by
  cases h with
  | var h => cases h
  | both _ _ => exact .both _
  | view h => exact .view (intersection_canonical h)

theorem bottom_empty (h : ValueTyped emptyContext v .bottom) : False := by
  cases h with
  | var h => cases h
  | view h => exact bottom_empty h

/-- Complete annotations are retained as data, without claiming their semantic
adequacy. A view observation is an explicit transition, never silent erasure. -/
inductive Event where
  | silent
  | observeView (occurrence : ViewOccurrence)
  | lambdaEntry (plan : LambdaEntryPlan)
  | wrapEntry (plan : WrapEntryPlan)
  | leaveScope (owner : Nat)
  | leaveExpose (effectView resultView : ViewOccurrence)

/-- Independent operational rules: no rule contains a typing or safety premise.
Only the left side of bind and bodies of scope/expose are evaluation contexts. -/
inductive Step : Comp → Event → Comp → Prop where
  | force : Step (.force (.delay body)) .silent body
  | forceView : Step (.force (.view v o)) (.observeView o) (.force v)
  | bindReturn : Step (.bind (.ret v) body) .silent (substComp (single v) body)
  | bind : Step m e n → Step (.bind m body) e (.bind n body)
  | unionLeft : Step (.unionCase (.inLeft v) l r) .silent (substComp (single v) l)
  | unionRight : Step (.unionCase (.inRight v) l r) .silent (substComp (single v) r)
  | unionView : Step (.unionCase (.view v o) l r) (.observeView o) (.unionCase v l r)
  | chooseLeft : Step (.chooseLeft (.both v)) .silent (.ret v)
  | chooseRight : Step (.chooseRight (.both v)) .silent (.ret v)
  | chooseLeftView : Step (.chooseLeft (.view v o)) (.observeView o) (.chooseLeft v)
  | chooseRightView : Step (.chooseRight (.view v o)) (.observeView o) (.chooseRight v)
  | scope : Step m e n → Step (.scope owner m) e (.scope owner n)
  | scopeReturn : Step (.scope owner (.ret v)) (.leaveScope owner) (.ret v)
  | expose : Step m e n → Step (.expose ev rv m) e (.expose ev rv n)
  | exposeReturn : Step (.expose ev rv (.ret v)) (.leaveExpose ev rv) (.ret v)
  | callView : Step (.dynamicCall (.view f o) arg) (.observeView o) (.dynamicCall f arg)
  | callLambda :
      Step (.dynamicCall (.lambda mode receipt a b r body consumer) carrier)
        (.lambdaEntry ⟨mode, receipt, a, b, r, body, consumer, carrier⟩)
        (LambdaEntryPlan.computation ⟨mode, receipt, a, b, r, body, consumer, carrier⟩)
  | callWrap :
      Step (.dynamicCall (.wrap inner input output) carrier)
        (.wrapEntry ⟨inner, input, output, carrier⟩)
        (WrapEntryPlan.computation ⟨inner, input, output, carrier⟩)

/-- Only explicit failure or an unhandled operation suspends execution. The
whole enclosing evaluation context and the original response binder remain. -/
inductive Suspended : Comp → Prop where
  | request (op payload continuation) : Suspended (.request op payload continuation)
  | fail (reason) : Suspended (.fail reason)
  | bind : Suspended m → Suspended (.bind m body)
  | scope : Suspended m → Suspended (.scope owner m)
  | expose : Suspended m → Suspended (.expose ev rv m)

inductive Returned : Comp → Prop where
  | ret (v : Value) : Returned (.ret v)

def CanProgress (m : Comp) : Prop :=
  Returned m ∨ Suspended m ∨ ∃ e n, Step m e n

theorem preservation (step : Step m e n) (h : CompTyped env m a) : CompTyped env n a := by
  induction step generalizing env a with
  | force =>
      cases h with
      | force hv => cases hv with | delay hb => exact hb
  | forceView =>
      cases h with
      | force hv => cases hv with | view hv => exact .force hv
  | bindReturn =>
      cases h with
      | bind hv hb => cases hv with | ret hv => exact substitute_top hb hv
  | bind _ ih =>
      cases h with
      | bind hm hb => exact .bind (ih hm) hb
  | unionLeft =>
      cases h with
      | unionCase hv hl _ => cases hv with | inLeft hv => exact substitute_top hl hv
  | unionRight =>
      cases h with
      | unionCase hv _ hr => cases hv with | inRight hv => exact substitute_top hr hv
  | unionView =>
      cases h with
      | unionCase hv hl hr => cases hv with | view hv => exact .unionCase hv hl hr
  | chooseLeft =>
      cases h with
      | chooseLeft hv => cases hv with | both hl _ => exact .ret hl
  | chooseRight =>
      cases h with
      | chooseRight hv => cases hv with | both _ hr => exact .ret hr
  | chooseLeftView =>
      cases h with
      | chooseLeft hv => cases hv with | view hv => exact .chooseLeft hv
  | chooseRightView =>
      cases h with
      | chooseRight hv => cases hv with | view hv => exact .chooseRight hv
  | scope _ ih =>
      cases h with
      | scope hm => exact .scope (ih hm)
  | scopeReturn =>
      cases h with
      | scope hm => exact hm
  | expose _ ih =>
      cases h with
      | expose hm => exact .expose (ih hm)
  | exposeReturn =>
      cases h with
      | expose hm => exact hm
  | callView =>
      cases h with
      | dynamicCall hf ha => cases hf with | view hf => exact .dynamicCall hf ha
  | callLambda =>
      cases h with
      | dynamicCall hf ha =>
          cases hf with
          | lambdaValue hb hc => exact lambda_value_plan_typed _ hb hc ha
          | lambdaComputation hb hc => exact lambda_computation_plan_typed _ hb hc ha
  | callWrap =>
      cases h with
      | dynamicCall hf ha =>
          cases hf with
          | wrap hf hi ho => exact wrap_plan_typed hf hi ho ha

theorem closed_progress (h : CompTyped emptyContext m a) : CanProgress m := by
  cases h with
  | ret _ => exact .inl (.ret _)
  | force hv =>
      cases thunk_canonical hv with
      | delay _ => exact .inr (.inr ⟨_, _, .force⟩)
      | view _ => exact .inr (.inr ⟨_, _, .forceView⟩)
  | bind hm hb =>
      rcases closed_progress hm with hr | hs | ⟨e, n, step⟩
      · cases hr
        exact .inr (.inr ⟨_, _, .bindReturn⟩)
      · exact .inr (.inl (.bind hs))
      · exact .inr (.inr ⟨e, _, .bind step⟩)
  | unionCase hv hl hr =>
      cases union_canonical hv with
      | left _ => exact .inr (.inr ⟨_, _, .unionLeft⟩)
      | right _ => exact .inr (.inr ⟨_, _, .unionRight⟩)
      | view _ => exact .inr (.inr ⟨_, _, .unionView⟩)
  | chooseLeft hv =>
      cases intersection_canonical hv with
      | both _ => exact .inr (.inr ⟨_, _, .chooseLeft⟩)
      | view _ => exact .inr (.inr ⟨_, _, .chooseLeftView⟩)
  | chooseRight hv =>
      cases intersection_canonical hv with
      | both _ => exact .inr (.inr ⟨_, _, .chooseRight⟩)
      | view _ => exact .inr (.inr ⟨_, _, .chooseRightView⟩)
  | absurd hv => exact False.elim (bottom_empty hv)
  | scope hm =>
      rcases closed_progress hm with hr | hs | ⟨e, n, step⟩
      · cases hr
        exact .inr (.inr ⟨_, _, .scopeReturn⟩)
      · exact .inr (.inl (.scope hs))
      · exact .inr (.inr ⟨e, _, .scope step⟩)
  | expose hm =>
      rcases closed_progress hm with hr | hs | ⟨e, n, step⟩
      · cases hr
        exact .inr (.inr ⟨_, _, .exposeReturn⟩)
      · exact .inr (.inl (.expose hs))
      · exact .inr (.inr ⟨e, _, .expose step⟩)
  | request _ _ => exact .inr (.inl (.request _ _ _))
  | fail => exact .inr (.inl (.fail _))
  | dynamicCall hf ha =>
      cases callable_canonical hf with
      | lambda _ _ _ _ _ _ _ => exact .inr (.inr ⟨_, _, .callLambda⟩)
      | wrap _ => exact .inr (.inr ⟨_, _, .callWrap⟩)
      | view _ => exact .inr (.inr ⟨_, _, .callView⟩)

theorem returned_no_step (h : Returned m) : ¬ Step m e n := by
  intro step
  cases h
  cases step

theorem suspended_no_step (h : Suspended m) : ¬ Step m e n := by
  intro step
  induction h generalizing e n with
  | request => cases step
  | fail => cases step
  | bind hs ih =>
      cases step with
      | bindReturn => cases hs
      | bind step => exact ih step
  | scope hs ih =>
      cases step with
      | scopeReturn => cases hs
      | scope step => exact ih step
  | expose hs ih =>
      cases step with
      | exposeReturn => cases hs
      | expose step => exact ih step

/-- Contexts capture only the actual evaluation positions; neither delayed
bodies nor request continuations are evaluated before their entry event. -/
inductive EvalContext where
  | hole
  | bind (inner : EvalContext) (body : Comp)
  | scope (owner : Nat) (inner : EvalContext)
  | expose (ev rv : ViewOccurrence) (inner : EvalContext)

def EvalContext.plug : EvalContext → Comp → Comp
  | .hole, m => m
  | .bind k body, m => .bind (k.plug m) body
  | .scope owner k, m => .scope owner (k.plug m)
  | .expose ev rv k, m => .expose ev rv (k.plug m)

inductive ContextTyped (env : Context) : EvalContext → Ty → Ty → Prop where
  | hole : ContextTyped env .hole a a
  | bind : ContextTyped env k a b → CompTyped (extend env b) body c →
      ContextTyped env (.bind k body) a c
  | scope : ContextTyped env k a b → ContextTyped env (.scope owner k) a b
  | expose : ContextTyped env k a b → ContextTyped env (.expose ev rv k) a b

theorem plug_typed (hk : ContextTyped env k a b) (hm : CompTyped env m a) :
    CompTyped env (k.plug m) b := by
  induction hk with
  | hole => exact hm
  | bind _ hb ih => exact .bind (ih hm) hb
  | scope _ ih => exact .scope (ih hm)
  | expose _ ih => exact .expose (ih hm)

theorem context_inversion (k : EvalContext) (h : CompTyped env (k.plug m) b) :
    ∃ a, CompTyped env m a ∧ ContextTyped env k a b := by
  induction k generalizing b with
  | hole => exact ⟨_, h, .hole⟩
  | bind k body ih =>
      cases h with
      | bind hm hb =>
          obtain ⟨a, hm, hk⟩ := ih hm
          exact ⟨a, hm, .bind hk hb⟩
  | scope owner k ih =>
      cases h with
      | scope hm =>
          obtain ⟨a, hm, hk⟩ := ih hm
          exact ⟨a, hm, .scope hk⟩
  | expose ev rv k ih =>
      cases h with
      | expose hm =>
          obtain ⟨a, hm, hk⟩ := ih hm
          exact ⟨a, hm, .expose hk⟩

/-- A suspension has a concrete failure or request at a finite context hole.
This is not an extra rule declaring arbitrary stuck terms terminal. -/
theorem suspended_decomposition (h : Suspended m) :
    (∃ k : EvalContext, ∃ reason, m = k.plug (.fail reason)) ∨
    (∃ k : EvalContext, ∃ op payload continuation, m = k.plug (.request op payload continuation)) := by
  induction h with
  | request op payload continuation =>
      exact .inr ⟨.hole, op, payload, continuation, rfl⟩
  | fail reason => exact .inl ⟨.hole, reason, rfl⟩
  | bind _ ih =>
      rcases ih with ⟨k, reason, rfl⟩ | ⟨k, op, payload, continuation, rfl⟩
      · exact .inl ⟨.bind k _, reason, rfl⟩
      · exact .inr ⟨.bind k _, op, payload, continuation, rfl⟩
  | scope _ ih =>
      rcases ih with ⟨k, reason, rfl⟩ | ⟨k, op, payload, continuation, rfl⟩
      · exact .inl ⟨.scope _ k, reason, rfl⟩
      · exact .inr ⟨.scope _ k, op, payload, continuation, rfl⟩
  | expose _ ih =>
      rcases ih with ⟨k, reason, rfl⟩ | ⟨k, op, payload, continuation, rfl⟩
      · exact .inl ⟨.expose _ _ k, reason, rfl⟩
      · exact .inr ⟨.expose _ _ k, op, payload, continuation, rfl⟩

/-- The finite trace stores every emitted event in execution order. -/
inductive Steps : Comp → List Event → Comp → Prop where
  | refl (m) : Steps m [] m
  | cons : Step m e n → Steps n trace last → Steps m (e :: trace) last

theorem trace_preservation (steps : Steps m trace n) (h : CompTyped env m a) :
    CompTyped env n a := by
  induction steps generalizing env a with
  | refl => exact h
  | cons step rest ih => exact ih (preservation step h)

/-- Quantifies over every finite prefix, not a selected successful execution. -/
theorem finite_prefix_safety (h : CompTyped emptyContext m a) (steps : Steps m trace n) :
    CompTyped emptyContext n a ∧ CanProgress n := by
  have hn := trace_preservation steps h
  exact ⟨hn, closed_progress hn⟩

/-- An actual operation response remains independently quantified. -/
theorem resume_request_typed
    (h : CompTyped env (.request op payload continuation) a)
    (response : Value) (hr : ValueTyped env response op.responseType) :
    CompTyped env (substComp (single response) continuation) a := by
  cases h with
  | request _ hk => exact substitute_top hk hr

/-- Independent response and enclosing-context quantifiers are both retained.
No local lambda action stands in for the foreign continuation. -/
theorem resume_in_context_typed (k : EvalContext)
    (h : CompTyped env (k.plug (.request op payload continuation)) a)
    (response : Value) (hr : ValueTyped env response op.responseType) :
    CompTyped env (k.plug (substComp (single response) continuation)) a := by
  obtain ⟨b, hm, hk⟩ := context_inversion k h
  exact plug_typed hk (resume_request_typed hm response hr)

/-- Viewed Force is represented explicitly, with the exact occurrence retained. -/
theorem viewed_force (v : Value) (o : ViewOccurrence) :
    Step (.force (.view v o)) (.observeView o) (.force v) := .forceView

/-- Computation entry passes the original thunk without forcing it. -/
theorem computation_entry_equation (receipt a b r body consumer carrier) :
    (LambdaEntryPlan.mk .computation receipt a b r body consumer carrier).computation =
      .bind (substComp (single carrier) body) (adapterBody consumer) := rfl

/-- Value entry forces before body execution, then applies the result consumer. -/
theorem value_entry_equation (receipt a b r body consumer carrier) :
    (LambdaEntryPlan.mk .value receipt a b r body consumer carrier).computation =
      .bind (.bind (.force carrier) body) (adapterBody consumer) := rfl

/-- Input adaptation is inside the delayed carrier; output adaptation waits for
an inner result. This equation rules out premature argument adaptation. -/
theorem wrap_entry_equation (inner input output carrier) :
    (WrapEntryPlan.mk inner input output carrier).computation =
      .bind (.dynamicCall inner (.delay (.bind (.force carrier) (adapterBody input))))
        (adapterBody output) := rfl

end YulangClosure.HigherOrder.Safety
