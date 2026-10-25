import YulangClosure.HandlerGraphSafety

namespace YulangClosure.HandlerGraph
open HigherOrder (Ty Context emptyContext extend OperationInstance ViewOccurrence ReceiptTemplate PathCorrespondence)
variable {R : Type} {xi : R → Ty} {graph : Graph R}

def graphLambdaPlan (p : HigherOrderGraph.Safety.LambdaEntryPlan R) : LambdaEntryPlan R :=
  ⟨p.mode, p.receipt, p.argument, p.bodyResult, p.result,
    graphComp p.body, graphAdapter p.consumer, graphValue p.carrier⟩

def graphWrapPlan (p : HigherOrderGraph.Safety.WrapEntryPlan R) : WrapEntryPlan R :=
  ⟨graphValue p.inner, graphAdapter p.input, graphAdapter p.output, graphValue p.carrier⟩

def graphEvent : HigherOrderGraph.Safety.Event R → Event R
  | .silent => .silent
  | .lookup r => .lookup r
  | .observeView o => .observeView o
  | .lambdaEntry p => .lambdaEntry (graphLambdaPlan p)
  | .wrapEntry p => .wrapEntry (graphWrapPlan p)
  | .leaveScope o => .leaveScope o
  | .leaveExpose e r => .leaveExpose e r

theorem graph_single (v : HigherOrderGraph.Value R Empty) (i : Nat) :
    graphValue (HigherOrderGraph.Safety.single v i) = single (graphValue (R := R) (S := Empty) v) i := by
  cases i <;> rfl

theorem graph_substitute_top (v : HigherOrderGraph.Value R Empty) (m : HigherOrderGraph.Comp R Empty) :
    graphComp (HigherOrderGraph.substComp (HigherOrderGraph.Safety.single v) m) =
      substComp (single (graphValue (R := R) (S := Empty) v)) (graphComp m) :=
  graphComp_subst m _ _ (graph_single v)

theorem graph_adapterBody (c : HigherOrderGraph.Adapter R Empty) :
    graphComp (HigherOrderGraph.Safety.adapterBody c) = adapterBody (graphAdapter c) := by
  cases c <;> rfl

theorem graph_lambda_computation (p : HigherOrderGraph.Safety.LambdaEntryPlan R) :
    graphComp p.computation = (graphLambdaPlan p).computation := by
  cases p with
  | mk mode receipt a b r body consumer carrier =>
      cases mode <;>
        simp only [HigherOrderGraph.Safety.LambdaEntryPlan.computation, HigherOrderGraph.Safety.consumeResult,
          HigherOrderGraph.Safety.valueEntry, HigherOrderGraph.Safety.computationEntry, graphComp,
          graph_substitute_top, graph_adapterBody, graphLambdaPlan,
          LambdaEntryPlan.computation, consumeResult, valueEntry, computationEntry]

theorem graph_wrap_computation (p : HigherOrderGraph.Safety.WrapEntryPlan R) :
    graphComp p.computation = (graphWrapPlan p).computation := by
  cases p with
  | mk inner input output carrier =>
      simp only [HigherOrderGraph.Safety.WrapEntryPlan.computation, HigherOrderGraph.Safety.consumeResult,
        graphComp, graphValue, graph_adapterBody, graphWrapPlan,
        WrapEntryPlan.computation, consumeResult]

def handlerLambdaPlan (p : HigherOrder.Handler.LambdaEntryPlan) : LambdaEntryPlan R :=
  ⟨p.mode, p.receipt, p.argument, p.bodyResult, p.result,
    handlerComp p.body, handlerAdapter p.consumer, handlerValue p.carrier⟩

def handlerWrapPlan (p : HigherOrder.Handler.WrapEntryPlan) : WrapEntryPlan R :=
  ⟨handlerValue p.inner, handlerAdapter p.input, handlerAdapter p.output, handlerValue p.carrier⟩

def handlerEvent : HigherOrder.Handler.Event → Event R
  | .silent => .silent
  | .observeView o => .observeView o
  | .lambdaEntry p => .lambdaEntry (handlerLambdaPlan p)
  | .wrapEntry p => .wrapEntry (handlerWrapPlan p)
  | .leaveScope o => .leaveScope o
  | .leaveExpose e r => .leaveExpose e r

theorem handler_single (v : HigherOrder.Handler.Value) (i : Nat) :
    handlerValue (HigherOrder.Handler.single v i) = single (handlerValue (R := R) (S := Empty) v) i := by
  cases i <;> rfl

theorem handler_substitute_top (v : HigherOrder.Handler.Value) (m : HigherOrder.Handler.Comp) :
    handlerComp (HigherOrder.Handler.substComp (HigherOrder.Handler.single v) m) =
      substComp (single (handlerValue (R := R) (S := Empty) v)) (handlerComp m) :=
  handlerComp_subst m _ _ (handler_single v)

theorem handler_adapterBody (c : HigherOrder.Handler.Adapter) :
    handlerComp (R := R) (S := Empty) (HigherOrder.Handler.adapterBody c) = adapterBody (handlerAdapter c) := by
  cases c <;> rfl

theorem handler_lambda_computation (p : HigherOrder.Handler.LambdaEntryPlan) :
    handlerComp p.computation = (handlerLambdaPlan (R := R) p).computation := by
  cases p with
  | mk mode receipt a b r body consumer carrier =>
      cases mode <;>
        simp only [HigherOrder.Handler.LambdaEntryPlan.computation, HigherOrder.Handler.consumeResult,
          HigherOrder.Handler.valueEntry, HigherOrder.Handler.computationEntry, handlerComp,
          handler_substitute_top, handler_adapterBody, handlerLambdaPlan,
          LambdaEntryPlan.computation, consumeResult, valueEntry, computationEntry]

theorem handler_wrap_computation (p : HigherOrder.Handler.WrapEntryPlan) :
    handlerComp p.computation = (handlerWrapPlan (R := R) p).computation := by
  cases p with
  | mk inner input output carrier =>
      simp only [HigherOrder.Handler.WrapEntryPlan.computation, HigherOrder.Handler.consumeResult,
        handlerComp, handlerValue, handler_adapterBody, handlerWrapPlan,
        WrapEntryPlan.computation, consumeResult]

theorem handler_input_eq (h : HigherOrder.Handler.Handler) :
    (handlerHandler (R := R) (S := Empty) h).input = h.input := by cases h <;> rfl

theorem handler_values_eq (h : HigherOrder.Handler.Handler) :
    handlerValueArms h.values = (handlerHandler (R := R) (S := Empty) h).values := by cases h <;> rfl

theorem handler_operations_eq (h : HigherOrder.Handler.Handler) :
    handlerOperationArms h.operations = (handlerHandler (R := R) (S := Empty) h).operations := by cases h <;> rfl

theorem handler_continuation (q a : Ty) (k : HigherOrder.Handler.Comp) :
    handlerValue (HigherOrder.Handler.continuationValue q a k) =
      continuationValue (R := R) q a (handlerComp k) := rfl

theorem handler_attempt (h : HigherOrder.Handler.Handler) (op : OperationInstance)
    (p : HigherOrder.Handler.Value) (k body : HigherOrder.Handler.Comp) :
    handlerComp (HigherOrder.Handler.attemptOperation h op p k body) =
      attemptOperation (R := R) (handlerHandler h) op (handlerValue p) (handlerComp k) (handlerComp body) := by
  unfold HigherOrder.Handler.attemptOperation attemptOperation
  rw [handler_input_eq]
  apply handlerComp_subst
  intro i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem handler_forwarded (h : HigherOrder.Handler.Handler) (k : HigherOrder.Handler.Comp) :
    handlerComp (HigherOrder.Handler.forwardedContinuation h k) =
      forwardedContinuation (R := R) (handlerHandler h) (handlerComp k) := by
  simp only [HigherOrder.Handler.forwardedContinuation, handlerComp,
    handlerHandler_rename, forwardedContinuation]

theorem graph_step (g : HigherOrderGraph.Graph R) (step : HigherOrderGraph.Safety.Step g m e n) :
    Step (liftGraph g) (graphComp m) (graphEvent e) (graphComp n) := by
  induction step with
  | forceRef =>
      simp only [graphComp, graphValue, graphEvent]
      exact .forceRef
  | unionRef =>
      simp only [graphComp, graphValue, graphEvent]
      exact .unionRef
  | chooseLeftRef =>
      simp only [graphComp, graphValue, graphEvent]
      exact .chooseLeftRef
  | chooseRightRef =>
      simp only [graphComp, graphValue, graphEvent]
      exact .chooseRightRef
  | absurdRef =>
      simp only [graphComp, graphValue, graphEvent]
      exact .absurdRef
  | callRef =>
      simp only [graphComp, graphValue, graphEvent]
      exact .callRef
  | absurdView =>
      simp only [graphComp, graphValue, graphEvent]
      exact .absurdView
  | force =>
      simp only [graphComp, graphValue, graphEvent]
      exact .force
  | forceView =>
      simp only [graphComp, graphValue, graphEvent]
      exact .forceView
  | bindReturn =>
      simp only [graphComp, graphEvent, graph_substitute_top]
      exact .bindReturn
  | bind _ ih =>
      exact .bind ih
  | unionLeft =>
      simp only [graphComp, graphValue, graphEvent, graph_substitute_top]
      exact .unionLeft
  | unionRight =>
      simp only [graphComp, graphValue, graphEvent, graph_substitute_top]
      exact .unionRight
  | unionView =>
      simp only [graphComp, graphValue, graphEvent]
      exact .unionView
  | chooseLeft =>
      simp only [graphComp, graphValue, graphEvent]
      exact .chooseLeft
  | chooseRight =>
      simp only [graphComp, graphValue, graphEvent]
      exact .chooseRight
  | chooseLeftView =>
      simp only [graphComp, graphValue, graphEvent]
      exact .chooseLeftView
  | chooseRightView =>
      simp only [graphComp, graphValue, graphEvent]
      exact .chooseRightView
  | scope _ ih =>
      exact .scope ih
  | scopeReturn =>
      simp only [graphComp, graphEvent]
      exact .scopeReturn
  | expose _ ih =>
      exact .expose ih
  | exposeReturn =>
      simp only [graphComp, graphEvent]
      exact .exposeReturn
  | callView =>
      simp only [graphComp, graphValue, graphEvent]
      exact .callView
  | callLambda =>
      simp only [graphComp, graphValue, graphEvent, graph_lambda_computation, graphLambdaPlan]
      exact .callLambda
  | callWrap =>
      simp only [graphComp, graphValue, graphEvent, graph_wrap_computation, graphWrapPlan]
      exact .callWrap

theorem handler_step (step : HigherOrder.Handler.Step m e n) :
    Step graph (handlerComp m) (handlerEvent e) (handlerComp n) := by
  induction step with
  | force =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .force
  | forceView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .forceView
  | bindReturn =>
      simp only [handlerComp, handlerEvent, handler_substitute_top]
      exact .bindReturn
  | bind _ ih =>
      exact .bind ih
  | unionLeft =>
      simp only [handlerComp, handlerValue, handlerEvent, handler_substitute_top]
      exact .unionLeft
  | unionRight =>
      simp only [handlerComp, handlerValue, handlerEvent, handler_substitute_top]
      exact .unionRight
  | unionView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .unionView
  | chooseLeft =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .chooseLeft
  | chooseRight =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .chooseRight
  | chooseLeftView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .chooseLeftView
  | chooseRightView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .chooseRightView
  | scope _ ih =>
      exact .scope ih
  | scopeReturn =>
      simp only [handlerComp, handlerEvent]
      exact .scopeReturn
  | expose _ ih =>
      exact .expose ih
  | exposeReturn =>
      simp only [handlerComp, handlerEvent]
      exact .exposeReturn
  | callView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .callView
  | callLambda =>
      simp only [handlerComp, handlerValue, handlerEvent, handler_lambda_computation, handlerLambdaPlan]
      exact .callLambda
  | callWrap =>
      simp only [handlerComp, handlerValue, handlerEvent, handler_wrap_computation, handlerWrapPlan]
      exact .callWrap
  | bindRequest =>
      simp only [handlerComp, handlerEvent, handlerComp_rename]
      exact .bindRequest
  | bindFail =>
      simp only [handlerComp, handlerEvent]
      exact .bindFail
  | scopeRequest =>
      simp only [handlerComp, handlerEvent]
      exact .scopeRequest
  | scopeFail =>
      simp only [handlerComp, handlerEvent]
      exact .scopeFail
  | exposeRequest =>
      simp only [handlerComp, handlerEvent]
      exact .exposeRequest
  | exposeFail =>
      simp only [handlerComp, handlerEvent]
      exact .exposeFail
  | handle _ ih =>
      exact .handle ih
  | handleReturn =>
      simp only [handlerComp, handlerEvent, handler_values_eq]
      exact .handleReturn
  | handleRequest =>
      simp only [handlerComp, handlerEvent, handler_operations_eq]
      exact .handleRequest
  | handleFail =>
      simp only [handlerComp, handlerEvent]
      exact .handleFail
  | valueEmpty =>
      simp only [handlerComp, handlerEvent, handlerValueArms]
      exact .valueEmpty
  | valueCons =>
      simp only [handlerComp, handlerEvent, handler_substitute_top, handlerValueArms]
      exact .valueCons
  | valueWait _ ih =>
      exact .valueWait ih
  | valueYes =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .valueYes
  | valueNo =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .valueNo
  | valueView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .valueView
  | valueFail =>
      simp only [handlerComp, handlerEvent]
      exact .valueFail
  | valueRequest =>
      simp only [handlerComp, handlerEvent, handlerValue_rename, handlerHandler_rename, handlerValueArms_rename]
      exact .valueRequest
  | operationEmpty =>
      simp only [handlerComp, handlerEvent, handler_forwarded, handlerOperationArms]
      exact .operationEmpty
  | operationCons =>
      simp only [handlerComp, handlerEvent, handler_attempt, handlerOperationArms]
      exact .operationCons
  | operationSkip h => exact .operationSkip h
  | operationWait _ ih =>
      exact .operationWait ih
  | operationYes =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .operationYes
  | operationNo =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .operationNo
  | operationView =>
      simp only [handlerComp, handlerValue, handlerEvent]
      exact .operationView
  | operationFail =>
      simp only [handlerComp, handlerEvent]
      exact .operationFail
  | operationRequest =>
      simp only [handlerComp, handlerEvent, handlerComp_rename, handlerValue_rename, handlerHandler_rename, handlerOperationArms_rename]
      exact .operationRequest



theorem Prefix.append (h : Prefix graph m es n) (k : Prefix graph n fs last) :
    Prefix graph m (es ++ fs) last := by
  revert k
  induction h with
  | refl => intro k; exact k
  | cons step _ ih => intro k; exact .cons step (ih k)

theorem Prefix.bind (h : Prefix graph m es n) (body : Comp R Empty) :
    Prefix graph (.bind m body) es (.bind n body) := by
  induction h with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (.bind step) ih

theorem Prefix.scope (h : Prefix graph m es n) (owner : Nat) :
    Prefix graph (.scope owner m) es (.scope owner n) := by
  induction h with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (.scope step) ih

theorem Prefix.expose (h : Prefix graph m es n) (ev rv : ViewOccurrence) :
    Prefix graph (.expose ev rv m) es (.expose ev rv n) := by
  induction h with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (.expose step) ih

/-- The old context is traversed structurally, retaining every actual body. -/
def graphContextPlug : HigherOrderGraph.Safety.EvalContext R → Comp R Empty → Comp R Empty
  | .hole, m => m
  | .bind k body, m => .bind (graphContextPlug k m) (graphComp body)
  | .scope owner k, m => .scope owner (graphContextPlug k m)
  | .expose ev rv k, m => .expose ev rv (graphContextPlug k m)

theorem graph_plug (k : HigherOrderGraph.Safety.EvalContext R) (m : HigherOrderGraph.Comp R Empty) :
    graphComp (k.plug m) = graphContextPlug k (graphComp m) := by
  induction k with
  | hole => rfl
  | bind k body ih => exact congrArg (fun m => Comp.bind m (graphComp body)) ih
  | scope owner k ih => exact congrArg (Comp.scope owner) ih
  | expose ev rv k ih => exact congrArg (Comp.expose ev rv) ih

/-- Each outer bind moves under the response binder. Its own result binder
remains zero, so the inserted response slot is skipped with `up succ`. -/
def graphContinuation : HigherOrderGraph.Safety.EvalContext R → Comp R Empty → Comp R Empty
  | .hole, k => k
  | .bind c body, k => .bind (graphContinuation c k) (renameComp (Original.up Nat.succ) (graphComp body))
  | .scope owner c, k => .scope owner (graphContinuation c k)
  | .expose ev rv c, k => .expose ev rv (graphContinuation c k)

theorem propagate_graph_request (c : HigherOrderGraph.Safety.EvalContext R)
    (op : OperationInstance) (p : Value R Empty) (k : Comp R Empty) :
    ∃ events, Prefix graph (graphContextPlug c (.request op p k)) events
      (.request op p (graphContinuation c k)) := by
  induction c with
  | hole => exact ⟨[], .refl _⟩
  | bind c body ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨events ++ [.silent], (trace.bind _).append (.cons .bindRequest (.refl _))⟩
  | scope owner c ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨events ++ [.silent], (trace.scope owner).append (.cons .scopeRequest (.refl _))⟩
  | expose ev rv c ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨events ++ [.silent], (trace.expose ev rv).append (.cons .exposeRequest (.refl _))⟩

theorem propagate_graph_failure (c : HigherOrderGraph.Safety.EvalContext R)
    (reason : Original.Failure) :
    ∃ events, Prefix graph (graphContextPlug c (.fail reason)) events (.fail reason) := by
  induction c with
  | hole => exact ⟨[], .refl _⟩
  | bind c body ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨events ++ [.silent], (trace.bind _).append (.cons .bindFail (.refl _))⟩
  | scope owner c ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨events ++ [.silent], (trace.scope owner).append (.cons .scopeFail (.refl _))⟩
  | expose ev rv c ih =>
      obtain ⟨events, trace⟩ := ih
      exact ⟨events ++ [.silent], (trace.expose ev rv).append (.cons .exposeFail (.refl _))⟩

/-- Actual response equation, for arbitrary combined response values (including
references and code with handlers), arbitrary old contexts and original K. -/
theorem graph_resume_equation (c : HigherOrderGraph.Safety.EvalContext R)
    (k : Comp R Empty) (v : Value R Empty) :
    substComp (single v) (graphContinuation c k) =
      graphContextPlug c (substComp (single v) k) := by
  induction c with
  | hole => rfl
  | bind c body ih =>
      simp only [graphContinuation, substComp, graphContextPlug, ih]
      rw [comp_rename_cancel (graphComp body) (Original.up Nat.succ) (lift (single v))
        (lift_cancel Nat.succ (single v) (fun _ => rfl))]
  | scope owner c ih => exact congrArg (Comp.scope owner) ih
  | expose ev rv c ih => exact congrArg (Comp.expose ev rv) ih

/-- Old contextual suspension becomes a genuine combined root request. This
statement retains the exact instance and payload, and derives K typing from
the old full computation and actual propagation, rather than assuming it. -/
theorem graph_request_correspondence (g : HigherOrderGraph.Graph R)
    (hg : HigherOrderGraph.WellTyped g xi)
    (c : HigherOrderGraph.Safety.EvalContext R) (op : OperationInstance)
    (p : HigherOrderGraph.Value R Empty) (k : HigherOrderGraph.Comp R Empty)
    (ht : HigherOrderGraph.CompTyped xi HigherOrderGraph.emptyTy emptyContext
      (c.plug (.request op p k)) a) :
    ∃ events, Prefix (liftGraph g) (graphComp (c.plug (.request op p k))) events
        (.request op (graphValue p) (graphContinuation c (graphComp k))) ∧
      ValueTyped xi emptyTy emptyContext (graphValue p) op.payloadType ∧
      CompTyped xi emptyTy (extend emptyContext op.responseType)
        (graphContinuation c (graphComp k)) a ∧
      (∀ response : Value R Empty,
        substComp (single response) (graphContinuation c (graphComp k)) =
          graphContextPlug c (substComp (single response) (graphComp k))) := by
  obtain ⟨events, trace⟩ := propagate_graph_request (graph := liftGraph g) c op (graphValue p) (graphComp k)
  have start : CompTyped xi emptyTy emptyContext
      (graphContextPlug c (.request op (graphValue p) (graphComp k))) a := by
    simpa only [graph_plug, graphComp, emptyTy, HigherOrderGraph.emptyTy] using (graphComp_typed ht)
  have finish := prefix_preservation (liftGraph_typed hg) trace start
  cases finish with
  | request hp hk =>
      refine ⟨events, ?_, hp, hk, ?_⟩
      · simpa only [graph_plug, graphComp] using trace
      · intro response
        exact graph_resume_equation c (graphComp k) response

theorem graph_failure_correspondence (g : HigherOrderGraph.Graph R)
    (c : HigherOrderGraph.Safety.EvalContext R) (reason : Original.Failure) :
    ∃ events, Prefix (liftGraph g) (graphComp (c.plug (.fail reason))) events (.fail reason) := by
  simpa only [graph_plug, graphComp] using
    (propagate_graph_failure (graph := liftGraph g) c reason)

/-- For an old response, the resumption is literally the embedding of the
old saved context plugged around the old response-substituted computation. -/
theorem old_graph_resume_equation (c : HigherOrderGraph.Safety.EvalContext R)
    (k : HigherOrderGraph.Comp R Empty) (v : HigherOrderGraph.Value R Empty) :
    substComp (single (graphValue v)) (graphContinuation c (graphComp k)) =
      graphComp (c.plug (HigherOrderGraph.substComp (HigherOrderGraph.Safety.single v) k)) := by
  rw [graph_resume_equation, graph_plug, graph_substitute_top]

/-- Apply the captured typing back to every independently typed response and
every raw internal prefix. No linear-use premise is imposed on the same K. -/
theorem graph_resumption_safety (g : HigherOrderGraph.Graph R)
    (hg : HigherOrderGraph.WellTyped g xi)
    (guard : GuardedValueGraph.Guarded (HigherOrderGraph.projectGraph g))
    (c : HigherOrderGraph.Safety.EvalContext R) (op : OperationInstance)
    (p : HigherOrderGraph.Value R Empty) (k : HigherOrderGraph.Comp R Empty)
    (ht : HigherOrderGraph.CompTyped xi HigherOrderGraph.emptyTy emptyContext
      (c.plug (.request op p k)) a)
    (response : Value R Empty) (hr : ValueTyped xi emptyTy emptyContext response op.responseType)
    (trace : Prefix (liftGraph g)
      (substComp (single response) (graphContinuation c (graphComp k))) events last) :
    CompTyped xi emptyTy emptyContext last a ∧ CanProgress (liftGraph g) last := by
  obtain ⟨_, _, _, hk, _⟩ := graph_request_correspondence g hg c op p k ht
  exact finite_prefix_safety (liftGraph_typed hg) (liftGraph_guard g guard)
    (substitute_top hk hr) trace

/-- The exact old allocation supplier is consumed before embedding. Handler h
is independently typed in the new allocated graph and may itself contain graph
references and arbitrary combined bodies. No fresh node typing/rank oracle. -/
theorem source_rec_under_handler
    {g : HigherOrderGraph.Graph R} {nu : Fin n → Ty}
    (hg : HigherOrderGraph.WellTyped g xi)
    (guard : GuardedValueGraph.Guarded (HigherOrderGraph.projectGraph g))
    (rhs : Fin n → HigherOrder.Value)
    (hrhs : ∀ s, HigherOrder.ValueTyped (HigherOrderGraph.sourceContext nu env) (rhs s) (nu s))
    (hcapture : HigherOrderGraph.CapturesTyped xi env capture)
    (hcycle : HigherOrderGraph.FreshNoCycle (HigherOrderGraph.sourceFresh capture rhs))
    (hbody : HigherOrder.CompTyped (HigherOrderGraph.sourceContext nu env) body a)
    (hh : HandlerTyped (HigherOrderGraph.joinTy xi nu) emptyTy emptyContext h a b)
    (trace : Prefix (liftGraph (HigherOrderGraph.allocate g (HigherOrderGraph.sourceFresh capture rhs)))
      (.handle h (graphComp (HigherOrderGraph.sourceCloseComp capture n body))) events last) :
    CompTyped (HigherOrderGraph.joinTy xi nu) emptyTy emptyContext last b ∧
      CanProgress (liftGraph (HigherOrderGraph.allocate g (HigherOrderGraph.sourceFresh capture rhs))) last := by
  obtain ⟨allocated, ⟨guarded⟩, closedBody⟩ :=
    HigherOrderGraph.source_rec_allocation hg guard rhs hrhs hcapture hcycle hbody
  exact finite_prefix_safety (liftGraph_typed allocated) (liftGraph_guard _ guarded)
    (.handle hh (graphComp_typed closedBody)) trace


theorem graph_prefix (g : HigherOrderGraph.Graph R)
    (trace : HigherOrderGraph.Safety.Steps g m events n) :
    Prefix (liftGraph g) (graphComp m) (events.map graphEvent) (graphComp n) := by
  induction trace with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (graph_step g step) ih

theorem handler_prefix (trace : HigherOrder.Handler.Prefix m events n) :
    Prefix graph (handlerComp m) (events.map handlerEvent) (handlerComp n) := by
  induction trace with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (handler_step step) ih

/-- Every old suspension, not merely a selected context, has finite root
propagation. The stronger request theorem above supplies its typed resumption. -/
theorem graph_suspended_root (g : HigherOrderGraph.Graph R)
    (hs : HigherOrderGraph.Safety.Suspended m) :
    ∃ events n, Prefix (liftGraph g) (graphComp m) events n ∧ Terminal n := by
  rcases HigherOrderGraph.Safety.suspended_decomposition hs with
    ⟨c, reason, rfl⟩ | ⟨c, op, p, k, rfl⟩
  · obtain ⟨events, trace⟩ := graph_failure_correspondence g c reason
    exact ⟨events, _, trace, .failed reason⟩
  · obtain ⟨events, trace⟩ := propagate_graph_request (graph := liftGraph g) c op (graphValue p) (graphComp k)
    exact ⟨events, _, by simpa only [graph_plug, graphComp] using trace, .requested _ _ _⟩

namespace Examples

def unitTy : Ty := .base .unit
def boolTy : Ty := .base .bool
def resultTy : Ty := .union unitTy boolTy
def op : OperationInstance := ⟨20, [], unitTy, unitTy⟩
def nextOp : OperationInstance := ⟨21, [], unitTy, boolTy⟩
def recursiveK : Comp Bool Empty := .dynamicCall (.ref false) (.delay (.ret (.var 0)))
def recursiveBody : Comp Bool Empty := .request op .unit recursiveK
def consumer : Adapter Bool Empty := .mk unitTy unitTy (.ret (.var 0)) [] []
def recursiveLambda : Value Bool Empty :=
  .lambda .computation ⟨[], []⟩ unitTy unitTy unitTy recursiveBody consumer

/-- The recursive reference occurs in actual request continuation code. The
other node is a returned union carrier observed by an actual wait rule. -/
def exampleGraph : Graph Bool
  | false => recursiveLambda
  | true => .inRight (.bool true)
def types : Bool → Ty
  | false => .callable unitTy unitTy
  | true => resultTy

theorem graph_typed : WellTyped exampleGraph types := by
  intro r
  cases r with
  | false =>
      exact .lambdaComputation
        (.request .unit (.dynamicCall (.ref false) (.delay (.ret (.var rfl)))))
        (.mk (.ret (.var rfl)))
  | true => exact .inRight .bool

def guard : GuardedValueGraph.Guarded (projectGraph exampleGraph) where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ 0
  decrease := by intro r s h; cases r <;> cases h

def handler : Handler Bool Empty := .mk 70 unitTy boolTy
  (.cons (.ret (.ref true)) .nil) (.cons op true (.ret (.ref true)) .nil)

theorem handler_typed : HandlerTyped types emptyTy env handler unitTy boolTy :=
  .mk (.cons (.ret (.ref true)) .nil) (.cons (.ret (.ref true)) .nil)

def recursiveProgram : Comp Bool Empty :=
  .handle handler (.dynamicCall (.ref false) (.delay (.ret .unit)))

theorem recursiveProgram_typed : CompTyped types emptyTy emptyContext recursiveProgram boolTy :=
  .handle handler_typed (.dynamicCall (.ref false) (.delay (.ret .unit)))

/-- Full real recursive lambda entry, rootward request propagation, shallow
selection, attempt evaluation, graph lookup inside wait, and Yes return. -/
theorem recursive_request_handler_execution :
    ∃ events, Prefix exampleGraph recursiveProgram events (.ret (.bool true)) := by
  exact ⟨_, .cons (.handle .callRef) (.cons (.handle .callLambda)
    (.cons (.handle .bindRequest) (.cons .handleRequest
      (.cons .operationCons (.cons .operationRef (.cons .operationYes (.refl _)))))))⟩

theorem recursive_every_prefix_safe (trace : Prefix exampleGraph recursiveProgram events n) :
    CompTyped types emptyTy emptyContext n boolTy ∧ CanProgress exampleGraph n :=
  finite_prefix_safety graph_typed guard recursiveProgram_typed trace

/-- The selected arm still receives K:unit→unit. H K has result bool. -/
theorem two_continuations :
    ValueTyped types emptyTy emptyContext (continuationValue unitTy unitTy recursiveK)
      (.callable unitTy unitTy) ∧
    CompTyped types emptyTy (extend emptyContext unitTy)
      (forwardedContinuation handler recursiveK) boolTy :=
  ⟨continuationValue_typed (.dynamicCall (.ref false) (.delay (.ret (.var rfl)))),
    forwardedContinuation_typed handler_typed (.dynamicCall (.ref false) (.delay (.ret (.var rfl))))⟩

def nestedWait : Comp Bool Empty :=
  .waitOperation handler op .unit (.ret (.var 0)) .nil
    (.request nextOp .unit (.ret (.ref true)))
def restoredWait : Comp Bool Empty :=
  .waitOperation (renameHandler Nat.succ handler) op (renameValue Nat.succ .unit)
    (renameComp (Original.up Nat.succ) (.ret (.var 0)))
    (renameOperationArms Nat.succ .nil) (.ret (.ref true))

theorem nestedWait_typed : CompTyped types emptyTy emptyContext nestedWait boolTy :=
  .waitOperation handler_typed .unit (.ret (.var rfl)) .nil (.request .unit (.ret (.ref true)))

theorem nested_restoration : Step exampleGraph nestedWait .silent (.request nextOp .unit restoredWait) :=
  .operationRequest

theorem nested_restoration_typed :
    CompTyped types emptyTy emptyContext (.request nextOp .unit restoredWait) boolTy :=
  preservation graph_typed nested_restoration nestedWait_typed

/-- Arbitrary typed response is consumed by the exact restored wait. Its
pending graph-backed trial then resumes and returns Yes. -/
theorem nested_response_execution (response : Value Bool Empty) :
    Prefix exampleGraph (substComp (single response) restoredWait)
      [.lookup true, .silent] (.ret (.bool true)) :=
  .cons .operationRef (.cons .operationYes (.refl _))

theorem nested_response_safe (response : Value Bool Empty)
    (hr : ValueTyped types emptyTy emptyContext response boolTy)
    (trace : Prefix exampleGraph (substComp (single response) restoredWait) events last) :
    CompTyped types emptyTy emptyContext last boolTy ∧ CanProgress exampleGraph last := by
  have hk : CompTyped types emptyTy (extend emptyContext boolTy) restoredWait boolTy := by
    have h := nested_restoration_typed
    cases h with
    | request _ hk => exact hk
  exact finite_prefix_safety graph_typed guard (substitute_top hk hr) trace

end Examples


namespace SourceExample
open Examples (unitTy boolTy op)

def oldGraph : HigherOrderGraph.Graph Empty := Empty.elim
def oldTypes : Empty → Ty := Empty.elim
def capture : Nat → HigherOrderGraph.Value Empty Empty := fun _ => .unit

def oldGuard : GuardedValueGraph.Guarded (HigherOrderGraph.projectGraph oldGraph) where
  rank := Empty.elim
  ceiling := 0
  bound := fun r => Empty.elim r
  decrease := fun r => Empty.elim r

def functionTy : Ty := .callable unitTy unitTy
def nameTypes : Fin 1 → Ty := fun _ => functionTy

def rhs : Fin 1 → HigherOrder.Value := fun _ =>
  .lambda .computation ⟨[], []⟩ unitTy unitTy unitTy
    (.request op .unit (.dynamicCall (.var 2) (.delay (.ret (.var 0)))))
    (.mk unitTy unitTy (.ret (.var 0)) [] [])

theorem rhs_typed (s : Fin 1) :
    HigherOrder.ValueTyped (HigherOrderGraph.sourceContext nameTypes emptyContext) (rhs s) functionTy :=
  .lambdaComputation (.request .unit (.dynamicCall (.var rfl) (.delay (.ret (.var rfl)))))
    (.mk (.ret (.var rfl)))

def fresh := HigherOrderGraph.sourceFresh capture rhs

theorem fresh_noCycle : HigherOrderGraph.FreshNoCycle fresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

def body : HigherOrder.Comp := .dynamicCall (.var 0) (.delay (.ret .unit))

def handler : Handler (Sum Empty (Fin 1)) Empty :=
  .mk 80 unitTy boolTy (.cons (.ret (.inRight (.bool true))) .nil)
    (.cons op true (.ret (.inRight (.bool true))) .nil)

def allocated : Graph (Sum Empty (Fin 1)) :=
  liftGraph (HigherOrderGraph.allocate oldGraph fresh)

def program : Comp (Sum Empty (Fin 1)) Empty :=
  .handle handler (graphComp (HigherOrderGraph.sourceCloseComp capture 1 body))

/-- The actual source recursive name becomes the fresh reference under both
the lambda parameter and the independent request response binder. -/
theorem allocated_equation (s : Fin 1) :
    allocated (.inr s) =
      .lambda .computation ⟨[], []⟩ unitTy unitTy unitTy
        (.request op .unit (.dynamicCall (.ref (.inr 0)) (.delay (.ret (.var 0)))))
        (.mk unitTy unitTy (.ret (.var 0)) [] []) := rfl

/-- Universal application of the actual allocation supplier, not an assumed
fresh graph typing judgment. The handler is independently typed after lifting. -/
theorem every_prefix_safe (trace : Prefix allocated program events last) :
    CompTyped (HigherOrderGraph.joinTy oldTypes nameTypes) emptyTy emptyContext last boolTy ∧
      CanProgress allocated last := by
  exact source_rec_under_handler (g := oldGraph) (xi := oldTypes) (nu := nameTypes)
    (env := emptyContext) (capture := capture) (body := body)
    (fun r => Empty.elim r) oldGuard rhs rhs_typed
    (by intro i a h; cases h) fresh_noCycle
    (.dynamicCall (.var rfl) (.delay (.ret .unit)))
    (.mk (.cons (.ret (.inRight .bool)) .nil) (.cons (.ret (.inRight .bool)) .nil)) trace

/-- This execution starts from sourceCloseComp and the actual allocated graph. -/
theorem request_selected : ∃ events, Prefix allocated program events (.ret (.bool true)) := by
  exact ⟨_, .cons (.handle .callRef) (.cons (.handle .callLambda)
    (.cons (.handle .bindRequest) (.cons .handleRequest
      (.cons .operationCons (.cons .operationYes (.refl _))))))⟩

end SourceExample

end YulangClosure.HandlerGraph
