import YulangClosure.HigherOrderGraphObservation

/-! Candidate raw execution for every accepted higher-order graph constructor.
Graph lookup is an actual transition. No raw rule assumes typing or canonical
forms; receipts, paths and views remain uninterpreted retained metadata. -/
namespace YulangClosure.HigherOrderGraph.Safety
open YulangClosure.HigherOrderGraph
open HigherOrder (Ty Context emptyContext extend ViewOccurrence ReceiptTemplate
  OperationInstance PathCorrespondence)
variable {R : Type} {xi : R → Ty} {graph : Graph R}

def single (v : Value R Empty) : Nat → Value R Empty
  | 0 => v
  | n+1 => .var n

theorem substitute_top (hb : CompTyped xi emptyTy (extend env a) body b) (hv : ValueTyped xi emptyTy env v a) :
    CompTyped xi emptyTy env (substComp (single v) body) b := by
  apply substComp_typed hb
  intro i t hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst t
      exact hv
  | succ i => exact .var hi

/-- Source application evaluates the callee first. The argument is shifted out
of the fresh callee binder before being delayed. -/
def sourceApply (callee argument : Comp R Empty) : Comp R Empty :=
  .bind callee (.dynamicCall (.var 0) (.delay (renameComp Nat.succ argument)))

theorem sourceApply_typed (hf : CompTyped xi emptyTy env callee (.callable a b))
    (ha : CompTyped xi emptyTy env argument a) : CompTyped xi emptyTy env (sourceApply callee argument) b :=
  .bind hf (.dynamicCall (.var rfl) (.delay (renameComp_typed ha (fun _ _ h => h))))

/-- Projection used only for a typed computation construction. Full adapters
remain in the plans below; this is not operational metadata erasure. -/
def adapterBody : Adapter R Empty → Comp R Empty
  | .mk _ _ body _ _ => body

theorem adapterBody_typed (h : AdapterTyped xi emptyTy env adapter a b) :
    CompTyped xi emptyTy (extend env a) (adapterBody adapter) b := by
  cases h with
  | mk h => exact h

def applyAdapter (adapter : Adapter R Empty) (v : Value R Empty) : Comp R Empty :=
  substComp (single v) (adapterBody adapter)

theorem applyAdapter_typed (h : AdapterTyped xi emptyTy env adapter a b)
    (hv : ValueTyped xi emptyTy env v a) : CompTyped xi emptyTy env (applyAdapter adapter v) b :=
  substitute_top (adapterBody_typed h) hv

def consumeResult (body : Comp R Empty) (consumer : Adapter R Empty) : Comp R Empty :=
  .bind body (adapterBody consumer)

theorem consumeResult_typed (hb : CompTyped xi emptyTy env body b)
    (hc : AdapterTyped xi emptyTy env consumer b r) : CompTyped xi emptyTy env (consumeResult body consumer) r :=
  .bind hb (adapterBody_typed hc)

/-- Value entry forces the carrier, then binds its value into the body. -/
def valueEntry (body : Comp R Empty) (carrier : Value R Empty) : Comp R Empty := .bind (.force carrier) body

theorem valueEntry_typed (hb : CompTyped xi emptyTy (extend env a) body b)
    (hc : ValueTyped xi emptyTy env carrier (.thunk a)) : CompTyped xi emptyTy env (valueEntry body carrier) b :=
  .bind (.force hc) hb

/-- Computation entry substitutes the carrier itself; no force is inserted. -/
def computationEntry (body : Comp R Empty) (carrier : Value R Empty) : Comp R Empty := substComp (single carrier) body

theorem computationEntry_typed (hb : CompTyped xi emptyTy (extend env (.thunk a)) body b)
    (hc : ValueTyped xi emptyTy env carrier (.thunk a)) : CompTyped xi emptyTy env (computationEntry body carrier) b :=
  substitute_top hb hc

structure LambdaEntryPlan (R : Type) where
  mode : Original.Mode
  receipt : ReceiptTemplate
  argument : Ty
  bodyResult : Ty
  result : Ty
  body : Comp R Empty
  consumer : Adapter R Empty
  carrier : Value R Empty

def LambdaEntryPlan.computation (p : LambdaEntryPlan R) : Comp R Empty :=
  consumeResult
    (match p.mode with
    | .value => valueEntry p.body p.carrier
    | .computation => computationEntry p.body p.carrier)
    p.consumer

theorem lambda_value_plan_typed (receipt : ReceiptTemplate)
    (hb : CompTyped xi emptyTy (extend env a) body b) (hc : AdapterTyped xi emptyTy env consumer b r)
    (ha : ValueTyped xi emptyTy env carrier (.thunk a)) :
    CompTyped xi emptyTy env (LambdaEntryPlan.computation
      ⟨.value, receipt, a, b, r, body, consumer, carrier⟩) r :=
  consumeResult_typed (valueEntry_typed hb ha) hc

theorem lambda_computation_plan_typed (receipt : ReceiptTemplate)
    (hb : CompTyped xi emptyTy (extend env (.thunk a)) body b) (hc : AdapterTyped xi emptyTy env consumer b r)
    (ha : ValueTyped xi emptyTy env carrier (.thunk a)) :
    CompTyped xi emptyTy env (LambdaEntryPlan.computation
      ⟨.computation, receipt, a, b, r, body, consumer, carrier⟩) r :=
  consumeResult_typed (computationEntry_typed hb ha) hc

/-- Input adaptation runs inside the delayed carrier. The output adapter runs
on the inner call's returned value. Entire adapter metadata is retained. -/
structure WrapEntryPlan (R : Type) where
  inner : Value R Empty
  input : Adapter R Empty
  output : Adapter R Empty
  carrier : Value R Empty

def WrapEntryPlan.computation (p : WrapEntryPlan R) : Comp R Empty :=
  consumeResult
    (.dynamicCall p.inner (.delay (.bind (.force p.carrier) (adapterBody p.input))))
    p.output

theorem wrap_plan_typed (hf : ValueTyped xi emptyTy env inner (.callable a b))
    (hi : AdapterTyped xi emptyTy env input c a) (ho : AdapterTyped xi emptyTy env output b d)
    (hc : ValueTyped xi emptyTy env carrier (.thunk c)) :
    CompTyped xi emptyTy env (WrapEntryPlan.computation ⟨inner, input, output, carrier⟩) d :=
  consumeResult_typed
    (.dynamicCall hf (.delay (.bind (.force hc) (adapterBody_typed hi)))) ho

/-- Complete annotations are retained as data, without claiming their semantic
adequacy. A view observation is an explicit transition, never silent erasure. -/
inductive Event (R : Type) where
  | silent
  | lookup (reference : R)
  | observeView (occurrence : ViewOccurrence)
  | lambdaEntry (plan : LambdaEntryPlan R)
  | wrapEntry (plan : WrapEntryPlan R)
  | leaveScope (owner : Nat)
  | leaveExpose (effectView resultView : ViewOccurrence)

/-- Independent operational rules: no rule contains a typing or safety premise.
Only the left side of bind and bodies of scope/expose are evaluation contexts. -/
inductive Step (graph : Graph R) : Comp R Empty → Event R → Comp R Empty → Prop where
  | forceRef : Step graph (.force (.ref r)) (.lookup r) (.force (graph r))
  | unionRef : Step graph (.unionCase (.ref r) l right) (.lookup r) (.unionCase (graph r) l right)
  | chooseLeftRef : Step graph (.chooseLeft (.ref r)) (.lookup r) (.chooseLeft (graph r))
  | chooseRightRef : Step graph (.chooseRight (.ref r)) (.lookup r) (.chooseRight (graph r))
  | absurdRef : Step graph (.absurd (.ref r)) (.lookup r) (.absurd (graph r))
  | callRef : Step graph (.dynamicCall (.ref r) arg) (.lookup r) (.dynamicCall (graph r) arg)
  | absurdView : Step graph (.absurd (.view v o)) (.observeView o) (.absurd v)
  | force : Step graph (.force (.delay body)) .silent body
  | forceView : Step graph (.force (.view v o)) (.observeView o) (.force v)
  | bindReturn : Step graph (.bind (.ret v) body) .silent (substComp (single v) body)
  | bind : Step graph m e n → Step graph (.bind m body) e (.bind n body)
  | unionLeft : Step graph (.unionCase (.inLeft v) l r) .silent (substComp (single v) l)
  | unionRight : Step graph (.unionCase (.inRight v) l r) .silent (substComp (single v) r)
  | unionView : Step graph (.unionCase (.view v o) l r) (.observeView o) (.unionCase v l r)
  | chooseLeft : Step graph (.chooseLeft (.both v)) .silent (.ret v)
  | chooseRight : Step graph (.chooseRight (.both v)) .silent (.ret v)
  | chooseLeftView : Step graph (.chooseLeft (.view v o)) (.observeView o) (.chooseLeft v)
  | chooseRightView : Step graph (.chooseRight (.view v o)) (.observeView o) (.chooseRight v)
  | scope : Step graph m e n → Step graph (.scope owner m) e (.scope owner n)
  | scopeReturn : Step graph (.scope owner (.ret v)) (.leaveScope owner) (.ret v)
  | expose : Step graph m e n → Step graph (.expose ev rv m) e (.expose ev rv n)
  | exposeReturn : Step graph (.expose ev rv (.ret v)) (.leaveExpose ev rv) (.ret v)
  | callView : Step graph (.dynamicCall (.view f o) arg) (.observeView o) (.dynamicCall f arg)
  | callLambda :
      Step graph (.dynamicCall (.lambda mode receipt a b r body consumer) carrier)
        (.lambdaEntry ⟨mode, receipt, a, b, r, body, consumer, carrier⟩)
        (LambdaEntryPlan.computation ⟨mode, receipt, a, b, r, body, consumer, carrier⟩)
  | callWrap :
      Step graph (.dynamicCall (.wrap inner input output) carrier)
        (.wrapEntry ⟨inner, input, output, carrier⟩)
        (WrapEntryPlan.computation ⟨inner, input, output, carrier⟩)

/-- Only explicit failure or an unhandled operation suspends execution. The
whole enclosing evaluation context and the original response binder remain. -/
inductive Suspended : Comp R Empty → Prop where
  | request (op payload continuation) : Suspended (.request op payload continuation)
  | fail (reason) : Suspended (.fail reason)
  | bind : Suspended m → Suspended (.bind m body)
  | scope : Suspended m → Suspended (.scope owner m)
  | expose : Suspended m → Suspended (.expose ev rv m)

inductive Returned : Comp R Empty → Prop where
  | ret (v : Value R Empty) : Returned (.ret v)

def CanProgress (m : Comp R Empty) : Prop :=
  Returned m ∨ Suspended m ∨ ∃ e n, Step graph m e n

theorem reference_type (h : ValueTyped xi emptyTy env (.ref r) a) : xi r = a := by
  cases h
  rfl

theorem preservation (hg : WellTyped graph xi) (step : Step graph m e n)
    (h : CompTyped xi emptyTy emptyContext m a) : CompTyped xi emptyTy emptyContext n a := by
  induction step generalizing a with
  | forceRef =>
      cases h with
      | force hv => exact .force ((reference_type hv) ▸ hg _)
  | unionRef =>
      cases h with
      | unionCase hv hl hr => exact .unionCase ((reference_type hv) ▸ hg _) hl hr
  | chooseLeftRef =>
      cases h with
      | chooseLeft hv => exact .chooseLeft ((reference_type hv) ▸ hg _)
  | chooseRightRef =>
      cases h with
      | chooseRight hv => exact .chooseRight ((reference_type hv) ▸ hg _)
  | absurdRef =>
      cases h with
      | absurd hv => exact .absurd ((reference_type hv) ▸ hg _)
  | callRef =>
      cases h with
      | dynamicCall hv ha => exact .dynamicCall ((reference_type hv) ▸ hg _) ha
  | absurdView =>
      cases h with
      | absurd hv => cases hv with | view hv => exact .absurd hv
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

theorem closed_progress (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : CompTyped xi emptyTy emptyContext m a) : CanProgress (graph := graph) m := by
  cases h with
  | ret _ => exact .inl (.ret _)
  | force hv =>
      obtain ⟨body, hh, _⟩ := thunk_observation (typed_observation hg guard hv)
      cases hh with
      | here => exact .inr (.inr ⟨_, _, .force⟩)
      | ref _ => exact .inr (.inr ⟨_, _, .forceRef⟩)
      | view _ => exact .inr (.inr ⟨_, _, .forceView⟩)
  | bind hm hb =>
      rcases closed_progress hg guard hm with hr | hs | ⟨e, n, step⟩
      · cases hr
        exact .inr (.inr ⟨_, _, .bindReturn⟩)
      · exact .inr (.inl (.bind hs))
      · exact .inr (.inr ⟨e, _, .bind step⟩)
  | unionCase hv hl hr =>
      rcases union_observation (typed_observation hg guard hv) with ⟨w, hh, _⟩ | ⟨w, hh, _⟩
      · cases hh with
        | here => exact .inr (.inr ⟨_, _, .unionLeft⟩)
        | ref _ => exact .inr (.inr ⟨_, _, .unionRef⟩)
        | view _ => exact .inr (.inr ⟨_, _, .unionView⟩)
      · cases hh with
        | here => exact .inr (.inr ⟨_, _, .unionRight⟩)
        | ref _ => exact .inr (.inr ⟨_, _, .unionRef⟩)
        | view _ => exact .inr (.inr ⟨_, _, .unionView⟩)
  | chooseLeft hv =>
      obtain ⟨w, hh, _, _⟩ := intersection_observation (typed_observation hg guard hv)
      cases hh with
      | here => exact .inr (.inr ⟨_, _, .chooseLeft⟩)
      | ref _ => exact .inr (.inr ⟨_, _, .chooseLeftRef⟩)
      | view _ => exact .inr (.inr ⟨_, _, .chooseLeftView⟩)
  | chooseRight hv =>
      obtain ⟨w, hh, _, _⟩ := intersection_observation (typed_observation hg guard hv)
      cases hh with
      | here => exact .inr (.inr ⟨_, _, .chooseRight⟩)
      | ref _ => exact .inr (.inr ⟨_, _, .chooseRightRef⟩)
      | view _ => exact .inr (.inr ⟨_, _, .chooseRightView⟩)
  | absurd hv => exact False.elim (bottom_empty hg guard hv)
  | scope hm =>
      rcases closed_progress hg guard hm with hr | hs | ⟨e, n, step⟩
      · cases hr
        exact .inr (.inr ⟨_, _, .scopeReturn⟩)
      · exact .inr (.inl (.scope hs))
      · exact .inr (.inr ⟨e, _, .scope step⟩)
  | expose hm =>
      rcases closed_progress hg guard hm with hr | hs | ⟨e, n, step⟩
      · cases hr
        exact .inr (.inr ⟨_, _, .exposeReturn⟩)
      · exact .inr (.inl (.expose hs))
      · exact .inr (.inr ⟨e, _, .expose step⟩)
  | request _ _ => exact .inr (.inl (.request _ _ _))
  | fail => exact .inr (.inl (.fail _))
  | dynamicCall hf ha =>
      obtain ⟨w, hh, ht⟩ := callable_observation (typed_observation hg guard hf)
      cases hh with
      | ref _ => exact .inr (.inr ⟨_, _, .callRef⟩)
      | view _ => exact .inr (.inr ⟨_, _, .callView⟩)
      | here =>
          cases ht with
          | lambdaValue _ _ => exact .inr (.inr ⟨_, _, .callLambda⟩)
          | lambdaComputation _ _ => exact .inr (.inr ⟨_, _, .callLambda⟩)
          | wrap _ _ _ => exact .inr (.inr ⟨_, _, .callWrap⟩)

theorem returned_no_step (h : Returned m) : ¬ Step graph m e n := by
  intro step
  cases h
  cases step

theorem suspended_no_step (h : Suspended m) : ¬ Step graph m e n := by
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
inductive EvalContext (R : Type) where
  | hole
  | bind (inner : EvalContext R) (body : Comp R Empty)
  | scope (owner : Nat) (inner : EvalContext R)
  | expose (ev rv : ViewOccurrence) (inner : EvalContext R)

def EvalContext.plug : EvalContext R → Comp R Empty → Comp R Empty
  | .hole, m => m
  | .bind k body, m => .bind (k.plug m) body
  | .scope owner k, m => .scope owner (k.plug m)
  | .expose ev rv k, m => .expose ev rv (k.plug m)

inductive ContextTyped (xi : R → Ty) (env : Context) : EvalContext R → Ty → Ty → Prop where
  | hole : ContextTyped xi env .hole a a
  | bind : ContextTyped xi env k a b → CompTyped xi emptyTy (extend env b) body c →
      ContextTyped xi env (.bind k body) a c
  | scope : ContextTyped xi env k a b → ContextTyped xi env (.scope owner k) a b
  | expose : ContextTyped xi env k a b → ContextTyped xi env (.expose ev rv k) a b

theorem plug_typed (hk : ContextTyped xi env k a b) (hm : CompTyped xi emptyTy env m a) :
    CompTyped xi emptyTy env (k.plug m) b := by
  induction hk with
  | hole => exact hm
  | bind _ hb ih => exact .bind (ih hm) hb
  | scope _ ih => exact .scope (ih hm)
  | expose _ ih => exact .expose (ih hm)

theorem context_inversion (k : EvalContext R) (h : CompTyped xi emptyTy env (k.plug m) b) :
    ∃ a, CompTyped xi emptyTy env m a ∧ ContextTyped xi env k a b := by
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
    (∃ k : EvalContext R, ∃ reason, m = k.plug (.fail reason)) ∨
    (∃ k : EvalContext R, ∃ op payload continuation, m = k.plug (.request op payload continuation)) := by
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
inductive Steps (graph : Graph R) : Comp R Empty → List (Event R) → Comp R Empty → Prop where
  | refl (m) : Steps graph m [] m
  | cons : Step graph m e n → Steps graph n trace last → Steps graph m (e :: trace) last

theorem trace_preservation (hg : WellTyped graph xi) (steps : Steps graph m trace n)
    (h : CompTyped xi emptyTy emptyContext m a) : CompTyped xi emptyTy emptyContext n a := by
  induction steps generalizing a with
  | refl => exact h
  | cons step rest ih => exact ih (preservation hg step h)

/-- The finite canonical lookup is realized by actual raw reference/view
steps followed by the force rule. No assumed transition is used. -/
theorem force_observation_execution (h : Head graph v (.delay body)) :
    ∃ trace, Steps graph (.force v) trace body := by
  have aux : ∀ (v w : Value R Empty), Head graph v w →
      ∀ body, w = .delay body → ∃ trace, Steps graph (.force v) trace body := by
    intro v w observation
    induction observation with
    | here v =>
        intro body equal
        cases equal
        exact ⟨_, .cons .force (.refl _)⟩
    | ref _ ih =>
        intro body equal
        obtain ⟨trace, steps⟩ := ih body equal
        exact ⟨_, .cons .forceRef steps⟩
    | view _ ih =>
        intro body equal
        obtain ⟨trace, steps⟩ := ih body equal
        exact ⟨_, .cons .forceView steps⟩
  exact aux _ _ h body rfl

/-- Quantifies over every finite prefix, not a selected successful execution. -/
theorem finite_prefix_safety (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : CompTyped xi emptyTy emptyContext m a) (steps : Steps graph m trace n) :
    CompTyped xi emptyTy emptyContext n a ∧ CanProgress (graph := graph) n := by
  have hn := trace_preservation hg steps h
  exact ⟨hn, closed_progress hg guard hn⟩

/-- An actual operation response remains independently quantified. -/
theorem resume_request_typed
    (h : CompTyped xi emptyTy env (.request op payload continuation) a)
    (response : Value R Empty) (hr : ValueTyped xi emptyTy env response op.responseType) :
    CompTyped xi emptyTy env (substComp (single response) continuation) a := by
  cases h with
  | request _ hk => exact substitute_top hk hr

/-- Independent response and enclosing-context quantifiers are both retained.
No local lambda action stands in for the foreign continuation. -/
theorem resume_in_context_typed (k : EvalContext R)
    (h : CompTyped xi emptyTy env (k.plug (.request op payload continuation)) a)
    (response : Value R Empty) (hr : ValueTyped xi emptyTy env response op.responseType) :
    CompTyped xi emptyTy env (k.plug (substComp (single response) continuation)) a := by
  obtain ⟨b, hm, hk⟩ := context_inversion k h
  exact plug_typed hk (resume_request_typed hm response hr)

/-- Viewed Force is represented explicitly, with the exact occurrence retained. -/
theorem viewed_force (v : Value R Empty) (o : ViewOccurrence) :
    Step graph (.force (.view v o)) (.observeView o) (.force v) := .forceView

/-- Computation entry passes the original thunk without forcing it. -/
theorem computation_entry_equation (receipt a b r body consumer) (carrier : Value R Empty) :
    (LambdaEntryPlan.mk .computation receipt a b r body consumer carrier).computation =
      .bind (substComp (single carrier) body) (adapterBody consumer) := rfl

/-- Value entry forces before body execution, then applies the result consumer. -/
theorem value_entry_equation (receipt a b r body consumer) (carrier : Value R Empty) :
    (LambdaEntryPlan.mk .value receipt a b r body consumer carrier).computation =
      .bind (.bind (.force carrier) body) (adapterBody consumer) := rfl

/-- Input adaptation is inside the delayed carrier; output adaptation waits for
an inner result. This equation rules out premature argument adaptation. -/
theorem wrap_entry_equation (inner : Value R Empty) (input output : Adapter R Empty) (carrier : Value R Empty) :
    (WrapEntryPlan.mk inner input output carrier).computation =
      .bind (.dynamicCall inner (.delay (.bind (.force carrier) (adapterBody input))))
        (adapterBody output) := rfl


/-- Concrete four-way alternative. Requests and failures are distinct finite
context decompositions; neither is an arbitrary stuck computation. -/
def Failed (m : Comp R Empty) : Prop := ∃ k : EvalContext R, ∃ reason, m = k.plug (.fail reason)
def Requested (m : Comp R Empty) : Prop :=
  ∃ k : EvalContext R, ∃ op payload continuation, m = k.plug (.request op payload continuation)

theorem progress_four (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : CompTyped xi emptyTy emptyContext m a) :
    Returned m ∨ Requested m ∨ Failed m ∨ ∃ e n, Step graph m e n := by
  rcases closed_progress hg guard h with hr | hs | hn
  · exact .inl hr
  · rcases suspended_decomposition hs with hf | hq
    · exact .inr (.inr (.inl hf))
    · exact .inr (.inl hq)
  · exact .inr (.inr (.inr hn))

theorem context_suspended (k : EvalContext R) (h : Suspended m) : Suspended (k.plug m) := by
  induction k with
  | hole => exact h
  | bind _ _ ih => exact .bind ih
  | scope _ _ ih => exact .scope ih
  | expose _ _ _ ih => exact .expose ih

theorem failed_no_step (h : Failed m) : ¬ Step graph m e n := by
  obtain ⟨k, reason, rfl⟩ := h
  exact suspended_no_step (context_suspended k (.fail reason))

theorem requested_no_step (h : Requested m) : ¬ Step graph m e n := by
  obtain ⟨k, op, payload, continuation, rfl⟩ := h
  exact suspended_no_step (context_suspended k (.request op payload continuation))

/-- A request's original response binder and the independent outer evaluation
context are derived from the concrete suspended computation's typing. -/
theorem request_context_typing (k : EvalContext R)
    (h : CompTyped xi emptyTy emptyContext (k.plug (.request op payload continuation)) a) :
    ∃ b, ValueTyped xi emptyTy emptyContext payload op.payloadType ∧
      CompTyped xi emptyTy (extend emptyContext op.responseType) continuation b ∧
      ContextTyped xi emptyContext k b a := by
  obtain ⟨b, hb, hk⟩ := context_inversion k h
  cases hb with
  | request hp hc => exact ⟨b, hp, hc, hk⟩

/-- Parent application: actual source RHS and body derivations, independently
typed old captures, and the actual finite fresh-cycle criterion supply every
node observation and every finite internal prefix after simultaneous allocation.
There is no dynamic rec instruction in this accepted grammar. -/
theorem source_rec_execution {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → HigherOrder.Value)
    (hrhs : ∀ s, HigherOrder.ValueTyped (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : HigherOrder.CompTyped (sourceContext nu env) body a) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) ∧
    (∀ r, ObservedTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu)
      (.ref r) (joinTy xi nu r)) ∧
    (∀ trace last, Steps (allocate graph (sourceFresh capture rhs))
      (sourceCloseComp capture n body) trace last →
      CompTyped (joinTy xi nu) emptyTy emptyContext last a ∧
      CanProgress (graph := allocate graph (sourceFresh capture rhs)) last) := by
  obtain ⟨ht, ⟨guard'⟩, hb⟩ := source_rec_allocation hg guard rhs hrhs hcapture hcycle hbody
  exact ⟨ht, (fun r => typed_observation ht guard' (.ref r)),
    (fun _ _ steps => finite_prefix_safety ht guard' hb steps)⟩

theorem finite_source_rec_execution {graph : Graph (Fin m)}
    {xi : Fin m → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi)
    (hOld : GuardedValueGraph.FiniteDecision.NoCycle (projectGraph graph))
    (rhs : Fin n → HigherOrder.Value)
    (hrhs : ∀ s, HigherOrder.ValueTyped (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : HigherOrder.CompTyped (sourceContext nu env) body a) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) ∧
    (∀ r, ObservedTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu)
      (.ref r) (joinTy xi nu r)) ∧
    (∀ trace last, Steps (allocate graph (sourceFresh capture rhs))
      (sourceCloseComp capture n body) trace last →
      CompTyped (joinTy xi nu) emptyTy emptyContext last a ∧
      CanProgress (graph := allocate graph (sourceFresh capture rhs)) last) :=
  source_rec_execution hg (GuardedValueGraph.FiniteDecision.guardOfNoCycle _ hOld)
    rhs hrhs hcapture hcycle hbody

/-- The explicit-name variant covers old references appearing in RHS code. -/
theorem named_rec_execution {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R (Fin n))
    (hrhs : ∀ s, ValueTyped xi nu env (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (fun s => closeValue capture (rhs s)))
    (hbody : CompTyped xi nu env body a)
    (steps : Steps (allocate graph (fun s => closeValue capture (rhs s)))
      (closeComp capture body) trace last) :
    CompTyped (joinTy xi nu) emptyTy emptyContext last a ∧
    CanProgress (graph := allocate graph (fun s => closeValue capture (rhs s))) last := by
  obtain ⟨ht, ⟨guard'⟩, hb⟩ := named_rec_allocation hg guard rhs hrhs hcapture hcycle hbody
  exact finite_prefix_safety ht guard' hb steps

namespace Examples
open YulangClosure.HigherOrderGraph.Examples

abbrev MutualRef := Sum (Fin 1) (Fin 2)
def mutualGraph : Graph MutualRef := allocate oldGraph mutualFresh
def carrier : Value MutualRef Empty := .delay (.ret .unit)
def callAt (s : Fin 2) : Comp MutualRef Empty := .dynamicCall (.ref (.inr s)) carrier
def callNode (s : Fin 2) : Comp MutualRef Empty := .dynamicCall (mutualFresh s) carrier
def consumerBody : Comp MutualRef Empty := .bind (.ret (.ref (.inl 0))) (.ret (.var 1))
def mutualPlan (s : Fin 2) : LambdaEntryPlan MutualRef :=
  ⟨.computation, receipt, unitTy, unitTy, unitTy,
    .bind (.ret (.ref (.inl 0))) (.dynamicCall (.ref (.inr (other s))) (.var 1)),
    .mk unitTy unitTy consumerBody [] [], carrier⟩
def entered (s : Fin 2) : Comp MutualRef Empty := (mutualPlan s).computation

theorem mutual_lookup (s : Fin 2) :
    Step mutualGraph (callAt s) (.lookup (.inr s)) (callNode s) := .callRef

theorem mutual_entry (s : Fin 2) :
    Step mutualGraph (callNode s) (.lambdaEntry (mutualPlan s)) (entered s) := by
  unfold callNode
  rw [mutualFresh_equation]
  exact .callLambda

theorem mutual_body_return (s : Fin 2) :
    Step mutualGraph (entered s) .silent (.bind (callAt (other s)) consumerBody) :=
  .bind .bindReturn

/-- Actual five-step prefix reaches the OTHER allocated lambda, retaining the
first result consumer. Recursive call/consumer accumulation is not collapsed. -/
theorem mutual_two_entries (s : Fin 2) :
    ∃ trace, Steps mutualGraph (callAt s) trace (.bind (entered (other s)) consumerBody) :=
  ⟨_, .cons (mutual_lookup s) (.cons (mutual_entry s)
    (.cons (mutual_body_return s) (.cons (.bind (mutual_lookup (other s)))
      (.cons (.bind (mutual_entry (other s))) (.refl _)))))⟩

def mutualSourceBody : HigherOrder.Comp := .dynamicCall (.var 0) (.delay (.ret .unit))

theorem mutualSourceBody_typed :
    HigherOrder.CompTyped (sourceContext (fun _ : Fin 2 => functionTy) outer)
      mutualSourceBody unitTy := .dynamicCall (.var rfl) (.delay (.ret .unit))

theorem mutual_source_closed : sourceCloseComp capture 2 mutualSourceBody = callAt 0 := rfl

/-- Source-derived safety for ALL finite prefixes of the actual recursive call,
not merely for the exhibited five steps. -/
theorem mutual_all_prefixes (steps : Steps mutualGraph (callAt 0) trace last) :
    CompTyped (joinTy oldTypes (fun _ : Fin 2 => functionTy)) emptyTy emptyContext last unitTy ∧
    CanProgress (graph := mutualGraph) last :=
  (source_rec_execution old_typed oldGuard mutualRhs mutualRhs_typed capture_typed
    mutualFresh_noCycle mutualSourceBody_typed).2.2 trace last steps

/-- Delayed recursive request uses the actual source response binder unchanged. -/
def requestFresh := sourceFresh capture (fun _ : Fin 1 => responseRhs)
def requestGraph := allocate oldGraph requestFresh
def requestSourceBody : HigherOrder.Comp := .force (.var 0)

theorem requestFresh_noCycle : FreshNoCycle requestFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem requestSourceBody_typed :
    HigherOrder.CompTyped (sourceContext (fun _ : Fin 1 => .thunk functionTy) outer)
      requestSourceBody functionTy := .force (.var rfl)

theorem request_two_steps :
    Steps requestGraph (sourceCloseComp capture 1 requestSourceBody)
      [.lookup (.inr 0), .silent]
      (.request operation (.ref (.inl 0))
        (.bind (.ret (.ref (.inr 0))) (.ret (.var 1)))) :=
  .cons .forceRef (.cons .force (.refl _))

theorem request_all_prefixes
    (steps : Steps requestGraph (sourceCloseComp capture 1 requestSourceBody) trace last) :
    CompTyped (joinTy oldTypes (fun _ : Fin 1 => .thunk functionTy)) emptyTy emptyContext last functionTy ∧
    CanProgress (graph := requestGraph) last :=
  (source_rec_execution old_typed oldGuard (fun _ : Fin 1 => responseRhs)
    (fun _ => responseRhs_typed) capture_typed requestFresh_noCycle requestSourceBody_typed).2.2 trace last steps

end Examples

end YulangClosure.HigherOrderGraph.Safety
