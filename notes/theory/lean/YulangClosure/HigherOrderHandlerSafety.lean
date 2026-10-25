import YulangClosure.HigherOrderHandlerSyntax

namespace YulangClosure.HigherOrder.Handler
open YulangClosure.HigherOrder (Ty Context emptyContext extend OperationInstance
  ViewOccurrence ReceiptTemplate PathCorrespondence)

/-! Actual raw higher-order shallow handler transitions. This is candidate
value typing, not the effect/permission or activation-freshening theorem. -/

deriving instance DecidableEq for Ty
deriving instance DecidableEq for OperationInstance

/-- Source application evaluates the callee first. The argument is shifted out
of the fresh callee binder before being delayed. -/
def sourceApply (callee argument : Comp) : Comp :=
  .bind callee (.dynamicCall (.var 0) (.delay (renameComp Nat.succ argument)))

theorem sourceApply_typed (hf : CompTyped env callee (.callable a b))
    (ha : CompTyped env argument a) : CompTyped env (sourceApply callee argument) b :=
  .bind hf (.dynamicCall (.var rfl) (.delay (renameComp_typed ha (fun _ _ h => h))))

/-- Projection used only for a typed computation construction. Full adapters
remain in the plans below; this is not operational metadata erasure. -/
def adapterBody : Adapter → Comp
  | .mk _ _ body _ _ => body

theorem adapterBody_typed (h : AdapterTyped env adapter a b) :
    CompTyped (extend env a) (adapterBody adapter) b := by
  cases h with
  | mk h => exact h

def applyAdapter (adapter : Adapter) (v : Value) : Comp :=
  substComp (single v) (adapterBody adapter)

theorem applyAdapter_typed (h : AdapterTyped env adapter a b)
    (hv : ValueTyped env v a) : CompTyped env (applyAdapter adapter v) b :=
  substitute_top (adapterBody_typed h) hv

def consumeResult (body : Comp) (consumer : Adapter) : Comp :=
  .bind body (adapterBody consumer)

theorem consumeResult_typed (hb : CompTyped env body b)
    (hc : AdapterTyped env consumer b r) : CompTyped env (consumeResult body consumer) r :=
  .bind hb (adapterBody_typed hc)

/-- Value entry forces the carrier, then binds its value into the body. -/
def valueEntry (body : Comp) (carrier : Value) : Comp := .bind (.force carrier) body

theorem valueEntry_typed (hb : CompTyped (extend env a) body b)
    (hc : ValueTyped env carrier (.thunk a)) : CompTyped env (valueEntry body carrier) b :=
  .bind (.force hc) hb

/-- Computation entry substitutes the carrier itself; no force is inserted. -/
def computationEntry (body : Comp) (carrier : Value) : Comp := substComp (single carrier) body

theorem computationEntry_typed (hb : CompTyped (extend env (.thunk a)) body b)
    (hc : ValueTyped env carrier (.thunk a)) : CompTyped env (computationEntry body carrier) b :=
  substitute_top hb hc

structure LambdaEntryPlan where
  mode : Original.Mode
  receipt : ReceiptTemplate
  argument : Ty
  bodyResult : Ty
  result : Ty
  body : Comp
  consumer : Adapter
  carrier : Value

def LambdaEntryPlan.computation (p : LambdaEntryPlan) : Comp :=
  consumeResult
    (match p.mode with
    | .value => valueEntry p.body p.carrier
    | .computation => computationEntry p.body p.carrier)
    p.consumer

theorem lambda_value_plan_typed (receipt : ReceiptTemplate)
    (hb : CompTyped (extend env a) body b) (hc : AdapterTyped env consumer b r)
    (ha : ValueTyped env carrier (.thunk a)) :
    CompTyped env (LambdaEntryPlan.computation
      ⟨.value, receipt, a, b, r, body, consumer, carrier⟩) r :=
  consumeResult_typed (valueEntry_typed hb ha) hc

theorem lambda_computation_plan_typed (receipt : ReceiptTemplate)
    (hb : CompTyped (extend env (.thunk a)) body b) (hc : AdapterTyped env consumer b r)
    (ha : ValueTyped env carrier (.thunk a)) :
    CompTyped env (LambdaEntryPlan.computation
      ⟨.computation, receipt, a, b, r, body, consumer, carrier⟩) r :=
  consumeResult_typed (computationEntry_typed hb ha) hc

/-- Input adaptation runs inside the delayed carrier. The output adapter runs
on the inner call's returned value. Entire adapter metadata is retained. -/
structure WrapEntryPlan where
  inner : Value
  input : Adapter
  output : Adapter
  carrier : Value

def WrapEntryPlan.computation (p : WrapEntryPlan) : Comp :=
  consumeResult
    (.dynamicCall p.inner (.delay (.bind (.force p.carrier) (adapterBody p.input))))
    p.output

theorem wrap_plan_typed (hf : ValueTyped env inner (.callable a b))
    (hi : AdapterTyped env input c a) (ho : AdapterTyped env output b d)
    (hc : ValueTyped env carrier (.thunk c)) :
    CompTyped env (WrapEntryPlan.computation ⟨inner, input, output, carrier⟩) d :=
  consumeResult_typed
    (.dynamicCall hf (.delay (.bind (.force hc) (adapterBody_typed hi)))) ho

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


def Handler.input : Handler → Ty
  | .mk _ a _ _ _ => a

def Handler.values : Handler → ValueArms
  | .mk _ _ _ vs _ => vs

def Handler.operations : Handler → OperationArms
  | .mk _ _ _ _ os => os

theorem handler_input (hh : HandlerTyped env h a b) : h.input = a := by
  cases hh
  rfl

theorem handler_values (hh : HandlerTyped env h a b) : ValueArmsTyped env h.values a b := by
  cases hh with
  | mk hv _ => exact hv

theorem handler_operations (hh : HandlerTyped env h a b) : OperationArmsTyped env h.operations a b := by
  cases hh with
  | mk _ ho => exact ho

/-- A concrete callable encoding of K. Its actual response binder is the
lambda parameter, and its result adapter is the identity computation. -/
def continuationValue (q a : Ty) (k : Comp) : Value :=
  .lambda .value ⟨[], []⟩ q a a k (.mk a a (.ret (.var 0)) [] [])

theorem continuationValue_typed (hk : CompTyped (extend env q) k a) :
    ValueTyped env (continuationValue q a k) (.callable q a) :=
  .lambdaValue hk (.mk (.ret (.var rfl)))

def pairSubstitution (payload continuation : Value) : Nat → Value
  | 0 => payload
  | 1 => continuation
  | n+2 => .var n

theorem substitute_pair
    (hb : CompTyped (extend (extend env kty) pty) body b)
    (hp : ValueTyped env p pty) (hk : ValueTyped env k kty) :
    CompTyped env (substComp (pairSubstitution p k) body) b := by
  apply substComp_typed hb
  intro i t hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst t
      exact hp
  | succ i =>
      cases i with
      | zero =>
          simp only [extend, Option.some.injEq] at hi
          subst t
          exact hk
      | succ i => exact .var hi

def attemptOperation (h : Handler) (op : OperationInstance) (p : Value) (k body : Comp) : Comp :=
  substComp (pairSubstitution p (continuationValue op.responseType h.input k)) body

theorem attemptOperation_typed (hh : HandlerTyped env h a b)
    (hp : ValueTyped env p op.payloadType) (hk : CompTyped (extend env op.responseType) k a)
    (hb : CompTyped (extend (extend env (.callable op.responseType a)) op.payloadType)
      body (.union (.base .unit) b)) :
    CompTyped env (attemptOperation h op p k body) (.union (.base .unit) b) := by
  unfold attemptOperation
  rw [handler_input hh]
  exact substitute_pair hb hp (continuationValue_typed hk)

/-- H K is separately constructed by reinstating the shifted handler under
K's response binder. It is never passed to a selected operation arm. -/
def forwardedContinuation (h : Handler) (k : Comp) : Comp :=
  .handle (renameHandler Nat.succ h) k

theorem forwardedContinuation_typed (hh : HandlerTyped env h a b)
    (hk : CompTyped (extend env q) k a) :
    CompTyped (extend env q) (forwardedContinuation h k) b :=
  .handle (renameHandler_typed hh (fun _ _ h => h)) hk

inductive Event where
  | silent
  | observeView (occurrence : ViewOccurrence)
  | lambdaEntry (plan : LambdaEntryPlan)
  | wrapEntry (plan : WrapEntryPlan)
  | leaveScope (owner : Nat)
  | leaveExpose (effectView resultView : ViewOccurrence)

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

  | bindRequest : Step (.bind (.request op p k) body) .silent
      (.request op p (.bind k (renameComp (Original.up Nat.succ) body)))
  | bindFail : Step (.bind (.fail reason) body) .silent (.fail reason)
  | scopeRequest : Step (.scope owner (.request op p k)) .silent
      (.request op p (.scope owner k))
  | scopeFail : Step (.scope owner (.fail reason)) .silent (.fail reason)
  | exposeRequest : Step (.expose ev rv (.request op p k)) .silent
      (.request op p (.expose ev rv k))
  | exposeFail : Step (.expose ev rv (.fail reason)) .silent (.fail reason)
  | handle : Step m e n → Step (.handle h m) e (.handle h n)
  | handleReturn : Step (.handle h (.ret v)) .silent (.tryValue h v h.values)
  | handleRequest : Step (.handle h (.request op p k)) .silent
      (.tryOperation h op p k h.operations)
  | handleFail : Step (.handle h (.fail reason)) .silent (.fail reason)
  | valueEmpty : Step (.tryValue h v .nil) .silent (.fail .matchFailure)
  | valueCons : Step (.tryValue h v (.cons body rest)) .silent
      (.waitValue h v rest (substComp (single v) body))
  | valueWait : Step m e n → Step (.waitValue h v rest m) e (.waitValue h v rest n)
  | valueYes : Step (.waitValue h v rest (.ret (.inRight result))) .silent (.ret result)
  | valueNo : Step (.waitValue h v rest (.ret (.inLeft unit))) .silent (.tryValue h v rest)
  | valueView : Step (.waitValue h v rest (.ret (.view result o))) (.observeView o)
      (.waitValue h v rest (.ret result))
  | valueFail : Step (.waitValue h v rest (.fail reason)) .silent (.fail reason)
  | valueRequest : Step (.waitValue h v rest (.request op p k)) .silent
      (.request op p (.waitValue (renameHandler Nat.succ h) (renameValue Nat.succ v)
        (renameValueArms Nat.succ rest) k))
  | operationEmpty : Step (.tryOperation h op p k .nil) .silent
      (.request op p (forwardedContinuation h k))
  | operationCons : Step (.tryOperation h op p k (.cons op true body rest)) .silent
      (.waitOperation h op p k rest (attemptOperation h op p k body))
  | operationSkip : (armOp ≠ op ∨ eligible = false) →
      Step (.tryOperation h op p k (.cons armOp eligible body rest)) .silent
        (.tryOperation h op p k rest)
  | operationWait : Step m e n →
      Step (.waitOperation h op p k rest m) e (.waitOperation h op p k rest n)
  | operationYes : Step (.waitOperation h op p k rest (.ret (.inRight result))) .silent (.ret result)
  | operationNo : Step (.waitOperation h op p k rest (.ret (.inLeft unit))) .silent
      (.tryOperation h op p k rest)
  | operationView : Step (.waitOperation h op p k rest (.ret (.view result o))) (.observeView o)
      (.waitOperation h op p k rest (.ret result))
  | operationFail : Step (.waitOperation h op p k rest (.fail reason)) .silent (.fail reason)
  | operationRequest : Step (.waitOperation h op p k rest (.request nextOp nextP nextK)) .silent
      (.request nextOp nextP (.waitOperation (renameHandler Nat.succ h) op
        (renameValue Nat.succ p) (renameComp (Original.up Nat.succ) k)
        (renameOperationArms Nat.succ rest) nextK))

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

  | bindRequest =>
      cases h with
      | bind hm hb => cases hm with
        | request hp hk => exact .request hp (.bind hk (renameComp_typed hb (up_typed (env := env) (target := extend env _) (r := Nat.succ) (fun _ _ h => h) _)))
  | bindFail => exact .fail
  | scopeRequest =>
      cases h with
      | scope hm => cases hm with
        | request hp hk => exact .request hp (.scope hk)
  | scopeFail => exact .fail
  | exposeRequest =>
      cases h with
      | expose hm => cases hm with
        | request hp hk => exact .request hp (.expose hk)
  | exposeFail => exact .fail
  | handle _ ih =>
      cases h with
      | handle hh hm => exact .handle hh (ih hm)
  | handleReturn =>
      cases h with
      | handle hh hm => cases hm with
        | ret hv => exact .tryValue hh hv (handler_values hh)
  | handleRequest =>
      cases h with
      | handle hh hm => cases hm with
        | request hp hk => exact .tryOperation hh hp hk (handler_operations hh)
  | handleFail => exact .fail
  | valueEmpty => exact .fail
  | valueCons =>
      cases h with
      | tryValue hh hv hs => cases hs with
        | cons hb hr => exact .waitValue hh hv hr (substitute_top hb hv)
  | valueWait _ ih =>
      cases h with
      | waitValue hh hv hr hm => exact .waitValue hh hv hr (ih hm)
  | valueYes =>
      cases h with
      | waitValue _ _ _ hm => cases hm with
        | ret hv => cases hv with
          | inRight hv => exact .ret hv
  | valueNo =>
      cases h with
      | waitValue hh hv hr _ => exact .tryValue hh hv hr
  | valueView =>
      cases h with
      | waitValue hh hv hr hm => cases hm with
        | ret hv' => cases hv' with
          | view hv' => exact .waitValue hh hv hr (.ret hv')
  | valueFail => exact .fail
  | valueRequest =>
      cases h with
      | waitValue hh hv hr hm => cases hm with
        | request hp hk => exact .request hp (.waitValue
            (renameHandler_typed hh (fun _ _ h => h))
            (renameValue_typed hv (fun _ _ h => h))
            (renameValueArms_typed hr (fun _ _ h => h)) hk)
  | operationEmpty =>
      cases h with
      | tryOperation hh hp hk _ => exact .request hp (forwardedContinuation_typed hh hk)
  | operationCons =>
      cases h with
      | tryOperation hh hp hk hs => cases hs with
        | cons hb hr => exact .waitOperation hh hp hk hr (attemptOperation_typed hh hp hk hb)
  | operationSkip _ =>
      cases h with
      | tryOperation hh hp hk hs => cases hs with
        | cons _ hr => exact .tryOperation hh hp hk hr
  | operationWait _ ih =>
      cases h with
      | waitOperation hh hp hk hr hm => exact .waitOperation hh hp hk hr (ih hm)
  | operationYes =>
      cases h with
      | waitOperation _ _ _ _ hm => cases hm with
        | ret hv => cases hv with
          | inRight hv => exact .ret hv
  | operationNo =>
      cases h with
      | waitOperation hh hp hk hr _ => exact .tryOperation hh hp hk hr
  | operationView =>
      cases h with
      | waitOperation hh hp hk hr hm => cases hm with
        | ret hv => cases hv with
          | view hv => exact .waitOperation hh hp hk hr (.ret hv)
  | operationFail => exact .fail
  | operationRequest =>
      cases h with
      | waitOperation hh hp hk hr hm => cases hm with
        | request hp' hk' => exact .request hp' (.waitOperation
            (renameHandler_typed hh (fun _ _ h => h))
            (renameValue_typed hp (fun _ _ h => h))
            (renameComp_typed hk (up_typed (env := env) (target := extend env _) (r := Nat.succ) (fun _ _ h => h) _))
            (renameOperationArms_typed hr (fun _ _ h => h)) hk')

/-- The terminal alternatives are only the three concrete outer constructors;
requests and failures underneath a frame must take their propagation step. -/
inductive Terminal : Comp → Prop where
  | returned (v : Value) : Terminal (.ret v)
  | requested (op p k) : Terminal (.request op p k)
  | failed (reason) : Terminal (.fail reason)

def CanProgress (m : Comp) : Prop := Terminal m ∨ ∃ e n, Step m e n

theorem operation_trials_progress (h : Handler) (op : OperationInstance)
    (p : Value) (k : Comp) (arms : OperationArms) : CanProgress (.tryOperation h op p k arms) := by
  cases arms with
  | nil => exact .inr ⟨_, _, .operationEmpty⟩
  | cons armOp eligible body rest =>
      cases eligible with
      | false => exact .inr ⟨_, _, .operationSkip (.inr rfl)⟩
      | true =>
          by_cases equal : armOp = op
          · subst armOp
            exact .inr ⟨_, _, .operationCons⟩
          · exact .inr ⟨_, _, .operationSkip (.inl equal)⟩

theorem closed_progress (h : CompTyped emptyContext m a) : CanProgress m := by
  cases h with
  | ret _ => exact .inl (.returned _)
  | request _ _ => exact .inl (.requested _ _ _)
  | fail => exact .inl (.failed _)
  | force hv =>
      cases thunk_canonical hv with
      | delay _ => exact .inr ⟨_, _, .force⟩
      | view _ => exact .inr ⟨_, _, .forceView⟩
  | bind hm hb =>
      rcases closed_progress hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .bindReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .bindRequest⟩
        | failed _ => exact .inr ⟨_, _, .bindFail⟩
      · exact .inr ⟨e, _, .bind step⟩
  | unionCase hv hl hr =>
      cases union_canonical hv with
      | left _ => exact .inr ⟨_, _, .unionLeft⟩
      | right _ => exact .inr ⟨_, _, .unionRight⟩
      | view _ => exact .inr ⟨_, _, .unionView⟩
  | chooseLeft hv =>
      cases intersection_canonical hv with
      | both _ => exact .inr ⟨_, _, .chooseLeft⟩
      | view _ => exact .inr ⟨_, _, .chooseLeftView⟩
  | chooseRight hv =>
      cases intersection_canonical hv with
      | both _ => exact .inr ⟨_, _, .chooseRight⟩
      | view _ => exact .inr ⟨_, _, .chooseRightView⟩
  | absurd hv => exact False.elim (bottom_empty hv)
  | scope hm =>
      rcases closed_progress hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .scopeReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .scopeRequest⟩
        | failed _ => exact .inr ⟨_, _, .scopeFail⟩
      · exact .inr ⟨e, _, .scope step⟩
  | expose hm =>
      rcases closed_progress hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .exposeReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .exposeRequest⟩
        | failed _ => exact .inr ⟨_, _, .exposeFail⟩
      · exact .inr ⟨e, _, .expose step⟩
  | dynamicCall hf ha =>
      cases callable_canonical hf with
      | lambda _ _ _ _ _ _ _ => exact .inr ⟨_, _, .callLambda⟩
      | wrap _ => exact .inr ⟨_, _, .callWrap⟩
      | view _ => exact .inr ⟨_, _, .callView⟩
  | handle hh hm =>
      rcases closed_progress hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .handleReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .handleRequest⟩
        | failed _ => exact .inr ⟨_, _, .handleFail⟩
      · exact .inr ⟨e, _, .handle step⟩
  | tryValue hh hv hs =>
      cases hs with
      | nil => exact .inr ⟨_, _, .valueEmpty⟩
      | cons _ _ => exact .inr ⟨_, _, .valueCons⟩
  | waitValue hh hv hs hm =>
      rcases closed_progress hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned v =>
            cases hm with
            | ret hv =>
                cases union_canonical hv with
                | left _ => exact .inr ⟨_, _, .valueNo⟩
                | right _ => exact .inr ⟨_, _, .valueYes⟩
                | view _ => exact .inr ⟨_, _, .valueView⟩
        | requested _ _ _ => exact .inr ⟨_, _, .valueRequest⟩
        | failed _ => exact .inr ⟨_, _, .valueFail⟩
      · exact .inr ⟨e, _, .valueWait step⟩
  | tryOperation hh hp hk hs => exact operation_trials_progress _ _ _ _ _
  | waitOperation hh hp hk hs hm =>
      rcases closed_progress hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned v =>
            cases hm with
            | ret hv =>
                cases union_canonical hv with
                | left _ => exact .inr ⟨_, _, .operationNo⟩
                | right _ => exact .inr ⟨_, _, .operationYes⟩
                | view _ => exact .inr ⟨_, _, .operationView⟩
        | requested _ _ _ => exact .inr ⟨_, _, .operationRequest⟩
        | failed _ => exact .inr ⟨_, _, .operationFail⟩
      · exact .inr ⟨e, _, .operationWait step⟩

inductive Prefix : Comp → List Event → Comp → Prop where
  | refl (m : Comp) : Prefix m [] m
  | cons : Step m e n → Prefix n events last → Prefix m (e :: events) last

theorem prefix_preservation (trace : Prefix m events n) (h : CompTyped env m a) :
    CompTyped env n a := by
  induction trace generalizing env a with
  | refl => exact h
  | cons step _ ih => exact ih (preservation step h)

/-- All raw finite internal prefixes, including arbitrary actual attempt code. -/
theorem finite_prefix_safety (h : CompTyped emptyContext m a) (trace : Prefix m events n) :
    CompTyped emptyContext n a ∧ CanProgress n := by
  have hn := prefix_preservation trace h
  exact ⟨hn, closed_progress hn⟩

theorem embedded_program_safety (h : HigherOrder.CompTyped emptyContext m a)
    (trace : Prefix (embedComp m) events n) : CompTyped emptyContext n a ∧ CanProgress n :=
  finite_prefix_safety (embedComp_typed h) trace

/-- No linear-use premise: every independently typed response can be substituted
into the same saved code, which is not consumed or modified. -/
theorem resume_typed (hk : CompTyped (extend env q) k a) (hv : ValueTyped env v q) :
    CompTyped env (substComp (single v) k) a := substitute_top hk hv

theorem many_responses_typed (hk : CompTyped (extend env q) k a)
    (responses : List Value) (typed : ∀ v, v ∈ responses → ValueTyped env v q) :
    ∀ v, v ∈ responses → CompTyped env (substComp (single v) k) a :=
  fun v member => resume_typed hk (typed v member)

/-! Distinguishing applications of the universal candidate proofs. -/

def unitType : Ty := .base .unit
def boolType : Ty := .base .bool
def unitOperation : OperationInstance := ⟨20, [], unitType, unitType⟩
def nestedOperation : OperationInstance := ⟨21, [], unitType, boolType⟩

def noAttempt : Comp := .ret (.inLeft .unit)
def yesAttempt : Comp := .ret (.inRight (.bool true))

/-- The arm actually invokes its shallow continuation (index one), passing
its payload (index zero) through a delayed carrier, before returning Yes. -/
def callingAttempt : Comp :=
  .bind (.dynamicCall (.var 1) (.delay (.ret (.var 0)))) yesAttempt

def selectedHandler : Handler :=
  .mk 70 unitType boolType (.cons yesAttempt .nil)
    (.cons unitOperation true callingAttempt .nil)

theorem selectedHandler_typed : HandlerTyped emptyContext selectedHandler unitType boolType :=
  .mk (.cons (.ret (.inRight .bool)) .nil)
    (.cons (.bind (.dynamicCall (.var rfl) (.delay (.ret (.var rfl))))
      (.ret (.inRight .bool))) .nil)

def selectedProgram : Comp :=
  .handle selectedHandler (.request unitOperation .unit (.ret (.var 0)))

theorem selectedProgram_typed : CompTyped emptyContext selectedProgram boolType :=
  .handle selectedHandler_typed (.request .unit (.ret (.var rfl)))

/-- Full actual execution of the attempt, including a higher-order call to K.
The caller's result is unit, while the enclosing handler's result is bool. -/
theorem selected_execution : ∃ events, Prefix selectedProgram events (.ret (.bool true)) := by
  refine ⟨[.silent, .silent,
    .lambdaEntry ⟨.value, ⟨[], []⟩, unitType, unitType, unitType,
      .ret (.var 0), .mk unitType unitType (.ret (.var 0)) [] [], .delay (.ret .unit)⟩,
    .silent, .silent, .silent, .silent, .silent], ?_⟩
  refine .cons .handleRequest (.cons .operationCons ?_)
  refine .cons (.operationWait (.bind .callLambda)) ?_
  refine .cons (.operationWait (.bind (.bind (.bind .force)))) ?_
  refine .cons (.operationWait (.bind (.bind .bindReturn))) ?_
  refine .cons (.operationWait (.bind .bindReturn)) ?_
  refine .cons (.operationWait .bindReturn) ?_
  exact .cons .operationYes (.refl _)

theorem selected_execution_safe : ∃ events,
    Prefix selectedProgram events (.ret (.bool true)) ∧
    CompTyped emptyContext (.ret (.bool true)) boolType ∧ CanProgress (.ret (.bool true)) := by
  obtain ⟨events, trace⟩ := selected_execution
  exact ⟨events, trace, finite_prefix_safety selectedProgram_typed trace⟩

/-- The original code is the lambda body, with no handler inserted. -/
theorem selected_continuation_is_original (h : Handler) (op : OperationInstance)
    (p : Value) (k body : Comp) :
    attemptOperation h op p k body = substComp
      (pairSubstitution p (.lambda .value ⟨[], []⟩ op.responseType h.input h.input k
        (.mk h.input h.input (.ret (.var 0)) [] []))) body := rfl

def forwardingHandler : Handler := .mk 71 unitType boolType (.cons yesAttempt .nil) .nil

theorem forwardingHandler_typed : HandlerTyped emptyContext forwardingHandler unitType boolType :=
  .mk (.cons (.ret (.inRight .bool)) .nil) .nil

theorem forwarded_execution :
    Prefix (.handle forwardingHandler (.request unitOperation .unit (.ret (.var 0))))
      [.silent, .silent]
      (.request unitOperation .unit
        (forwardedContinuation forwardingHandler (.ret (.var 0)))) :=
  .cons .handleRequest (.cons .operationEmpty (.refl _))

theorem forwarded_execution_safe :
    CompTyped emptyContext (.request unitOperation .unit
      (forwardedContinuation forwardingHandler (.ret (.var 0)))) boolType ∧
    CanProgress (.request unitOperation .unit
      (forwardedContinuation forwardingHandler (.ret (.var 0)))) :=
  finite_prefix_safety
    (.handle forwardingHandler_typed (.request .unit (.ret (.var rfl)))) forwarded_execution

/-- Original K returns unit; the forwarded continuation returns bool. -/
theorem distinct_continuation_types :
    ValueTyped emptyContext (continuationValue unitType unitType (.ret (.var 0)))
      (.callable unitType unitType) ∧
    CompTyped (extend emptyContext unitType)
      (forwardedContinuation forwardingHandler (.ret (.var 0))) boolType :=
  ⟨continuationValue_typed (.ret (.var rfl)),
    forwardedContinuation_typed forwardingHandler_typed (.ret (.var rfl))⟩

def orderedHandler : Handler :=
  .mk 72 unitType boolType (.cons noAttempt (.cons yesAttempt .nil)) .nil

theorem orderedHandler_typed : HandlerTyped emptyContext orderedHandler unitType boolType :=
  .mk (.cons (.ret (.inLeft .unit)) (.cons (.ret (.inRight .bool)) .nil)) .nil

theorem ordered_value_trials :
    Prefix (.handle orderedHandler (.ret .unit))
      [.silent, .silent, .silent, .silent, .silent] (.ret (.bool true)) :=
  .cons .handleReturn (.cons .valueCons (.cons .valueNo
    (.cons .valueCons (.cons .valueYes (.refl _)))))

theorem ordered_value_trials_safe : CompTyped emptyContext (.ret (.bool true)) boolType ∧
    CanProgress (.ret (.bool true)) :=
  finite_prefix_safety (.handle orderedHandler_typed (.ret .unit)) ordered_value_trials

/-- The two exhaustion cases have different actual successors. -/
theorem value_exhaustion (h : Handler) (v : Value) :
    Step (.tryValue h v .nil) .silent (.fail .matchFailure) := .valueEmpty

theorem operation_exhaustion (h : Handler) (op : OperationInstance) (p : Value) (k : Comp) :
    Step (.tryOperation h op p k .nil) .silent
      (.request op p (.handle (renameHandler Nat.succ h) k)) := .operationEmpty

/-- Same payload/response types do not suffice to select a different operation. -/
def unrelatedOperation : OperationInstance := ⟨200, [], unitType, unitType⟩

theorem wrong_identity_skipped (h : Handler) (p : Value) (k body : Comp) (rest : OperationArms) :
    Step (.tryOperation h unitOperation p k (.cons unrelatedOperation true body rest)) .silent
      (.tryOperation h unitOperation p k rest) := by
  apply Step.operationSkip
  apply Or.inl
  intro equal
  have impossible : (200 : Nat) = 20 := congrArg OperationInstance.operation equal
  cases impossible

/-- Ordered type arguments are part of the compared instance too. -/
def otherArgumentsOperation : OperationInstance := ⟨20, [boolType], unitType, unitType⟩

theorem wrong_arguments_skipped (h : Handler) (p : Value) (k body : Comp) (rest : OperationArms) :
    Step (.tryOperation h unitOperation p k (.cons otherArgumentsOperation true body rest)) .silent
      (.tryOperation h unitOperation p k rest) := by
  apply Step.operationSkip
  apply Or.inl
  intro equal
  have impossible : [boolType] = ([] : List Ty) := congrArg OperationInstance.typeArguments equal
  cases impossible

/-- Explicit permission data affects selection only; the typing premise for
this arm remains present even when eligibility is false. -/
theorem ineligible_skipped (h : Handler) (op : OperationInstance) (p : Value)
    (k body : Comp) (rest : OperationArms) :
    Step (.tryOperation h op p k (.cons op false body rest)) .silent
      (.tryOperation h op p k rest) := .operationSkip (.inr rfl)

def nestedWait : Comp :=
  .waitOperation forwardingHandler unitOperation .unit (.ret (.var 0)) .nil
    (.request nestedOperation .unit noAttempt)

theorem nestedWait_typed : CompTyped emptyContext nestedWait boolType :=
  .waitOperation forwardingHandler_typed .unit (.ret (.var rfl)) .nil
    (.request .unit (.ret (.inLeft .unit)))

def nestedRestoration : Comp :=
  .waitOperation (renameHandler Nat.succ forwardingHandler) unitOperation
    (renameValue Nat.succ .unit) (renameComp (Original.up Nat.succ) (.ret (.var 0)))
    (renameOperationArms Nat.succ .nil) noAttempt

theorem nested_request_restores_pending_wait :
    Step nestedWait .silent (.request nestedOperation .unit nestedRestoration) := .operationRequest

theorem nested_request_restoration_typed :
    CompTyped emptyContext (.request nestedOperation .unit nestedRestoration) boolType :=
  preservation nested_request_restores_pending_wait nestedWait_typed

theorem nested_response_restoration_typed (response : Value)
    (hr : ValueTyped emptyContext response boolType) :
    CompTyped emptyContext (substComp (single response) nestedRestoration) boolType := by
  have typed := nested_request_restoration_typed
  cases typed with
  | request _ hk => exact resume_typed hk hr

/-- A completed trial event remains in the trace before No advances the
ordered plan. No rule restores a pre-attempt world or replays earlier code. -/
theorem no_after_event (h : Handler) (op : OperationInstance) (p : Value)
    (k : Comp) (rest : OperationArms) :
    Prefix (.waitOperation h op p k rest (.scope 37 noAttempt))
      [.leaveScope 37, .silent] (.tryOperation h op p k rest) :=
  .cons (.operationWait .scopeReturn) (.cons .operationNo (.refl _))

/-- Nested extended forms under both lambda and adapter binders. The result
consumer is in the lambda's outer context; it is not under its parameter. -/
def nestedLambda : Value :=
  .lambda .value ⟨[], []⟩ unitType boolType boolType
    (.handle forwardingHandler (.ret (.var 0)))
    (.mk boolType boolType
      (.handle (.mk 73 boolType boolType (.cons (.ret (.inRight (.var 0))) .nil) .nil)
        (.ret (.var 0))) [] [])

theorem nestedLambda_typed : ValueTyped emptyContext nestedLambda (.callable unitType boolType) :=
  .lambdaValue
    (.handle (.mk (.cons (.ret (.inRight .bool)) .nil) .nil) (.ret (.var rfl)))
    (.mk (.handle (.mk (.cons (.ret (.inRight (.var rfl))) .nil) .nil) (.ret (.var rfl))))

theorem nested_lambda_call_safe
    (trace : Prefix (.dynamicCall nestedLambda (.delay (.ret .unit))) events n) :
    CompTyped emptyContext n boolType ∧ CanProgress n :=
  finite_prefix_safety (.dynamicCall nestedLambda_typed (.delay (.ret .unit))) trace

end YulangClosure.HigherOrder.Handler
