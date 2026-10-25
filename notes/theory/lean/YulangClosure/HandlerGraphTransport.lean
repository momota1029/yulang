import YulangClosure.HandlerGraphSafety

/-! Six-sort immutable reference transport for the actual combined machine.
Local binders and recursive names are unchanged. Candidate research theorem. -/
namespace YulangClosure.HandlerGraph.Extension
open HigherOrder (Ty Context emptyContext extend OperationInstance)
variable {R S T U : Type} {xi : R → Ty} {nu : S → Ty} {tau : T → Ty}

mutual
  def mapValue (f : R → T) : Value R S → Value T S
    | .ref r => .ref (f r)
    | .recvar s => .recvar s
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (mapComp f m)
    | .inLeft v => .inLeft (mapValue f v)
    | .inRight v => .inRight (mapValue f v)
    | .both v => .both (mapValue f v)
    | .top v => .top (mapValue f v)
    | .view v o => .view (mapValue f v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (mapComp f body) (mapAdapter f consumer)
    | .wrap inner input output => .wrap (mapValue f inner) (mapAdapter f input) (mapAdapter f output)
  def mapComp (f : R → T) : Comp R S → Comp T S
    | .ret v => .ret (mapValue f v)
    | .force v => .force (mapValue f v)
    | .chooseLeft v => .chooseLeft (mapValue f v)
    | .chooseRight v => .chooseRight (mapValue f v)
    | .absurd v => .absurd (mapValue f v)
    | .bind m n => .bind (mapComp f m) (mapComp f n)
    | .unionCase v l right => .unionCase (mapValue f v) (mapComp f l) (mapComp f right)
    | .scope owner body => .scope owner (mapComp f body)
    | .expose ev rv body => .expose ev rv (mapComp f body)
    | .request op v k => .request op (mapValue f v) (mapComp f k)
    | .fail reason => .fail reason
    | .dynamicCall inner a => .dynamicCall (mapValue f inner) (mapValue f a)
    | .handle h m => .handle (mapHandler f h) (mapComp f m)
    | .tryValue h v arms => .tryValue (mapHandler f h) (mapValue f v) (mapValueArms f arms)
    | .waitValue h v arms attempt => .waitValue (mapHandler f h) (mapValue f v)
        (mapValueArms f arms) (mapComp f attempt)
    | .tryOperation h op p k arms => .tryOperation (mapHandler f h) op (mapValue f p)
        (mapComp f k) (mapOperationArms f arms)
    | .waitOperation h op p k arms attempt => .waitOperation (mapHandler f h) op (mapValue f p)
        (mapComp f k) (mapOperationArms f arms) (mapComp f attempt)
  def mapHandler (f : R → T) : Handler R S → Handler T S
    | .mk id a b vs os => .mk id a b (mapValueArms f vs) (mapOperationArms f os)
  def mapValueArms (f : R → T) : ValueArms R S → ValueArms T S
    | .nil => .nil
    | .cons body rest => .cons (mapComp f body) (mapValueArms f rest)
  def mapOperationArms (f : R → T) : OperationArms R S → OperationArms T S
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (mapComp f body)
        (mapOperationArms f rest)
  def mapAdapter (f : R → T) : Adapter R S → Adapter T S
    | .mk a b body paths views => .mk a b (mapComp f body) paths views
end

mutual
  theorem mapValue_typed (h : ValueTyped xi nu env v a) (f : R → T) (hf : ∀ r, tau (f r) = xi r) :
      ValueTyped tau nu env (mapValue f v) a := by
    cases h with
    | ref r => simpa only [mapValue, hf] using (ValueTyped.ref (xi := tau) (nu := nu) (env := env) (f r))
    | recvar s => exact .recvar s
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (mapComp_typed h f hf)
    | inLeft h => exact .inLeft (mapValue_typed h f hf)
    | inRight h => exact .inRight (mapValue_typed h f hf)
    | top h => exact .top (mapValue_typed h f hf)
    | view h => exact .view (mapValue_typed h f hf)
    | both h k => exact .both (mapValue_typed h f hf) (mapValue_typed k f hf)
    | lambdaValue h k => exact .lambdaValue (mapComp_typed h f hf) (mapAdapter_typed k f hf)
    | lambdaComputation h k => exact .lambdaComputation (mapComp_typed h f hf) (mapAdapter_typed k f hf)
    | wrap h i o => exact .wrap (mapValue_typed h f hf) (mapAdapter_typed i f hf) (mapAdapter_typed o f hf)
  theorem mapComp_typed (h : CompTyped xi nu env m a) (f : R → T) (hf : ∀ r, tau (f r) = xi r) :
      CompTyped tau nu env (mapComp f m) a := by
    cases h with
    | ret h => exact .ret (mapValue_typed h f hf)
    | force h => exact .force (mapValue_typed h f hf)
    | chooseLeft h => exact .chooseLeft (mapValue_typed h f hf)
    | chooseRight h => exact .chooseRight (mapValue_typed h f hf)
    | absurd h => exact .absurd (mapValue_typed h f hf)
    | bind h k => exact .bind (mapComp_typed h f hf) (mapComp_typed k f hf)
    | unionCase h l r =>
        exact .unionCase (mapValue_typed h f hf)
          (mapComp_typed l f hf) (mapComp_typed r f hf)
    | scope h => exact .scope (mapComp_typed h f hf)
    | expose h => exact .expose (mapComp_typed h f hf)
    | request h k => exact .request (mapValue_typed h f hf) (mapComp_typed k f hf)
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (mapValue_typed h f hf) (mapValue_typed k f hf)
    | handle hh hm => exact .handle (mapHandler_typed hh f hf) (mapComp_typed hm f hf)
    | tryValue hh hv hs => exact .tryValue (mapHandler_typed hh f hf) (mapValue_typed hv f hf) (mapValueArms_typed hs f hf)
    | waitValue hh hv hs hm => exact .waitValue (mapHandler_typed hh f hf) (mapValue_typed hv f hf) (mapValueArms_typed hs f hf) (mapComp_typed hm f hf)
    | tryOperation hh hp hk hs => exact .tryOperation (mapHandler_typed hh f hf) (mapValue_typed hp f hf) (mapComp_typed hk f hf) (mapOperationArms_typed hs f hf)
    | waitOperation hh hp hk hs hm => exact .waitOperation (mapHandler_typed hh f hf) (mapValue_typed hp f hf) (mapComp_typed hk f hf) (mapOperationArms_typed hs f hf) (mapComp_typed hm f hf)
  theorem mapHandler_typed (h : HandlerTyped xi nu env handler a b) (f : R → T) (hf : ∀ r, tau (f r) = xi r) :
      HandlerTyped tau nu env (mapHandler f handler) a b := by
    cases h with
    | mk hv ho => exact .mk (mapValueArms_typed hv f hf) (mapOperationArms_typed ho f hf)
  theorem mapValueArms_typed (h : ValueArmsTyped xi nu env arms a b) (f : R → T) (hf : ∀ r, tau (f r) = xi r) :
      ValueArmsTyped tau nu env (mapValueArms f arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (mapComp_typed hb f hf) (mapValueArms_typed hr f hf)
  theorem mapOperationArms_typed (h : OperationArmsTyped xi nu env arms a b) (f : R → T) (hf : ∀ r, tau (f r) = xi r) :
      OperationArmsTyped tau nu env (mapOperationArms f arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (mapComp_typed hb f hf) (mapOperationArms_typed hr f hf)
  theorem mapAdapter_typed (h : AdapterTyped xi nu env adapter a b) (f : R → T) (hf : ∀ r, tau (f r) = xi r) :
      AdapterTyped tau nu env (mapAdapter f adapter) a b := by
    cases h with
    | mk h => exact .mk (mapComp_typed h f hf)
end

mutual
  theorem mapValue_id (v : Value R S) :
      mapValue id v = v := by
    cases v <;> simp only [mapValue, mapValue_id, mapComp_id, mapAdapter_id, id]
  theorem mapComp_id (v : Comp R S) :
      mapComp id v = v := by
    cases v <;> simp only [mapComp, mapValue_id, mapComp_id, mapHandler_id, mapValueArms_id, mapOperationArms_id]
  theorem mapHandler_id (v : Handler R S) :
      mapHandler id v = v := by
    cases v <;> simp only [mapHandler, mapValueArms_id, mapOperationArms_id]
  theorem mapValueArms_id (v : ValueArms R S) :
      mapValueArms id v = v := by
    cases v <;> simp only [mapValueArms, mapComp_id, mapValueArms_id]
  theorem mapOperationArms_id (v : OperationArms R S) :
      mapOperationArms id v = v := by
    cases v <;> simp only [mapOperationArms, mapComp_id, mapOperationArms_id]
  theorem mapAdapter_id (v : Adapter R S) :
      mapAdapter id v = v := by
    cases v <;> simp only [mapAdapter, mapComp_id]
end

mutual
  theorem mapValue_comp (f : R → T) (g : T → U) (v : Value R S) :
      mapValue g (mapValue f v) = mapValue (fun r => g (f r)) v := by
    cases v <;> simp only [mapValue, mapValue_comp, mapComp_comp, mapAdapter_comp]
  theorem mapComp_comp (f : R → T) (g : T → U) (v : Comp R S) :
      mapComp g (mapComp f v) = mapComp (fun r => g (f r)) v := by
    cases v <;> simp only [mapComp, mapValue_comp, mapComp_comp, mapHandler_comp, mapValueArms_comp, mapOperationArms_comp]
  theorem mapHandler_comp (f : R → T) (g : T → U) (v : Handler R S) :
      mapHandler g (mapHandler f v) = mapHandler (fun r => g (f r)) v := by
    cases v <;> simp only [mapHandler, mapValueArms_comp, mapOperationArms_comp]
  theorem mapValueArms_comp (f : R → T) (g : T → U) (v : ValueArms R S) :
      mapValueArms g (mapValueArms f v) = mapValueArms (fun r => g (f r)) v := by
    cases v <;> simp only [mapValueArms, mapComp_comp, mapValueArms_comp]
  theorem mapOperationArms_comp (f : R → T) (g : T → U) (v : OperationArms R S) :
      mapOperationArms g (mapOperationArms f v) = mapOperationArms (fun r => g (f r)) v := by
    cases v <;> simp only [mapOperationArms, mapComp_comp, mapOperationArms_comp]
  theorem mapAdapter_comp (f : R → T) (g : T → U) (v : Adapter R S) :
      mapAdapter g (mapAdapter f v) = mapAdapter (fun r => g (f r)) v := by
    cases v <;> simp only [mapAdapter, mapComp_comp]
end

mutual
  theorem mapValue_rename (f : R → T) (r : Nat → Nat) (v : Value R S) :
      mapValue f (renameValue r v) = renameValue r (mapValue f v) := by
    cases v <;> simp only [mapValue, renameValue, mapValue_rename, mapComp_rename, mapAdapter_rename]
  theorem mapComp_rename (f : R → T) (r : Nat → Nat) (v : Comp R S) :
      mapComp f (renameComp r v) = renameComp r (mapComp f v) := by
    cases v <;> simp only [mapComp, renameComp, mapValue_rename, mapComp_rename, mapHandler_rename, mapValueArms_rename, mapOperationArms_rename]
  theorem mapHandler_rename (f : R → T) (r : Nat → Nat) (v : Handler R S) :
      mapHandler f (renameHandler r v) = renameHandler r (mapHandler f v) := by
    cases v <;> simp only [mapHandler, renameHandler, mapValueArms_rename, mapOperationArms_rename]
  theorem mapValueArms_rename (f : R → T) (r : Nat → Nat) (v : ValueArms R S) :
      mapValueArms f (renameValueArms r v) = renameValueArms r (mapValueArms f v) := by
    cases v <;> simp only [mapValueArms, renameValueArms, mapComp_rename, mapValueArms_rename]
  theorem mapOperationArms_rename (f : R → T) (r : Nat → Nat) (v : OperationArms R S) :
      mapOperationArms f (renameOperationArms r v) = renameOperationArms r (mapOperationArms f v) := by
    cases v <;> simp only [mapOperationArms, renameOperationArms, mapComp_rename, mapOperationArms_rename]
  theorem mapAdapter_rename (f : R → T) (r : Nat → Nat) (v : Adapter R S) :
      mapAdapter f (renameAdapter r v) = renameAdapter r (mapAdapter f v) := by
    cases v <;> simp only [mapAdapter, renameAdapter, mapComp_rename]
end

theorem map_lift (f : R → T) (s : Nat → Value R S) :
    (fun i => mapValue f (lift s i)) = lift (fun i => mapValue f (s i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact mapValue_rename f Nat.succ (s i)

mutual
  theorem mapValue_subst (f : R → T) (s : Nat → Value R S) (v : Value R S) :
      mapValue f (substValue s v) = substValue (fun i => mapValue f (s i)) (mapValue f v) := by
    cases v <;> simp only [mapValue, substValue, mapValue_subst, mapComp_subst, mapAdapter_subst, map_lift]
  theorem mapComp_subst (f : R → T) (s : Nat → Value R S) (v : Comp R S) :
      mapComp f (substComp s v) = substComp (fun i => mapValue f (s i)) (mapComp f v) := by
    cases v <;> simp only [mapComp, substComp, mapValue_subst, mapComp_subst, mapHandler_subst, mapValueArms_subst, mapOperationArms_subst, map_lift]
  theorem mapHandler_subst (f : R → T) (s : Nat → Value R S) (v : Handler R S) :
      mapHandler f (substHandler s v) = substHandler (fun i => mapValue f (s i)) (mapHandler f v) := by
    cases v <;> simp only [mapHandler, substHandler, mapValueArms_subst, mapOperationArms_subst]
  theorem mapValueArms_subst (f : R → T) (s : Nat → Value R S) (v : ValueArms R S) :
      mapValueArms f (substValueArms s v) = substValueArms (fun i => mapValue f (s i)) (mapValueArms f v) := by
    cases v <;> simp only [mapValueArms, substValueArms, mapComp_subst, mapValueArms_subst, map_lift]
  theorem mapOperationArms_subst (f : R → T) (s : Nat → Value R S) (v : OperationArms R S) :
      mapOperationArms f (substOperationArms s v) = substOperationArms (fun i => mapValue f (s i)) (mapOperationArms f v) := by
    cases v <;> simp only [mapOperationArms, substOperationArms, mapComp_subst, mapOperationArms_subst, map_lift]
  theorem mapAdapter_subst (f : R → T) (s : Nat → Value R S) (v : Adapter R S) :
      mapAdapter f (substAdapter s v) = substAdapter (fun i => mapValue f (s i)) (mapAdapter f v) := by
    cases v <;> simp only [mapAdapter, substAdapter, mapComp_subst, map_lift]
end

theorem map_single (f : R → T) (v : Value R Empty) :
    (fun i => mapValue f (single v i)) = single (mapValue f v) := by
  funext i
  cases i <;> rfl

theorem map_substitute_top (f : R → T) (v : Value R Empty) (body : Comp R Empty) :
    mapComp f (substComp (single v) body) =
      substComp (single (mapValue f v)) (mapComp f body) := by
  rw [mapComp_subst, map_single]

/-- An extension constrains actual old node bytes structurally. It assumes no
execution, observation, preservation or saved-continuation law. -/
structure Embedding (old : Graph R) (xi : R → Ty) (new : Graph T) (tau : T → Ty) where
  refs : R → T
  injective : ∀ {r s}, refs r = refs s → r = s
  types : ∀ r, tau (refs r) = xi r
  nodes : ∀ r, new (refs r) = mapValue refs (old r)

def Embedding.refl (graph : Graph R) (xi : R → Ty) : Embedding graph xi graph xi where
  refs := id
  injective := fun {_ _} h => h
  types := fun _ => rfl
  nodes := fun r => (mapValue_id (graph r)).symm

def Embedding.trans {g : Graph R} {h : Graph T} {k : Graph U}
    {xi : R → Ty} {tau : T → Ty} {ups : U → Ty}
    (e : Embedding g xi h tau) (d : Embedding h tau k ups) : Embedding g xi k ups where
  refs := fun r => d.refs (e.refs r)
  injective := fun {_ _} eq => e.injective (d.injective eq)
  types := fun r => (d.types (e.refs r)).trans (e.types r)
  nodes := by
    intro r
    rw [d.nodes, e.nodes, mapValue_comp]

theorem collision_rejected {g : Graph R} {h : Graph T}
    (e : Embedding g xi h tau) {r s : R} (distinct : r ≠ s) : e.refs r ≠ e.refs s :=
  fun eq => distinct (e.injective eq)

theorem overwrite_rejected {g : Graph R} {h : Graph T}
    (e : Embedding g xi h tau) (r : R) (changed : h (e.refs r) ≠ mapValue e.refs (g r)) : False :=
  changed (e.nodes r)

def mapLambdaPlan (f : R → T) (p : LambdaEntryPlan R) : LambdaEntryPlan T :=
  ⟨p.mode, p.receipt, p.argument, p.bodyResult, p.result,
    mapComp f p.body, mapAdapter f p.consumer, mapValue f p.carrier⟩

def mapWrapPlan (f : R → T) (p : WrapEntryPlan R) : WrapEntryPlan T :=
  ⟨mapValue f p.inner, mapAdapter f p.input, mapAdapter f p.output, mapValue f p.carrier⟩

def mapEvent (f : R → T) : Event R → Event T
  | .silent => .silent
  | .lookup r => .lookup (f r)
  | .observeView o => .observeView o
  | .lambdaEntry p => .lambdaEntry (mapLambdaPlan f p)
  | .wrapEntry p => .wrapEntry (mapWrapPlan f p)
  | .leaveScope owner => .leaveScope owner
  | .leaveExpose ev rv => .leaveExpose ev rv

theorem map_adapterBody (f : R → T) (a : Adapter R Empty) :
    mapComp f (adapterBody a) = adapterBody (mapAdapter f a) := by cases a; rfl

theorem map_lambda_computation (f : R → T) (p : LambdaEntryPlan R) :
    mapComp f p.computation = (mapLambdaPlan f p).computation := by
  cases p with
  | mk mode receipt a b r body consumer carrier =>
      cases mode <;> simp only [LambdaEntryPlan.computation, mapLambdaPlan,
        consumeResult, valueEntry, computationEntry, mapComp,
        map_adapterBody, map_substitute_top]

theorem map_wrap_computation (f : R → T) (p : WrapEntryPlan R) :
    mapComp f p.computation = (mapWrapPlan f p).computation := by
  cases p
  simp only [WrapEntryPlan.computation, mapWrapPlan, consumeResult, mapComp,
    mapValue, map_adapterBody]

theorem map_handler_input (f : R → T) (h : Handler R Empty) :
    (mapHandler f h).input = h.input := by cases h; rfl

theorem map_handler_values (f : R → T) (h : Handler R Empty) :
    mapValueArms f h.values = (mapHandler f h).values := by cases h; rfl

theorem map_handler_operations (f : R → T) (h : Handler R Empty) :
    mapOperationArms f h.operations = (mapHandler f h).operations := by cases h; rfl

theorem map_continuationValue (f : R → T) (q a : Ty) (k : Comp R Empty) :
    mapValue f (continuationValue q a k) = continuationValue q a (mapComp f k) := rfl

theorem map_pairSubstitution (f : R → T) (p k : Value R Empty) :
    (fun i => mapValue f (pairSubstitution p k i)) =
      pairSubstitution (mapValue f p) (mapValue f k) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem map_attemptOperation (f : R → T) (h : Handler R Empty)
    (op : OperationInstance) (p : Value R Empty) (k body : Comp R Empty) :
    mapComp f (attemptOperation h op p k body) =
      attemptOperation (mapHandler f h) op (mapValue f p) (mapComp f k) (mapComp f body) := by
  simp only [attemptOperation, mapComp_subst, map_pairSubstitution,
    map_continuationValue, map_handler_input]

theorem map_forwardedContinuation (f : R → T) (h : Handler R Empty) (k : Comp R Empty) :
    mapComp f (forwardedContinuation h k) =
      forwardedContinuation (mapHandler f h) (mapComp f k) := by
  simp only [forwardedContinuation, mapComp, mapHandler_rename]

/-- All actual raw combined-machine rules transport, with no typing assumption
on the step. In particular both wait lookups and K/HK stay distinct. -/
theorem map_step {g : Graph R} {h : Graph T}
    (e : Embedding g xi h tau) (step : Step g m event n) :
    Step h (mapComp e.refs m) (mapEvent e.refs event) (mapComp e.refs n) := by
  induction step with
  | forceRef => simpa only [mapComp, mapValue, mapEvent, e.nodes] using (Step.forceRef (graph := h) (r := e.refs _))
  | unionRef => simpa only [mapComp, mapValue, mapEvent, e.nodes] using (Step.unionRef (graph := h) (r := e.refs _) (l := mapComp e.refs _) (right := mapComp e.refs _))
  | chooseLeftRef => simpa only [mapComp, mapValue, mapEvent, e.nodes] using (Step.chooseLeftRef (graph := h) (r := e.refs _))
  | chooseRightRef => simpa only [mapComp, mapValue, mapEvent, e.nodes] using (Step.chooseRightRef (graph := h) (r := e.refs _))
  | absurdRef => simpa only [mapComp, mapValue, mapEvent, e.nodes] using (Step.absurdRef (graph := h) (r := e.refs _))
  | callRef => simpa only [mapComp, mapValue, mapEvent, e.nodes] using (Step.callRef (graph := h) (r := e.refs _) (arg := mapValue e.refs _))
  | valueRef =>
      simpa only [mapComp, mapValue, mapEvent, e.nodes] using
        (Step.valueRef (graph := h) (h := mapHandler e.refs _) (v := mapValue e.refs _)
          (rest := mapValueArms e.refs _) (r := e.refs _))
  | operationRef =>
      simpa only [mapComp, mapValue, mapEvent, e.nodes] using
        (Step.operationRef (graph := h) (h := mapHandler e.refs _) (op := _)
          (p := mapValue e.refs _) (k := mapComp e.refs _)
          (rest := mapOperationArms e.refs _) (r := e.refs _))
  | absurdView => exact .absurdView
  | force => exact .force
  | forceView => exact .forceView
  | bindReturn => simpa only [mapComp, mapValue, mapEvent, map_substitute_top] using (Step.bindReturn (graph := h) (v := mapValue e.refs _) (body := mapComp e.refs _))
  | bind _ ih => exact .bind ih
  | unionLeft => simpa only [mapComp, mapValue, mapEvent, map_substitute_top] using (Step.unionLeft (graph := h) (v := mapValue e.refs _) (l := mapComp e.refs _) (r := mapComp e.refs _))
  | unionRight => simpa only [mapComp, mapValue, mapEvent, map_substitute_top] using (Step.unionRight (graph := h) (v := mapValue e.refs _) (l := mapComp e.refs _) (r := mapComp e.refs _))
  | unionView => exact .unionView
  | chooseLeft => exact .chooseLeft
  | chooseRight => exact .chooseRight
  | chooseLeftView => exact .chooseLeftView
  | chooseRightView => exact .chooseRightView
  | scope _ ih => exact .scope ih
  | scopeReturn => exact .scopeReturn
  | expose _ ih => exact .expose ih
  | exposeReturn => exact .exposeReturn
  | callView => exact .callView
  | callLambda =>
      rw [map_lambda_computation]
      exact .callLambda
  | callWrap =>
      rw [map_wrap_computation]
      exact .callWrap
  | bindRequest =>
      simpa only [mapComp, mapEvent, mapComp_rename] using
        (Step.bindRequest (graph := h) (op := _) (p := mapValue e.refs _)
          (k := mapComp e.refs _) (body := mapComp e.refs _))
  | bindFail => exact .bindFail
  | scopeRequest => exact .scopeRequest
  | scopeFail => exact .scopeFail
  | exposeRequest => exact .exposeRequest
  | exposeFail => exact .exposeFail
  | handle _ ih => exact .handle ih
  | handleReturn =>
      simpa only [mapComp, mapEvent, map_handler_values] using
        (Step.handleReturn (graph := h) (h := mapHandler e.refs _) (v := mapValue e.refs _))
  | handleRequest =>
      simpa only [mapComp, mapEvent, map_handler_operations] using
        (Step.handleRequest (graph := h) (h := mapHandler e.refs _) (op := _)
          (p := mapValue e.refs _) (k := mapComp e.refs _))
  | handleFail => exact .handleFail
  | valueEmpty => exact .valueEmpty
  | valueCons =>
      simpa only [mapComp, mapValueArms, mapEvent, map_substitute_top] using
        (Step.valueCons (graph := h) (h := mapHandler e.refs _) (v := mapValue e.refs _)
          (body := mapComp e.refs _) (rest := mapValueArms e.refs _))
  | valueWait _ ih => exact .valueWait ih
  | valueYes => exact .valueYes
  | valueNo => exact .valueNo
  | valueView => exact .valueView
  | valueFail => exact .valueFail
  | valueRequest =>
      simpa only [mapComp, mapEvent, mapHandler_rename, mapValue_rename,
        mapValueArms_rename] using
        (Step.valueRequest (graph := h) (h := mapHandler e.refs _) (v := mapValue e.refs _)
          (rest := mapValueArms e.refs _) (op := _) (p := mapValue e.refs _) (k := mapComp e.refs _))
  | operationEmpty =>
      simpa only [mapComp, mapOperationArms, mapEvent, map_forwardedContinuation] using
        (Step.operationEmpty (graph := h) (h := mapHandler e.refs _) (op := _)
          (p := mapValue e.refs _) (k := mapComp e.refs _))
  | operationCons =>
      simpa only [mapComp, mapOperationArms, mapEvent, map_attemptOperation] using
        (Step.operationCons (graph := h) (h := mapHandler e.refs _) (op := _)
          (p := mapValue e.refs _) (k := mapComp e.refs _) (body := mapComp e.refs _)
          (rest := mapOperationArms e.refs _))
  | operationSkip skipped => exact .operationSkip skipped
  | operationWait _ ih => exact .operationWait ih
  | operationYes => exact .operationYes
  | operationNo => exact .operationNo
  | operationView => exact .operationView
  | operationFail => exact .operationFail
  | operationRequest =>
      simpa only [mapComp, mapEvent, mapHandler_rename, mapValue_rename,
        mapComp_rename, mapOperationArms_rename] using
        (Step.operationRequest (graph := h) (h := mapHandler e.refs _) (op := _)
          (p := mapValue e.refs _) (k := mapComp e.refs _) (rest := mapOperationArms e.refs _)
          (nextOp := _) (nextP := mapValue e.refs _) (nextK := mapComp e.refs _))

theorem map_prefix {g : Graph R} {h : Graph T}
    (e : Embedding g xi h tau) (steps : Prefix g m trace n) :
    Prefix h (mapComp e.refs m) (trace.map (mapEvent e.refs)) (mapComp e.refs n) := by
  induction steps with
  | refl => exact .refl _
  | cons step _ ih => exact .cons (map_step e step) ih

end YulangClosure.HandlerGraph.Extension
