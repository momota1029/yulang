import YulangClosure.HandlerGraphEmbedding

namespace YulangClosure.HandlerGraph
open HigherOrder (Ty Context emptyContext extend OperationInstance ViewOccurrence ReceiptTemplate PathCorrespondence)
variable {R : Type}

inductive ObservedTyped (graph : Graph R) (xi : R → Ty) : Value R Empty → Ty → Prop where
  | ref (r) : ObservedTyped graph xi (graph r) (xi r) → ObservedTyped graph xi (.ref r) (xi r)
  | unit : ObservedTyped graph xi .unit (.base .unit)
  | bool : ObservedTyped graph xi (.bool v) (.base .bool)
  | int : ObservedTyped graph xi (.int v) (.base .int)
  | floatBits : ObservedTyped graph xi (.floatBits v) (.base .float)
  | string : ObservedTyped graph xi (.string v) (.base .string)
  | bytes : ObservedTyped graph xi (.bytes v) (.base .bytes)
  | path : ObservedTyped graph xi (.path v) (.base .path)
  | char : ObservedTyped graph xi (.char v) (.base .char)
  | delay : CompTyped xi emptyTy emptyContext body a → ObservedTyped graph xi (.delay body) (.thunk a)
  | inLeft : ValueTyped xi emptyTy emptyContext v a → ObservedTyped graph xi (.inLeft v) (.union a b)
  | inRight : ValueTyped xi emptyTy emptyContext v b → ObservedTyped graph xi (.inRight v) (.union a b)
  | both : ObservedTyped graph xi v a → ObservedTyped graph xi v b →
      ObservedTyped graph xi (.both v) (.intersection a b)
  | top : ObservedTyped graph xi v a → ObservedTyped graph xi (.top v) .top
  | view : ObservedTyped graph xi v a → ObservedTyped graph xi (.view v occurrence) a
  | lambdaValue : CompTyped xi emptyTy (extend emptyContext a) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      ObservedTyped graph xi (.lambda .value receipt a b r body consumer) (.callable a r)
  | lambdaComputation : CompTyped xi emptyTy (extend emptyContext (.thunk a)) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      ObservedTyped graph xi (.lambda .computation receipt a b r body consumer) (.callable a r)
  | wrap : ObservedTyped graph xi f (.callable a b) →
      AdapterTyped xi emptyTy emptyContext input c a → AdapterTyped xi emptyTy emptyContext output b d →
      ObservedTyped graph xi (.wrap f input output) (.callable c d)

variable {graph : Graph R} {xi : R → Ty}

theorem ObservedTyped.typed (h : ObservedTyped graph xi v a) :
    ValueTyped xi emptyTy emptyContext v a := by
  induction h with
  | ref r _ _ => exact .ref r
  | unit => exact .unit
  | bool => exact .bool
  | int => exact .int
  | floatBits => exact .floatBits
  | string => exact .string
  | bytes => exact .bytes
  | path => exact .path
  | char => exact .char
  | delay h => exact .delay h
  | inLeft h => exact .inLeft h
  | inRight h => exact .inRight h
  | both _ _ ih ik => exact .both ih ik
  | top _ ih => exact .top ih
  | view _ ih => exact .view ih
  | lambdaValue h k => exact .lambdaValue h k
  | lambdaComputation h k => exact .lambdaComputation h k
  | wrap _ i o ih => exact .wrap ih i o

/-- Structural descent handles arbitrary finite wrapper syntax between graph
edges. The reference supplier is required only at the actual frontier. -/
theorem observe_from_references (h : ValueTyped xi emptyTy emptyContext v a)
    (refs : ∀ r, nextValue v = some r → ObservedTyped graph xi (.ref r) (xi r)) :
    ObservedTyped graph xi v a := by
  cases h with
  | ref r => exact refs r rfl
  | recvar e => exact Empty.elim e
  | var h => cases h
  | unit => exact .unit
  | bool => exact .bool
  | int => exact .int
  | floatBits => exact .floatBits
  | string => exact .string
  | bytes => exact .bytes
  | path => exact .path
  | char => exact .char
  | delay h => exact .delay h
  | inLeft h => exact .inLeft h
  | inRight h => exact .inRight h
  | both h k => exact .both (observe_from_references h refs) (observe_from_references k refs)
  | top h => exact .top (observe_from_references h refs)
  | view h => exact .view (observe_from_references h refs)
  | lambdaValue h k => exact .lambdaValue h k
  | lambdaComputation h k => exact .lambdaComputation h k
  | wrap h i o => exact .wrap (observe_from_references h refs) i o

/-- Actual reference lookup plus the accepted guard derive finite observation;
no canonical-value or typing oracle for projected terminal units is used. -/
theorem typed_observation (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : ValueTyped xi emptyTy emptyContext v a) : ObservedTyped graph xi v a := by
  have aux : ∀ n (v : Value R Empty) a,
      ValueTyped xi emptyTy emptyContext v a →
      (∀ r, nextValue v = some r → guard.rank r < n) → ObservedTyped graph xi v a := by
    intro n
    induction n with
    | zero =>
        intro v a hv hb
        apply observe_from_references hv
        intro r hr
        exact False.elim (Nat.not_lt_zero _ (hb r hr))
    | succ n ih =>
        intro v a hv hb
        apply observe_from_references hv
        intro r hr
        apply ObservedTyped.ref r
        apply ih (graph r) (xi r) (hg r)
        intro s hs
        exact Nat.lt_of_lt_of_le
          (guard.decrease r s ((projection_edge graph r s).mpr hs))
          (Nat.le_of_lt_succ (hb r hr))
  exact aux guard.ceiling v a h (fun r _ => guard.bound r)

/-- Raw finite reference/view lookup. `here` retains the actual value, and
suppliers below determine its required introduction shape. No typing premise
occurs in this relation. Wrapper entry is not erased by this lookup. -/
inductive Head (graph : Graph R) : Value R Empty → Value R Empty → Prop where
  | here (v) : Head graph v v
  | ref : Head graph (graph r) w → Head graph (.ref r) w
  | view : Head graph v w → Head graph (.view v occurrence) w

theorem thunk_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .thunk a) :
    ∃ body, Head graph v (.delay body) ∧ CompTyped xi emptyTy emptyContext body a := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨body, hh, ht⟩ := ih ht
      exact ⟨body, .ref hh, ht⟩
  | view h ih =>
      intro ht
      obtain ⟨body, hh, ht⟩ := ih ht
      exact ⟨body, .view hh, ht⟩
  | delay h =>
      intro ht
      cases ht
      exact ⟨_, .here _, h⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem thunk_observation (h : ObservedTyped graph xi v (.thunk a)) :
    ∃ body, Head graph v (.delay body) ∧ CompTyped xi emptyTy emptyContext body a :=
  thunk_observation_of_eq h rfl

inductive CallableTerminal (xi : R → Ty) : Value R Empty → Ty → Ty → Prop where
  | lambdaValue : CompTyped xi emptyTy (extend emptyContext a) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      CallableTerminal xi (.lambda .value receipt a b r body consumer) a r
  | lambdaComputation : CompTyped xi emptyTy (extend emptyContext (.thunk a)) body b →
      AdapterTyped xi emptyTy emptyContext consumer b r →
      CallableTerminal xi (.lambda .computation receipt a b r body consumer) a r
  | wrap : ValueTyped xi emptyTy emptyContext f (.callable a b) →
      AdapterTyped xi emptyTy emptyContext input c a → AdapterTyped xi emptyTy emptyContext output b d →
      CallableTerminal xi (.wrap f input output) c d

theorem callable_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .callable a b) :
    ∃ w, Head graph v w ∧ CallableTerminal xi w a b := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨w, hh, ht⟩ := ih ht
      exact ⟨w, .ref hh, ht⟩
  | view h ih =>
      intro ht
      obtain ⟨w, hh, ht⟩ := ih ht
      exact ⟨w, .view hh, ht⟩
  | lambdaValue h k =>
      intro ht
      cases ht
      exact ⟨_, .here _, .lambdaValue h k⟩
  | lambdaComputation h k =>
      intro ht
      cases ht
      exact ⟨_, .here _, .lambdaComputation h k⟩
  | wrap h i o ih =>
      intro ht
      cases ht
      exact ⟨_, .here _, .wrap h.typed i o⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht

theorem callable_observation (h : ObservedTyped graph xi v (.callable a b)) :
    ∃ w, Head graph v w ∧ CallableTerminal xi w a b :=
  callable_observation_of_eq h rfl

theorem union_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .union a b) :
    (∃ w, Head graph v (.inLeft w) ∧ ValueTyped xi emptyTy emptyContext w a) ∨
    (∃ w, Head graph v (.inRight w) ∧ ValueTyped xi emptyTy emptyContext w b) := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      rcases ih ht with ⟨w, hh, ht⟩ | ⟨w, hh, ht⟩
      · exact .inl ⟨w, .ref hh, ht⟩
      · exact .inr ⟨w, .ref hh, ht⟩
  | view h ih =>
      intro ht
      rcases ih ht with ⟨w, hh, ht⟩ | ⟨w, hh, ht⟩
      · exact .inl ⟨w, .view hh, ht⟩
      · exact .inr ⟨w, .view hh, ht⟩
  | inLeft h =>
      intro ht
      cases ht
      exact .inl ⟨_, .here _, h⟩
  | inRight h =>
      intro ht
      cases ht
      exact .inr ⟨_, .here _, h⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem union_observation (h : ObservedTyped graph xi v (.union a b)) :
    (∃ w, Head graph v (.inLeft w) ∧ ValueTyped xi emptyTy emptyContext w a) ∨
    (∃ w, Head graph v (.inRight w) ∧ ValueTyped xi emptyTy emptyContext w b) :=
  union_observation_of_eq h rfl

theorem intersection_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .intersection a b) :
    ∃ w, Head graph v (.both w) ∧ ValueTyped xi emptyTy emptyContext w a ∧
      ValueTyped xi emptyTy emptyContext w b := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨w, hh, ha, hb⟩ := ih ht
      exact ⟨w, .ref hh, ha, hb⟩
  | view h ih =>
      intro ht
      obtain ⟨w, hh, ha, hb⟩ := ih ht
      exact ⟨w, .view hh, ha, hb⟩
  | both h k ih ik =>
      intro ht
      cases ht
      exact ⟨_, .here _, h.typed, k.typed⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem intersection_observation (h : ObservedTyped graph xi v (.intersection a b)) :
    ∃ w, Head graph v (.both w) ∧ ValueTyped xi emptyTy emptyContext w a ∧
      ValueTyped xi emptyTy emptyContext w b :=
  intersection_observation_of_eq h rfl

theorem top_observation_of_eq (h : ObservedTyped graph xi v t) (ht : t = .top) :
    ∃ w a, Head graph v (.top w) ∧ ValueTyped xi emptyTy emptyContext w a := by
  revert ht
  induction h with
  | ref r h ih =>
      intro ht
      obtain ⟨w, a, hh, ht⟩ := ih ht
      exact ⟨w, a, .ref hh, ht⟩
  | view h ih =>
      intro ht
      obtain ⟨w, a, hh, ht⟩ := ih ht
      exact ⟨w, a, .view hh, ht⟩
  | top h ih =>
      intro ht
      cases ht
      exact ⟨_, _, .here _, h.typed⟩
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem top_observation (h : ObservedTyped graph xi v .top) :
    ∃ w a, Head graph v (.top w) ∧ ValueTyped xi emptyTy emptyContext w a :=
  top_observation_of_eq h rfl

theorem ObservedTyped.bottom_empty_of_eq (h : ObservedTyped graph xi v t)
    (ht : t = .bottom) : False := by
  revert ht
  induction h with
  | ref r h ih => intro ht; exact ih ht
  | view h ih => intro ht; exact ih ht
  | unit => intro ht; cases ht
  | bool => intro ht; cases ht
  | int => intro ht; cases ht
  | floatBits => intro ht; cases ht
  | string => intro ht; cases ht
  | bytes => intro ht; cases ht
  | path => intro ht; cases ht
  | char => intro ht; cases ht
  | delay h => intro ht; cases ht
  | inLeft h => intro ht; cases ht
  | inRight h => intro ht; cases ht
  | both h k ih ik => intro ht; cases ht
  | top h ih => intro ht; cases ht
  | lambdaValue h k => intro ht; cases ht
  | lambdaComputation h k => intro ht; cases ht
  | wrap h i o ih => intro ht; cases ht

theorem ObservedTyped.bottom_empty (h : ObservedTyped graph xi v .bottom) : False :=
  h.bottom_empty_of_eq rfl

theorem bottom_empty (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (h : ValueTyped xi emptyTy emptyContext v .bottom) : False :=
  (typed_observation hg guard h).bottom_empty



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

/-- Value R Empty entry forces the carrier, then binds its value into the body. -/
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

def Handler.input : Handler R Empty → Ty
  | .mk _ a _ _ _ => a

def Handler.values : Handler R Empty → ValueArms R Empty
  | .mk _ _ _ vs _ => vs

def Handler.operations : Handler R Empty → OperationArms R Empty
  | .mk _ _ _ _ os => os

theorem handler_input (hh : HandlerTyped xi emptyTy env h a b) : h.input = a := by
  cases hh
  rfl

theorem handler_values (hh : HandlerTyped xi emptyTy env h a b) : ValueArmsTyped xi emptyTy env h.values a b := by
  cases hh with
  | mk hv _ => exact hv

theorem handler_operations (hh : HandlerTyped xi emptyTy env h a b) : OperationArmsTyped xi emptyTy env h.operations a b := by
  cases hh with
  | mk _ ho => exact ho

/-- A concrete callable encoding of K. Its actual response binder is the
lambda parameter, and its result adapter is the identity computation. -/
def continuationValue (q a : Ty) (k : Comp R Empty) : Value R Empty :=
  .lambda .value ⟨[], []⟩ q a a k (.mk a a (.ret (.var 0)) [] [])

theorem continuationValue_typed (hk : CompTyped xi emptyTy (extend env q) k a) :
    ValueTyped xi emptyTy env (continuationValue q a k) (.callable q a) :=
  .lambdaValue hk (.mk (.ret (.var rfl)))

def pairSubstitution (payload continuation : Value R Empty) : Nat → Value R Empty
  | 0 => payload
  | 1 => continuation
  | n+2 => .var n

theorem substitute_pair
    (hb : CompTyped xi emptyTy (extend (extend env kty) pty) body b)
    (hp : ValueTyped xi emptyTy env p pty) (hk : ValueTyped xi emptyTy env k kty) :
    CompTyped xi emptyTy env (substComp (pairSubstitution p k) body) b := by
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

def attemptOperation (h : Handler R Empty) (op : OperationInstance) (p : Value R Empty) (k body : Comp R Empty) : Comp R Empty :=
  substComp (pairSubstitution p (continuationValue op.responseType h.input k)) body

theorem attemptOperation_typed (hh : HandlerTyped xi emptyTy env h a b)
    (hp : ValueTyped xi emptyTy env p op.payloadType) (hk : CompTyped xi emptyTy (extend env op.responseType) k a)
    (hb : CompTyped xi emptyTy (extend (extend env (.callable op.responseType a)) op.payloadType)
      body (.union (.base .unit) b)) :
    CompTyped xi emptyTy env (attemptOperation h op p k body) (.union (.base .unit) b) := by
  unfold attemptOperation
  rw [handler_input hh]
  exact substitute_pair hb hp (continuationValue_typed hk)

/-- H K is separately constructed by reinstating the shifted handler under
K's response binder. It is never passed to a selected operation arm. -/
def forwardedContinuation (h : Handler R Empty) (k : Comp R Empty) : Comp R Empty :=
  .handle (renameHandler Nat.succ h) k

theorem forwardedContinuation_typed (hh : HandlerTyped xi emptyTy env h a b)
    (hk : CompTyped xi emptyTy (extend env q) k a) :
    CompTyped xi emptyTy (extend env q) (forwardedContinuation h k) b :=
  .handle (renameHandler_typed hh (fun _ _ h => h)) hk

inductive Event (R : Type) where
  | silent
  | lookup (reference : R)
  | observeView (occurrence : ViewOccurrence)
  | lambdaEntry (plan : LambdaEntryPlan R)
  | wrapEntry (plan : WrapEntryPlan R)
  | leaveScope (owner : Nat)
  | leaveExpose (effectView resultView : ViewOccurrence)

inductive Step (graph : Graph R) : Comp R Empty → Event R → Comp R Empty → Prop where
  | forceRef : Step graph (.force (.ref r)) (.lookup r) (.force (graph r))
  | unionRef : Step graph (.unionCase (.ref r) l right) (.lookup r) (.unionCase (graph r) l right)
  | chooseLeftRef : Step graph (.chooseLeft (.ref r)) (.lookup r) (.chooseLeft (graph r))
  | chooseRightRef : Step graph (.chooseRight (.ref r)) (.lookup r) (.chooseRight (graph r))
  | absurdRef : Step graph (.absurd (.ref r)) (.lookup r) (.absurd (graph r))
  | callRef : Step graph (.dynamicCall (.ref r) arg) (.lookup r) (.dynamicCall (graph r) arg)
  | absurdView : Step graph (.absurd (.view v o)) (.observeView o) (.absurd v)
  | valueRef : Step graph (.waitValue h v rest (.ret (.ref r))) (.lookup r)
      (.waitValue h v rest (.ret (graph r)))
  | operationRef : Step graph (.waitOperation h op p k rest (.ret (.ref r))) (.lookup r)
      (.waitOperation h op p k rest (.ret (graph r)))
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

  | bindRequest : Step graph (.bind (.request op p k) body) .silent
      (.request op p (.bind k (renameComp (Original.up Nat.succ) body)))
  | bindFail : Step graph (.bind (.fail reason) body) .silent (.fail reason)
  | scopeRequest : Step graph (.scope owner (.request op p k)) .silent
      (.request op p (.scope owner k))
  | scopeFail : Step graph (.scope owner (.fail reason)) .silent (.fail reason)
  | exposeRequest : Step graph (.expose ev rv (.request op p k)) .silent
      (.request op p (.expose ev rv k))
  | exposeFail : Step graph (.expose ev rv (.fail reason)) .silent (.fail reason)
  | handle : Step graph m e n → Step graph (.handle h m) e (.handle h n)
  | handleReturn : Step graph (.handle h (.ret v)) .silent (.tryValue h v h.values)
  | handleRequest : Step graph (.handle h (.request op p k)) .silent
      (.tryOperation h op p k h.operations)
  | handleFail : Step graph (.handle h (.fail reason)) .silent (.fail reason)
  | valueEmpty : Step graph (.tryValue h v .nil) .silent (.fail .matchFailure)
  | valueCons : Step graph (.tryValue h v (.cons body rest)) .silent
      (.waitValue h v rest (substComp (single v) body))
  | valueWait : Step graph m e n → Step graph (.waitValue h v rest m) e (.waitValue h v rest n)
  | valueYes : Step graph (.waitValue h v rest (.ret (.inRight result))) .silent (.ret result)
  | valueNo : Step graph (.waitValue h v rest (.ret (.inLeft unit))) .silent (.tryValue h v rest)
  | valueView : Step graph (.waitValue h v rest (.ret (.view result o))) (.observeView o)
      (.waitValue h v rest (.ret result))
  | valueFail : Step graph (.waitValue h v rest (.fail reason)) .silent (.fail reason)
  | valueRequest : Step graph (.waitValue h v rest (.request op p k)) .silent
      (.request op p (.waitValue (renameHandler Nat.succ h) (renameValue Nat.succ v)
        (renameValueArms Nat.succ rest) k))
  | operationEmpty : Step graph (.tryOperation h op p k .nil) .silent
      (.request op p (forwardedContinuation h k))
  | operationCons : Step graph (.tryOperation h op p k (.cons op true body rest)) .silent
      (.waitOperation h op p k rest (attemptOperation h op p k body))
  | operationSkip : (armOp ≠ op ∨ eligible = false) →
      Step graph (.tryOperation h op p k (.cons armOp eligible body rest)) .silent
        (.tryOperation h op p k rest)
  | operationWait : Step graph m e n →
      Step graph (.waitOperation h op p k rest m) e (.waitOperation h op p k rest n)
  | operationYes : Step graph (.waitOperation h op p k rest (.ret (.inRight result))) .silent (.ret result)
  | operationNo : Step graph (.waitOperation h op p k rest (.ret (.inLeft unit))) .silent
      (.tryOperation h op p k rest)
  | operationView : Step graph (.waitOperation h op p k rest (.ret (.view result o))) (.observeView o)
      (.waitOperation h op p k rest (.ret result))
  | operationFail : Step graph (.waitOperation h op p k rest (.fail reason)) .silent (.fail reason)
  | operationRequest : Step graph (.waitOperation h op p k rest (.request nextOp nextP nextK)) .silent
      (.request nextOp nextP (.waitOperation (renameHandler Nat.succ h) op
        (renameValue Nat.succ p) (renameComp (Original.up Nat.succ) k)
        (renameOperationArms Nat.succ rest) nextK))

theorem reference_type (h : ValueTyped xi emptyTy env (.ref r) a) : xi r = a := by
  cases h
  rfl

theorem preservation (hg : WellTyped graph xi) (step : Step graph m e n) (h : CompTyped xi emptyTy emptyContext m a) : CompTyped xi emptyTy emptyContext n a := by
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
  | valueRef =>
      cases h with
      | waitValue hh hv hr hm => cases hm with
        | ret hv' => exact .waitValue hh hv hr (.ret ((reference_type hv') ▸ hg _))
  | operationRef =>
      cases h with
      | waitOperation hh hp hk hr hm => cases hm with
        | ret hv => exact .waitOperation hh hp hk hr (.ret ((reference_type hv) ▸ hg _))
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
        | request hp hk => exact .request hp (.bind hk (renameComp_typed hb (up_typed (env := emptyContext) (target := extend emptyContext _) (r := Nat.succ) (fun _ _ h => h) _)))
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
            (renameComp_typed hk (up_typed (env := emptyContext) (target := extend emptyContext _) (r := Nat.succ) (fun _ _ h => h) _))
            (renameOperationArms_typed hr (fun _ _ h => h)) hk')

/-- The terminal alternatives are only the three concrete outer constructors;
requests and failures underneath a frame must take their propagation step. -/
inductive Terminal : Comp R Empty → Prop where
  | returned (v : Value R Empty) : Terminal (.ret v)
  | requested (op p k) : Terminal (.request op p k)
  | failed (reason) : Terminal (.fail reason)

def CanProgress (graph : Graph R) (m : Comp R Empty) : Prop := Terminal m ∨ ∃ e n, Step graph m e n

theorem operation_trials_progress (h : Handler R Empty) (op : OperationInstance)
    (p : Value R Empty) (k : Comp R Empty) (arms : OperationArms R Empty) : CanProgress graph (.tryOperation h op p k arms) := by
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

theorem closed_progress (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph)) (h : CompTyped xi emptyTy emptyContext m a) : CanProgress graph m := by
  cases h with
  | ret _ => exact .inl (.returned _)
  | request _ _ => exact .inl (.requested _ _ _)
  | fail => exact .inl (.failed _)
  | force hv =>
      obtain ⟨body, hh, _⟩ := thunk_observation (typed_observation hg guard hv)
      cases hh with
      | here => exact .inr ⟨_, _, .force⟩
      | ref _ => exact .inr ⟨_, _, .forceRef⟩
      | view _ => exact .inr ⟨_, _, .forceView⟩
  | bind hm hb =>
      rcases closed_progress hg guard hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .bindReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .bindRequest⟩
        | failed _ => exact .inr ⟨_, _, .bindFail⟩
      · exact .inr ⟨e, _, .bind step⟩
  | unionCase hv hl hr =>
      rcases union_observation (typed_observation hg guard hv) with ⟨w, hh, _⟩ | ⟨w, hh, _⟩
      · cases hh with
        | here => exact .inr ⟨_, _, .unionLeft⟩
        | ref _ => exact .inr ⟨_, _, .unionRef⟩
        | view _ => exact .inr ⟨_, _, .unionView⟩
      · cases hh with
        | here => exact .inr ⟨_, _, .unionRight⟩
        | ref _ => exact .inr ⟨_, _, .unionRef⟩
        | view _ => exact .inr ⟨_, _, .unionView⟩
  | chooseLeft hv =>
      obtain ⟨w, hh, _, _⟩ := intersection_observation (typed_observation hg guard hv)
      cases hh with
      | here => exact .inr ⟨_, _, .chooseLeft⟩
      | ref _ => exact .inr ⟨_, _, .chooseLeftRef⟩
      | view _ => exact .inr ⟨_, _, .chooseLeftView⟩
  | chooseRight hv =>
      obtain ⟨w, hh, _, _⟩ := intersection_observation (typed_observation hg guard hv)
      cases hh with
      | here => exact .inr ⟨_, _, .chooseRight⟩
      | ref _ => exact .inr ⟨_, _, .chooseRightRef⟩
      | view _ => exact .inr ⟨_, _, .chooseRightView⟩
  | absurd hv => exact False.elim (bottom_empty hg guard hv)
  | scope hm =>
      rcases closed_progress hg guard hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .scopeReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .scopeRequest⟩
        | failed _ => exact .inr ⟨_, _, .scopeFail⟩
      · exact .inr ⟨e, _, .scope step⟩
  | expose hm =>
      rcases closed_progress hg guard hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned _ => exact .inr ⟨_, _, .exposeReturn⟩
        | requested _ _ _ => exact .inr ⟨_, _, .exposeRequest⟩
        | failed _ => exact .inr ⟨_, _, .exposeFail⟩
      · exact .inr ⟨e, _, .expose step⟩
  | dynamicCall hf ha =>
      obtain ⟨w, hh, ht⟩ := callable_observation (typed_observation hg guard hf)
      cases hh with
      | ref _ => exact .inr ⟨_, _, .callRef⟩
      | view _ => exact .inr ⟨_, _, .callView⟩
      | here =>
          cases ht with
          | lambdaValue _ _ => exact .inr ⟨_, _, .callLambda⟩
          | lambdaComputation _ _ => exact .inr ⟨_, _, .callLambda⟩
          | wrap _ _ _ => exact .inr ⟨_, _, .callWrap⟩

  | handle hh hm =>
      rcases closed_progress hg guard hm with terminal | ⟨e, n, step⟩
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
      rcases closed_progress hg guard hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned v =>
            cases hm with
            | ret hv =>
                rcases union_observation (typed_observation hg guard hv) with ⟨w, hh, _⟩ | ⟨w, hh, _⟩
                · cases hh with
                  | here => exact .inr ⟨_, _, .valueNo⟩
                  | ref _ => exact .inr ⟨_, _, .valueRef⟩
                  | view _ => exact .inr ⟨_, _, .valueView⟩
                · cases hh with
                  | here => exact .inr ⟨_, _, .valueYes⟩
                  | ref _ => exact .inr ⟨_, _, .valueRef⟩
                  | view _ => exact .inr ⟨_, _, .valueView⟩
        | requested _ _ _ => exact .inr ⟨_, _, .valueRequest⟩
        | failed _ => exact .inr ⟨_, _, .valueFail⟩
      · exact .inr ⟨e, _, .valueWait step⟩
  | tryOperation hh hp hk hs => exact operation_trials_progress _ _ _ _ _
  | waitOperation hh hp hk hs hm =>
      rcases closed_progress hg guard hm with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned v =>
            cases hm with
            | ret hv =>
                rcases union_observation (typed_observation hg guard hv) with ⟨w, hh, _⟩ | ⟨w, hh, _⟩
                · cases hh with
                  | here => exact .inr ⟨_, _, .operationNo⟩
                  | ref _ => exact .inr ⟨_, _, .operationRef⟩
                  | view _ => exact .inr ⟨_, _, .operationView⟩
                · cases hh with
                  | here => exact .inr ⟨_, _, .operationYes⟩
                  | ref _ => exact .inr ⟨_, _, .operationRef⟩
                  | view _ => exact .inr ⟨_, _, .operationView⟩
        | requested _ _ _ => exact .inr ⟨_, _, .operationRequest⟩
        | failed _ => exact .inr ⟨_, _, .operationFail⟩
      · exact .inr ⟨e, _, .operationWait step⟩

inductive Prefix (graph : Graph R) : Comp R Empty → List (Event R) → Comp R Empty → Prop where
  | refl (m : Comp R Empty) : Prefix graph m [] m
  | cons : Step graph m e n → Prefix graph n events last → Prefix graph m (e :: events) last

theorem prefix_preservation (hg : WellTyped graph xi) (trace : Prefix graph m events n) (h : CompTyped xi emptyTy emptyContext m a) :
    CompTyped xi emptyTy emptyContext n a := by
  induction trace generalizing a with
  | refl => exact h
  | cons step _ ih => exact ih (preservation hg step h)

/-- All raw finite internal prefixes, including arbitrary actual attempt code. -/
theorem finite_prefix_safety (hg : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph)) (h : CompTyped xi emptyTy emptyContext m a) (trace : Prefix graph m events n) :
    CompTyped xi emptyTy emptyContext n a ∧ CanProgress graph n := by
  have hn := prefix_preservation hg trace h
  exact ⟨hn, closed_progress hg guard hn⟩


end YulangClosure.HandlerGraph
