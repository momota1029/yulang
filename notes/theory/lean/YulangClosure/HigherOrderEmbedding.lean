import YulangClosure.HigherOrderSyntax
import YulangClosure.CallEnvironmentRealization

namespace YulangClosure.HigherOrder

def embedTy : Original.Ty → Ty
  | .base b => .base b
  | .thunk a => .thunk (embedTy a)
  | .union a b => .union (embedTy a) (embedTy b)
  | .intersection a b => .intersection (embedTy a) (embedTy b)
  | .top => .top
  | .bottom => .bottom

def embedPort : TypedCall.PortKind → PortKind
  | .carrier => .carrier
  | .callEffect => .callEffect
  | .result => .result

def embedPath (p : TypedCall.PortPath) : PortPath :=
  ⟨p.components, embedPort p.port, embedTy p.type⟩

def embedOccurrence (v : TypedCall.ViewOccurrence) : ViewOccurrence :=
  ⟨v.identity, embedPath v.path⟩

/-- Prop-to-Prop translation: no erased mapping identity is reified as data. -/
theorem embedPathRule {p q : TypedCall.PortPath} (h : TypedCall.PathRule p q) :
    PathRule (embedPath p) (embedPath q) := by
  induction h with
  | identity p => exact .identity _
  | «prefix» label p q h ih => exact .prefix label _ _ ih
  | adapterMap identity p q => exact .adapterMap identity _ _

def embedCorrespondence (p : TypedCall.PathCorrespondence) : PathCorrespondence :=
  ⟨embedPath p.source, embedPath p.target, embedPathRule p.rule⟩

def embedOperation (op : TypedCall.OperationInstance) : OperationInstance :=
  ⟨op.operation, op.typeArguments.map embedTy, embedTy op.payloadType, embedTy op.responseType⟩

def embedSlot (s : TypedCall.ReceiptSlot) : ReceiptSlot := ⟨s.slot, embedPath s.path⟩
def embedReceipt (r : TypedCall.ReceiptTemplate) : ReceiptTemplate :=
  ⟨r.profile.map embedPath, r.designatedSlots.map embedSlot⟩

def embedPorts (p : TypedCall.InterfacePorts) : InterfacePorts :=
  ⟨p.interface, embedPath p.callEffect, embedPath p.result,
    embedOccurrence p.callEffectView, embedOccurrence p.resultView⟩

mutual
  def embedOriginalValue : Original.Val → Value
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay c => .delay (embedOriginalComp c)
    | .inLeft v => .inLeft (embedOriginalValue v)
    | .inRight v => .inRight (embedOriginalValue v)
    | .both v => .both (embedOriginalValue v)
    | .top v => .top (embedOriginalValue v)
  def embedOriginalComp : Original.Comp → Comp
    | .ret v => .ret (embedOriginalValue v)
    | .force v => .force (embedOriginalValue v)
    | .bind m n => .bind (embedOriginalComp m) (embedOriginalComp n)
    | .unionCase v l r => .unionCase (embedOriginalValue v)
        (embedOriginalComp l) (embedOriginalComp r)
    | .chooseLeft v => .chooseLeft (embedOriginalValue v)
    | .chooseRight v => .chooseRight (embedOriginalValue v)
    | .absurd v => .absurd (embedOriginalValue v)
end

mutual
  def embedValue : TypedCall.Value → Value
    | .var i => .var i
    | .original v => embedOriginalValue v
    | .delay c => .delay (embedComp c)
    | .view v o => .view (embedValue v) (embedOccurrence o)
  def embedComp : TypedCall.Comp → Comp
    | .original c => embedOriginalComp c
    | .ret v => .ret (embedValue v)
    | .bind m n => .bind (embedComp m) (embedComp n)
    | .force v => .force (embedValue v)
    | .scope owner c => .scope owner (embedComp c)
    | .expose e r c => .expose (embedOccurrence e) (embedOccurrence r) (embedComp c)
    | .request op v k => .request (embedOperation op) (embedValue v) (embedComp k)
    | .fail reason => .fail reason
end

def embedAdapter (a : TypedCall.Adapter) : Adapter :=
  .mk (embedTy a.input) (embedTy a.output) (embedComp a.body)
    (a.pathCorrespondences.map embedCorrespondence) (a.capturedViews.map embedOccurrence)

def embedFunction : TypedCall.Function → Value
  | .lambda mode receipt a b r body consumer =>
      .lambda mode (embedReceipt receipt) (embedTy a) (embedTy b) (embedTy r)
        (embedComp body) (embedAdapter consumer)
  | .wrap f a r => .wrap (embedFunction f) (embedAdapter a) (embedAdapter r)

/-- Universal in the target context; closed old syntax needs no weakening axiom. -/
def ContextEmbedding (old : Original.Context) (new : Context) : Prop :=
  ∀ i a, old i = some a → new i = some (embedTy a)

theorem empty_embedding (env : Context) : ContextEmbedding Original.emptyContext env := by
  intro i a h
  cases h

theorem extend_embedding {old : Original.Context} {new : Context}
    (h : ContextEmbedding old new) (a : Original.Ty) :
    ContextEmbedding (Original.extend old a) (extend new (embedTy a)) := by
  intro i b hi
  cases i with
  | zero =>
      simp only [Original.extend, Option.some.injEq] at hi
      subst b
      rfl
  | succ i => exact h i b hi

mutual
  theorem embedOriginalValue_typed {old : Original.Context} {v : Original.Val} {a : Original.Ty}
      (h : Original.ValTyped old v a) {new : Context} (he : ContextEmbedding old new) :
      ValueTyped new (embedOriginalValue v) (embedTy a) := by
    cases h with
    | var h => exact .var (he _ _ h)
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (embedOriginalComp_typed h he)
    | inLeft h => exact .inLeft (embedOriginalValue_typed h he)
    | inRight h => exact .inRight (embedOriginalValue_typed h he)
    | both h k => exact .both (embedOriginalValue_typed h he) (embedOriginalValue_typed k he)
    | top h => exact .top (embedOriginalValue_typed h he)
  theorem embedOriginalComp_typed {old : Original.Context} {c : Original.Comp} {a : Original.Ty}
      (h : Original.CompTyped old c a) {new : Context} (he : ContextEmbedding old new) :
      CompTyped new (embedOriginalComp c) (embedTy a) := by
    cases h with
    | ret h => exact .ret (embedOriginalValue_typed h he)
    | force h => exact .force (embedOriginalValue_typed h he)
    | bind h k =>
        exact .bind (embedOriginalComp_typed h he)
          (embedOriginalComp_typed k (extend_embedding he _))
    | unionCase h l r =>
        exact .unionCase (embedOriginalValue_typed h he)
          (embedOriginalComp_typed l (extend_embedding he _))
          (embedOriginalComp_typed r (extend_embedding he _))
    | chooseLeft h => exact .chooseLeft (embedOriginalValue_typed h he)
    | chooseRight h => exact .chooseRight (embedOriginalValue_typed h he)
    | absurd h => exact .absurd (embedOriginalValue_typed h he)
end

mutual
  theorem embedValue_typed {old : Original.Context} {v : TypedCall.Value} {a : Original.Ty}
      (h : TypedCall.ValueTyped old v a) {new : Context} (he : ContextEmbedding old new) :
      ValueTyped new (embedValue v) (embedTy a) := by
    cases h with
    | var h => exact .var (he _ _ h)
    | original h => exact embedOriginalValue_typed h (empty_embedding _)
    | delay h => exact .delay (embedComp_typed h he)
    | view h => exact .view (embedValue_typed h he)
  theorem embedComp_typed {old : Original.Context} {c : TypedCall.Comp} {a : Original.Ty}
      (h : TypedCall.CompTyped old c a) {new : Context} (he : ContextEmbedding old new) :
      CompTyped new (embedComp c) (embedTy a) := by
    cases h with
    | original h => exact embedOriginalComp_typed h (empty_embedding _)
    | ret h => exact .ret (embedValue_typed h he)
    | bind h k => exact .bind (embedComp_typed h he) (embedComp_typed k (extend_embedding he _))
    | force h => exact .force (embedValue_typed h he)
    | scope h => exact .scope (embedComp_typed h he)
    | expose e r h => exact .expose (embedComp_typed h he)
    | request h k =>
        exact .request (embedValue_typed h he)
          (embedComp_typed k (extend_embedding he _))
    | fail => exact .fail
end

theorem embedAdapter_typed (a : TypedCall.Adapter) (env : Context) :
    AdapterTyped env (embedAdapter a) (embedTy a.input) (embedTy a.output) :=
  .mk (embedComp_typed a.typed (extend_embedding (empty_embedding env) a.input))

theorem embedFunction_typed {f : TypedCall.Function} {a b : Original.Ty}
    (h : TypedCall.FunctionTyped f a b) (env : Context) :
    ValueTyped env (embedFunction f) (.callable (embedTy a) (embedTy b)) := by
  induction h with
  | lambdaValue receipt a bodyResult result body consumer hb hc hr =>
      exact .lambdaValue (embedComp_typed hb (extend_embedding (empty_embedding env) a))
        (by simpa only [hc, hr] using embedAdapter_typed consumer env)
  | lambdaComputation receipt a bodyResult result body consumer hb hc hr =>
      exact .lambdaComputation
        (embedComp_typed hb (extend_embedding (empty_embedding env) (.thunk a)))
        (by simpa only [hc, hr] using embedAdapter_typed consumer env)
  | @wrap f argumentAdapter resultAdapter a b c d hf ha hao hr hro ih =>
      exact .wrap ih
        (by simpa only [ha, hao] using embedAdapter_typed argumentAdapter env)
        (by simpa only [hr, hro] using embedAdapter_typed resultAdapter env)

/-- Callable values inhabit response binders; no Function-only response sort. -/
theorem callable_response (env : Context) (a b : Ty) :
    CompTyped (extend env (.callable a b)) (.ret (.var 0)) (.callable a b) :=
  .ret (.var rfl)

/-- A request can bind and return an actual callable-typed response. -/
theorem request_callable_response (env : Context) (operation : Nat)
    (typeArguments : List Ty) (payloadType a b : Ty) (payload : Value)
    (hp : ValueTyped env payload payloadType) :
    CompTyped env
      (.request ⟨operation, typeArguments, payloadType, .callable a b⟩ payload (.ret (.var 0)))
      (.callable a b) :=
  .request hp (callable_response env a b)

/-- Old functions are now usable as higher-order arguments (delayed carrier). -/
theorem function_as_argument {f : TypedCall.Function} {a b : Original.Ty}
    (h : TypedCall.FunctionTyped f a b) (env : Context) :
    ValueTyped env (.delay (.ret (embedFunction f))) (.thunk (.callable (embedTy a) (embedTy b))) :=
  .delay (.ret (embedFunction_typed h env))

theorem call_with_function_argument {f : TypedCall.Function} {a b : Original.Ty}
    (h : TypedCall.FunctionTyped f a b) {env : Context} {g : Value} {result : Ty}
    (hg : ValueTyped env g (.callable (.callable (embedTy a) (embedTy b)) result)) :
    CompTyped env (.dynamicCall g (.delay (.ret (embedFunction f)))) result :=
  .dynamicCall hg (function_as_argument h env)

/-- Generic native cells can hold the new typed callable value. This is a formal
store construction, not readback of a Rust Closure or a source layout theorem. -/
theorem function_cell {f : TypedCall.Function} {a b : Original.Ty}
    (h : TypedCall.FunctionTyped f a b) (store : NativeClosureEnvironment.Store Value) :
    (store.push (embedFunction f)).cell store.size = some (embedFunction f) ∧
      ValueTyped emptyContext (embedFunction f) (.callable (embedTy a) (embedTy b)) :=
  ⟨NativeClosureEnvironment.push_current _ _, embedFunction_typed h _⟩

def embedStore (store : Nat → Option TypedCall.Value) : Nat → Option Value :=
  fun cell => (store cell).map embedValue

/-- Read the same address in the pointwise-translated current store. -/
def readEmbedded [DecidableEq K] (arena : NativeClosureEnvironment.Arena K D)
    (env : Nat) (store : Nat → Option Value) (ref : CallEnvironmentRealization.Reference K) :
    Option Value := (CallEnvironmentRealization.address arena env ref).bind store

theorem read_embedding [DecidableEq K] (arena : NativeClosureEnvironment.Arena K D)
    (env : Nat) (store : Nat → Option TypedCall.Value)
    (ref : CallEnvironmentRealization.Reference K) :
    readEmbedded arena env (embedStore store) ref =
      (CallEnvironmentRealization.read arena env store ref).map embedValue := by
  cases h : CallEnvironmentRealization.address arena env ref <;>
    simp [readEmbedded, CallEnvironmentRealization.read, embedStore, h]

theorem read_embedding_typed [DecidableEq K]
    {arena : NativeClosureEnvironment.Arena K D} {env : Nat}
    {store : Nat → Option TypedCall.Value} {layout : CallEnvironmentRealization.Layout K}
    (cells : CallEnvironmentRealization.CellsTyped arena env store layout)
    {ref : CallEnvironmentRealization.Reference K} {a : Original.Ty}
    (hm : (ref, a) ∈ layout) {v : TypedCall.Value}
    (hr : CallEnvironmentRealization.read arena env store ref = some v) :
    readEmbedded arena env (embedStore store) ref = some (embedValue v) ∧
      ValueTyped emptyContext (embedValue v) (embedTy a) := by
  constructor
  · rw [read_embedding, hr]
    rfl
  · exact embedValue_typed (CallEnvironmentRealization.successful_read_typed cells hm hr)
      (empty_embedding _)

/-- Successful represented CURRENT reads supply actual embedded cell values. -/
theorem captured_value_typed [DecidableEq K]
    {arena : NativeClosureEnvironment.Arena K D} {env : Nat}
    {store : Nat → Option TypedCall.Value} {layout : CallEnvironmentRealization.Layout K}
    {values : List TypedCall.Value}
    (success : CallEnvironmentRealization.realize arena env store layout = some values)
    (cells : CallEnvironmentRealization.CellsTyped arena env store layout)
    (filler : TypedCall.Value) (i : Nat) (a : Original.Ty)
    (hi : CallEnvironmentRealization.context layout i = some a) :
    ValueTyped emptyContext
      (embedValue (CallEnvironmentRealization.substitution filler values i)) (embedTy a) :=
  embedValue_typed (CallEnvironmentRealization.realized_substitution_typed
    success cells filler i a hi) (empty_embedding _)

/-- Apply the actual capture supplier to the parent body before embedding. -/
theorem captured_body_typed [DecidableEq K]
    {arena : NativeClosureEnvironment.Arena K D} {env : Nat}
    {store : Nat → Option TypedCall.Value} {layout : CallEnvironmentRealization.Layout K}
    {values : List TypedCall.Value}
    (success : CallEnvironmentRealization.realize arena env store layout = some values)
    (cells : CallEnvironmentRealization.CellsTyped arena env store layout)
    (filler : TypedCall.Value) {body : TypedCall.Comp} {a : Original.Ty}
    (hb : TypedCall.CompTyped (CallEnvironmentRealization.context layout) body a) :
    CompTyped emptyContext (embedComp (TypedCall.substituteCallComp
      (CallEnvironmentRealization.substitution filler values) body)) (embedTy a) :=
  embedComp_typed (CallEnvironmentRealization.close_body success cells filler hb) (empty_embedding _)

end YulangClosure.HigherOrder
