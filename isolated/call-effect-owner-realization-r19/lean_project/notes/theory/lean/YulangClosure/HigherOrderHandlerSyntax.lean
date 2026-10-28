import YulangClosure.HigherOrderSubstitution

namespace YulangClosure.HigherOrder.Handler
open YulangClosure.HigherOrder (Ty Context emptyContext extend OperationInstance
  ViewOccurrence ReceiptTemplate PathCorrespondence)

/-! Candidate recursively extended syntax. Every attempt is actual Comp code.
An operation arm binds payload at zero and the original shallow continuation at
one. Eligibility is raw data; its permission interpretation is deliberately open.
No definition below supplies typing as syntax or as an operational premise. -/

mutual
  inductive Value where
    | var (index : Nat)
    | unit
    | bool (value : Bool)
    | int (value : Int)
    | floatBits (value : UInt64)
    | string (value : String)
    | bytes (value : List UInt8)
    | path (value : List UInt8)
    | char (value : String)
    | delay (body : Comp)
    | inLeft (value : Value)
    | inRight (value : Value)
    | both (value : Value)
    | top (value : Value)
    | view (value : Value) (occurrence : ViewOccurrence)
    | lambda (mode : Original.Mode) (receipt : ReceiptTemplate)
        (argument bodyResult result : Ty) (body : Comp) (consumer : Adapter)
    | wrap (inner : Value) (input output : Adapter)
  inductive Comp where
    | ret (value : Value)
    | force (value : Value)
    | bind (first body : Comp)
    | unionCase (value : Value) (left right : Comp)
    | chooseLeft (value : Value)
    | chooseRight (value : Value)
    | absurd (value : Value)
    | scope (owner : Nat) (body : Comp)
    | expose (effectView resultView : ViewOccurrence) (body : Comp)
    | request (op : OperationInstance) (payload : Value) (continuation : Comp)
    | fail (reason : Original.Failure)
    | dynamicCall (function argument : Value)
    | handle (handler : Handler) (body : Comp)
    | tryValue (handler : Handler) (value : Value) (arms : ValueArms)
    | waitValue (handler : Handler) (value : Value) (remaining : ValueArms) (attempt : Comp)
    | tryOperation (handler : Handler) (op : OperationInstance) (payload : Value) (continuation : Comp) (arms : OperationArms)
    | waitOperation (handler : Handler) (op : OperationInstance) (payload : Value) (continuation : Comp) (remaining : OperationArms) (attempt : Comp)
  inductive Handler where
    | mk (identity : Nat) (input output : Ty) (values : ValueArms) (operations : OperationArms)
  inductive ValueArms where
    | nil
    | cons (body : Comp) (rest : ValueArms)
  inductive OperationArms where
    | nil
    | cons (op : OperationInstance) (eligible : Bool) (body : Comp) (rest : OperationArms)
  inductive Adapter where
    | mk (input output : Ty) (body : Comp)
        (paths : List PathCorrespondence) (views : List ViewOccurrence)
end


mutual
  inductive ValueTyped : Context → Value → Ty → Prop
    | var : env i = some a → ValueTyped env (.var i) a
    | unit : ValueTyped env .unit (.base .unit)
    | bool : ValueTyped env (.bool v) (.base .bool)
    | int : ValueTyped env (.int v) (.base .int)
    | floatBits : ValueTyped env (.floatBits v) (.base .float)
    | string : ValueTyped env (.string v) (.base .string)
    | bytes : ValueTyped env (.bytes v) (.base .bytes)
    | path : ValueTyped env (.path v) (.base .path)
    | char : ValueTyped env (.char v) (.base .char)
    | delay : CompTyped env m a → ValueTyped env (.delay m) (.thunk a)
    | inLeft : ValueTyped env v a → ValueTyped env (.inLeft v) (.union a b)
    | inRight : ValueTyped env v b → ValueTyped env (.inRight v) (.union a b)
    | both : ValueTyped env v a → ValueTyped env v b →
        ValueTyped env (.both v) (.intersection a b)
    | top : ValueTyped env v a → ValueTyped env (.top v) .top
    | view : ValueTyped env v a → ValueTyped env (.view v occurrence) a
    | lambdaValue : CompTyped (extend env a) body b → AdapterTyped env consumer b r →
        ValueTyped env (.lambda .value receipt a b r body consumer) (.callable a r)
    | lambdaComputation : CompTyped (extend env (.thunk a)) body b → AdapterTyped env consumer b r →
        ValueTyped env (.lambda .computation receipt a b r body consumer) (.callable a r)
    | wrap : ValueTyped env f (.callable a b) → AdapterTyped env input c a →
        AdapterTyped env output b d → ValueTyped env (.wrap f input output) (.callable c d)
  inductive CompTyped : Context → Comp → Ty → Prop
    | ret : ValueTyped env v a → CompTyped env (.ret v) a
    | force : ValueTyped env v (.thunk a) → CompTyped env (.force v) a
    | bind : CompTyped env m a → CompTyped (extend env a) n b →
        CompTyped env (.bind m n) b
    | unionCase : ValueTyped env v (.union a b) →
        CompTyped (extend env a) l c → CompTyped (extend env b) r c →
        CompTyped env (.unionCase v l r) c
    | chooseLeft : ValueTyped env v (.intersection a b) → CompTyped env (.chooseLeft v) a
    | chooseRight : ValueTyped env v (.intersection a b) → CompTyped env (.chooseRight v) b
    | absurd : ValueTyped env v .bottom → CompTyped env (.absurd v) a
    | scope : CompTyped env body a → CompTyped env (.scope owner body) a
    | expose : CompTyped env body a → CompTyped env (.expose ev rv body) a
    | request : ValueTyped env payload op.payloadType →
        CompTyped (extend env op.responseType) continuation a →
        CompTyped env (.request op payload continuation) a
    | fail : CompTyped env (.fail reason) a
    | dynamicCall : ValueTyped env f (.callable a b) → ValueTyped env arg (.thunk a) →
        CompTyped env (.dynamicCall f arg) b
    | handle : HandlerTyped env h a b → CompTyped env m a → CompTyped env (.handle h m) b
    | tryValue : HandlerTyped env h a b → ValueTyped env v a → ValueArmsTyped env arms a b →
        CompTyped env (.tryValue h v arms) b
    | waitValue : HandlerTyped env h a b → ValueTyped env v a → ValueArmsTyped env arms a b →
        CompTyped env attempt (.union (.base .unit) b) → CompTyped env (.waitValue h v arms attempt) b
    | tryOperation : HandlerTyped env h a b → ValueTyped env p op.payloadType →
        CompTyped (extend env op.responseType) k a → OperationArmsTyped env arms a b →
        CompTyped env (.tryOperation h op p k arms) b
    | waitOperation : HandlerTyped env h a b → ValueTyped env p op.payloadType →
        CompTyped (extend env op.responseType) k a → OperationArmsTyped env arms a b →
        CompTyped env attempt (.union (.base .unit) b) → CompTyped env (.waitOperation h op p k arms attempt) b
  inductive HandlerTyped : Context → Handler → Ty → Ty → Prop where
    | mk : ValueArmsTyped env vs a b → OperationArmsTyped env os a b →
        HandlerTyped env (.mk identity a b vs os) a b
  inductive ValueArmsTyped : Context → ValueArms → Ty → Ty → Prop where
    | nil : ValueArmsTyped env .nil a b
    | cons : CompTyped (extend env a) body (.union (.base .unit) b) →
        ValueArmsTyped env rest a b → ValueArmsTyped env (.cons body rest) a b
  inductive OperationArmsTyped : Context → OperationArms → Ty → Ty → Prop where
    | nil : OperationArmsTyped env .nil a b
    | cons : CompTyped (extend (extend env (.callable op.responseType a)) op.payloadType)
          body (.union (.base .unit) b) → OperationArmsTyped env rest a b →
        OperationArmsTyped env (.cons op eligible body rest) a b
  inductive AdapterTyped : Context → Adapter → Ty → Ty → Prop where
    | mk : CompTyped (extend env a) body b →
        AdapterTyped env (.mk a b body paths views) a b
end




mutual
  def renameValue (r : Nat → Nat) : Value → Value
    | .var i => .var (r i)
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (renameComp r m)
    | .inLeft v => .inLeft (renameValue r v)
    | .inRight v => .inRight (renameValue r v)
    | .both v => .both (renameValue r v)
    | .top v => .top (renameValue r v)
    | .view v o => .view (renameValue r v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (renameComp (Original.up r) body) (renameAdapter r consumer)
    | .wrap f input output => .wrap (renameValue r f) (renameAdapter r input) (renameAdapter r output)
  def renameComp (r : Nat → Nat) : Comp → Comp
    | .ret v => .ret (renameValue r v)
    | .force v => .force (renameValue r v)
    | .chooseLeft v => .chooseLeft (renameValue r v)
    | .chooseRight v => .chooseRight (renameValue r v)
    | .absurd v => .absurd (renameValue r v)
    | .bind m n => .bind (renameComp r m) (renameComp (Original.up r) n)
    | .unionCase v l right => .unionCase (renameValue r v) (renameComp (Original.up r) l) (renameComp (Original.up r) right)
    | .scope owner body => .scope owner (renameComp r body)
    | .expose ev rv body => .expose ev rv (renameComp r body)
    | .request op v k => .request op (renameValue r v) (renameComp (Original.up r) k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (renameValue r f) (renameValue r a)
    | .handle h m => .handle (renameHandler r h) (renameComp r m)
    | .tryValue h v arms => .tryValue (renameHandler r h) (renameValue r v) (renameValueArms r arms)
    | .waitValue h v arms attempt => .waitValue (renameHandler r h) (renameValue r v)
        (renameValueArms r arms) (renameComp r attempt)
    | .tryOperation h op p k arms => .tryOperation (renameHandler r h) op (renameValue r p)
        (renameComp (Original.up r) k) (renameOperationArms r arms)
    | .waitOperation h op p k arms attempt => .waitOperation (renameHandler r h) op (renameValue r p)
        (renameComp (Original.up r) k) (renameOperationArms r arms) (renameComp r attempt)
  def renameHandler (r : Nat → Nat) : Handler → Handler
    | .mk id a b vs os => .mk id a b (renameValueArms r vs) (renameOperationArms r os)
  def renameValueArms (r : Nat → Nat) : ValueArms → ValueArms
    | .nil => .nil
    | .cons body rest => .cons (renameComp (Original.up r) body) (renameValueArms r rest)
  def renameOperationArms (r : Nat → Nat) : OperationArms → OperationArms
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (renameComp (Original.up (Original.up r)) body)
        (renameOperationArms r rest)
  def renameAdapter (r : Nat → Nat) : Adapter → Adapter
    | .mk a b body paths views => .mk a b (renameComp (Original.up r) body) paths views
end

def lift (s : Nat → Value) : Nat → Value
  | 0 => .var 0
  | n+1 => renameValue Nat.succ (s n)

mutual
  def substValue (s : Nat → Value) : Value → Value
    | .var i => s i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (substComp s m)
    | .inLeft v => .inLeft (substValue s v)
    | .inRight v => .inRight (substValue s v)
    | .both v => .both (substValue s v)
    | .top v => .top (substValue s v)
    | .view v o => .view (substValue s v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (substComp (lift s) body) (substAdapter s consumer)
    | .wrap f input output => .wrap (substValue s f) (substAdapter s input) (substAdapter s output)
  def substComp (s : Nat → Value) : Comp → Comp
    | .ret v => .ret (substValue s v)
    | .force v => .force (substValue s v)
    | .chooseLeft v => .chooseLeft (substValue s v)
    | .chooseRight v => .chooseRight (substValue s v)
    | .absurd v => .absurd (substValue s v)
    | .bind m n => .bind (substComp s m) (substComp (lift s) n)
    | .unionCase v l r => .unionCase (substValue s v) (substComp (lift s) l) (substComp (lift s) r)
    | .scope owner body => .scope owner (substComp s body)
    | .expose ev rv body => .expose ev rv (substComp s body)
    | .request op v k => .request op (substValue s v) (substComp (lift s) k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (substValue s f) (substValue s a)
    | .handle h m => .handle (substHandler s h) (substComp s m)
    | .tryValue h v arms => .tryValue (substHandler s h) (substValue s v) (substValueArms s arms)
    | .waitValue h v arms attempt => .waitValue (substHandler s h) (substValue s v)
        (substValueArms s arms) (substComp s attempt)
    | .tryOperation h op p k arms => .tryOperation (substHandler s h) op (substValue s p)
        (substComp (lift s) k) (substOperationArms s arms)
    | .waitOperation h op p k arms attempt => .waitOperation (substHandler s h) op (substValue s p)
        (substComp (lift s) k) (substOperationArms s arms) (substComp s attempt)
  def substHandler (s : Nat → Value) : Handler → Handler
    | .mk id a b vs os => .mk id a b (substValueArms s vs) (substOperationArms s os)
  def substValueArms (s : Nat → Value) : ValueArms → ValueArms
    | .nil => .nil
    | .cons body rest => .cons (substComp (lift s) body) (substValueArms s rest)
  def substOperationArms (s : Nat → Value) : OperationArms → OperationArms
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (substComp (lift (lift s)) body)
        (substOperationArms s rest)
  def substAdapter (s : Nat → Value) : Adapter → Adapter
    | .mk a b body paths views => .mk a b (substComp (lift s) body) paths views
end

def RenamingTyped (env target : Context) (r : Nat → Nat) : Prop :=
  ∀ i a, env i = some a → target (r i) = some a

theorem up_typed (h : RenamingTyped env target r) (a : Ty) :
    RenamingTyped (extend env a) (extend target a) (Original.up r) := by
  intro i b hi
  cases i with
  | zero => exact hi
  | succ i => exact h i b hi

mutual
  theorem renameValue_typed (h : ValueTyped env v a) (ht : RenamingTyped env target r) :
      ValueTyped target (renameValue r v) a := by
    cases h with
    | var h => exact .var (ht _ _ h)
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (renameComp_typed h ht)
    | inLeft h => exact .inLeft (renameValue_typed h ht)
    | inRight h => exact .inRight (renameValue_typed h ht)
    | top h => exact .top (renameValue_typed h ht)
    | view h => exact .view (renameValue_typed h ht)
    | both h k => exact .both (renameValue_typed h ht) (renameValue_typed k ht)
    | lambdaValue h k => exact .lambdaValue (renameComp_typed h (up_typed ht _)) (renameAdapter_typed k ht)
    | lambdaComputation h k => exact .lambdaComputation (renameComp_typed h (up_typed ht _)) (renameAdapter_typed k ht)
    | wrap h i o => exact .wrap (renameValue_typed h ht) (renameAdapter_typed i ht) (renameAdapter_typed o ht)
  theorem renameComp_typed (h : CompTyped env m a) (ht : RenamingTyped env target r) :
      CompTyped target (renameComp r m) a := by
    cases h with
    | ret h => exact .ret (renameValue_typed h ht)
    | force h => exact .force (renameValue_typed h ht)
    | chooseLeft h => exact .chooseLeft (renameValue_typed h ht)
    | chooseRight h => exact .chooseRight (renameValue_typed h ht)
    | absurd h => exact .absurd (renameValue_typed h ht)
    | bind h k => exact .bind (renameComp_typed h ht) (renameComp_typed k (up_typed ht _))
    | unionCase h l r =>
        exact .unionCase (renameValue_typed h ht)
          (renameComp_typed l (up_typed ht _)) (renameComp_typed r (up_typed ht _))
    | scope h => exact .scope (renameComp_typed h ht)
    | expose h => exact .expose (renameComp_typed h ht)
    | request h k => exact .request (renameValue_typed h ht) (renameComp_typed k (up_typed ht _))
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (renameValue_typed h ht) (renameValue_typed k ht)
    | handle hh hm => exact .handle (renameHandler_typed hh ht) (renameComp_typed hm ht)
    | tryValue hh hv hs => exact .tryValue (renameHandler_typed hh ht) (renameValue_typed hv ht) (renameValueArms_typed hs ht)
    | waitValue hh hv hs hm => exact .waitValue (renameHandler_typed hh ht) (renameValue_typed hv ht) (renameValueArms_typed hs ht) (renameComp_typed hm ht)
    | tryOperation hh hp hk hs => exact .tryOperation (renameHandler_typed hh ht) (renameValue_typed hp ht) (renameComp_typed hk (up_typed ht _)) (renameOperationArms_typed hs ht)
    | waitOperation hh hp hk hs hm => exact .waitOperation (renameHandler_typed hh ht) (renameValue_typed hp ht) (renameComp_typed hk (up_typed ht _)) (renameOperationArms_typed hs ht) (renameComp_typed hm ht)
  theorem renameHandler_typed (h : HandlerTyped env handler a b) (ht : RenamingTyped env target r) :
      HandlerTyped target (renameHandler r handler) a b := by
    cases h with
    | mk hv ho => exact .mk (renameValueArms_typed hv ht) (renameOperationArms_typed ho ht)
  theorem renameValueArms_typed (h : ValueArmsTyped env arms a b) (ht : RenamingTyped env target r) :
      ValueArmsTyped target (renameValueArms r arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (renameComp_typed hb (up_typed ht _)) (renameValueArms_typed hr ht)
  theorem renameOperationArms_typed (h : OperationArmsTyped env arms a b) (ht : RenamingTyped env target r) :
      OperationArmsTyped target (renameOperationArms r arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (renameComp_typed hb (up_typed (up_typed ht _) _)) (renameOperationArms_typed hr ht)
  theorem renameAdapter_typed (h : AdapterTyped env adapter a b) (ht : RenamingTyped env target r) :
      AdapterTyped target (renameAdapter r adapter) a b := by
    cases h with
    | mk h => exact .mk (renameComp_typed h (up_typed ht _))
end

def SubstitutionTyped (env target : Context) (s : Nat → Value) : Prop :=
  ∀ i a, env i = some a → ValueTyped target (s i) a

theorem lift_typed (h : SubstitutionTyped env target s) (a : Ty) :
    SubstitutionTyped (extend env a) (extend target a) (lift s) := by
  intro i b hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst b
      exact .var rfl
  | succ i => exact renameValue_typed (h i b hi) (fun _ _ h => h)

mutual
  theorem substValue_typed (h : ValueTyped env v a) (ht : SubstitutionTyped env target s) :
      ValueTyped target (substValue s v) a := by
    cases h with
    | var h => exact ht _ _ h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (substComp_typed h ht)
    | inLeft h => exact .inLeft (substValue_typed h ht)
    | inRight h => exact .inRight (substValue_typed h ht)
    | top h => exact .top (substValue_typed h ht)
    | view h => exact .view (substValue_typed h ht)
    | both h k => exact .both (substValue_typed h ht) (substValue_typed k ht)
    | lambdaValue h k => exact .lambdaValue (substComp_typed h (lift_typed ht _)) (substAdapter_typed k ht)
    | lambdaComputation h k => exact .lambdaComputation (substComp_typed h (lift_typed ht _)) (substAdapter_typed k ht)
    | wrap h i o => exact .wrap (substValue_typed h ht) (substAdapter_typed i ht) (substAdapter_typed o ht)
  theorem substComp_typed (h : CompTyped env m a) (ht : SubstitutionTyped env target s) :
      CompTyped target (substComp s m) a := by
    cases h with
    | ret h => exact .ret (substValue_typed h ht)
    | force h => exact .force (substValue_typed h ht)
    | chooseLeft h => exact .chooseLeft (substValue_typed h ht)
    | chooseRight h => exact .chooseRight (substValue_typed h ht)
    | absurd h => exact .absurd (substValue_typed h ht)
    | bind h k => exact .bind (substComp_typed h ht) (substComp_typed k (lift_typed ht _))
    | unionCase h l r =>
        exact .unionCase (substValue_typed h ht)
          (substComp_typed l (lift_typed ht _)) (substComp_typed r (lift_typed ht _))
    | scope h => exact .scope (substComp_typed h ht)
    | expose h => exact .expose (substComp_typed h ht)
    | request h k => exact .request (substValue_typed h ht) (substComp_typed k (lift_typed ht _))
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (substValue_typed h ht) (substValue_typed k ht)
    | handle hh hm => exact .handle (substHandler_typed hh ht) (substComp_typed hm ht)
    | tryValue hh hv hs => exact .tryValue (substHandler_typed hh ht) (substValue_typed hv ht) (substValueArms_typed hs ht)
    | waitValue hh hv hs hm => exact .waitValue (substHandler_typed hh ht) (substValue_typed hv ht) (substValueArms_typed hs ht) (substComp_typed hm ht)
    | tryOperation hh hp hk hs => exact .tryOperation (substHandler_typed hh ht) (substValue_typed hp ht) (substComp_typed hk (lift_typed ht _)) (substOperationArms_typed hs ht)
    | waitOperation hh hp hk hs hm => exact .waitOperation (substHandler_typed hh ht) (substValue_typed hp ht) (substComp_typed hk (lift_typed ht _)) (substOperationArms_typed hs ht) (substComp_typed hm ht)
  theorem substHandler_typed (h : HandlerTyped env handler a b) (ht : SubstitutionTyped env target s) :
      HandlerTyped target (substHandler s handler) a b := by
    cases h with
    | mk hv ho => exact .mk (substValueArms_typed hv ht) (substOperationArms_typed ho ht)
  theorem substValueArms_typed (h : ValueArmsTyped env arms a b) (ht : SubstitutionTyped env target s) :
      ValueArmsTyped target (substValueArms s arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (substComp_typed hb (lift_typed ht _)) (substValueArms_typed hr ht)
  theorem substOperationArms_typed (h : OperationArmsTyped env arms a b) (ht : SubstitutionTyped env target s) :
      OperationArmsTyped target (substOperationArms s arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (substComp_typed hb (lift_typed (lift_typed ht _) _)) (substOperationArms_typed hr ht)
  theorem substAdapter_typed (h : AdapterTyped env adapter a b) (ht : SubstitutionTyped env target s) :
      AdapterTyped target (substAdapter s adapter) a b := by
    cases h with
    | mk h => exact .mk (substComp_typed h (lift_typed ht _))
end

def single (v : Value) : Nat → Value
  | 0 => v
  | n+1 => .var n

theorem substitute_top (hb : CompTyped (extend env a) body b) (hv : ValueTyped env v a) :
    CompTyped env (substComp (single v) body) b := by
  apply substComp_typed hb
  intro i t hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst t
      exact hv
  | succ i => exact .var hi


/- Structural embedding recurses into every accepted code binder. -/
mutual
  def embedValue : HigherOrder.Value → Value
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (embedComp m)
    | .inLeft v => .inLeft (embedValue v)
    | .inRight v => .inRight (embedValue v)
    | .both v => .both (embedValue v)
    | .top v => .top (embedValue v)
    | .view v o => .view (embedValue v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (embedComp body) (embedAdapter consumer)
    | .wrap f input output => .wrap (embedValue f) (embedAdapter input) (embedAdapter output)
  def embedComp : HigherOrder.Comp → Comp
    | .ret v => .ret (embedValue v)
    | .force v => .force (embedValue v)
    | .chooseLeft v => .chooseLeft (embedValue v)
    | .chooseRight v => .chooseRight (embedValue v)
    | .absurd v => .absurd (embedValue v)
    | .bind m n => .bind (embedComp m) (embedComp n)
    | .unionCase v l right => .unionCase (embedValue v) (embedComp l) (embedComp right)
    | .scope owner body => .scope owner (embedComp body)
    | .expose ev rv body => .expose ev rv (embedComp body)
    | .request op v k => .request op (embedValue v) (embedComp k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (embedValue f) (embedValue a)
  def embedAdapter : HigherOrder.Adapter → Adapter
    | .mk a b body paths views => .mk a b (embedComp body) paths views
end

mutual
  theorem embedValue_typed (h : HigherOrder.ValueTyped env v a) :
      ValueTyped env (embedValue v) a := by
    cases h with
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (embedComp_typed h)
    | inLeft h => exact .inLeft (embedValue_typed h)
    | inRight h => exact .inRight (embedValue_typed h)
    | top h => exact .top (embedValue_typed h)
    | view h => exact .view (embedValue_typed h)
    | both h k => exact .both (embedValue_typed h) (embedValue_typed k)
    | lambdaValue h k => exact .lambdaValue (embedComp_typed h) (embedAdapter_typed k)
    | lambdaComputation h k => exact .lambdaComputation (embedComp_typed h) (embedAdapter_typed k)
    | wrap h i o => exact .wrap (embedValue_typed h) (embedAdapter_typed i) (embedAdapter_typed o)
  theorem embedComp_typed (h : HigherOrder.CompTyped env m a) :
      CompTyped env (embedComp m) a := by
    cases h with
    | ret h => exact .ret (embedValue_typed h)
    | force h => exact .force (embedValue_typed h)
    | chooseLeft h => exact .chooseLeft (embedValue_typed h)
    | chooseRight h => exact .chooseRight (embedValue_typed h)
    | absurd h => exact .absurd (embedValue_typed h)
    | bind h k => exact .bind (embedComp_typed h) (embedComp_typed k)
    | unionCase h l r =>
        exact .unionCase (embedValue_typed h)
          (embedComp_typed l) (embedComp_typed r)
    | scope h => exact .scope (embedComp_typed h)
    | expose h => exact .expose (embedComp_typed h)
    | request h k => exact .request (embedValue_typed h) (embedComp_typed k)
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (embedValue_typed h) (embedValue_typed k)
  theorem embedAdapter_typed (h : HigherOrder.AdapterTyped env adapter a b) :
      AdapterTyped env (embedAdapter adapter) a b := by
    cases h with
    | mk h => exact .mk (embedComp_typed h)
end

end YulangClosure.HigherOrder.Handler
