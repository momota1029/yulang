import YulangClosure.HigherOrderHandlerSafety
import YulangClosure.HigherOrderGraphSafety

namespace YulangClosure.HandlerGraph
open YulangClosure.HigherOrder (Ty Context emptyContext extend OperationInstance
  ViewOccurrence ReceiptTemplate PathCorrespondence)

/-! Candidate recursively extended syntax. Every attempt is actual Comp R S code.
An operation arm binds payload at zero and the original shallow continuation at
one. Eligibility is raw data; its permission interpretation is deliberately open.
No definition below supplies typing as syntax or as an operational premise. -/

mutual
  inductive Value (R S : Type) where
    | ref (reference : R)
    | recvar (name : S)
    | var (index : Nat)
    | unit
    | bool (value : Bool)
    | int (value : Int)
    | floatBits (value : UInt64)
    | string (value : String)
    | bytes (value : List UInt8)
    | path (value : List UInt8)
    | char (value : String)
    | delay (body : Comp R S)
    | inLeft (value : Value R S)
    | inRight (value : Value R S)
    | both (value : Value R S)
    | top (value : Value R S)
    | view (value : Value R S) (occurrence : ViewOccurrence)
    | lambda (mode : Original.Mode) (receipt : ReceiptTemplate)
        (argument bodyResult result : Ty) (body : Comp R S) (consumer : Adapter R S)
    | wrap (inner : Value R S) (input output : Adapter R S)
  inductive Comp (R S : Type) where
    | ret (value : Value R S)
    | force (value : Value R S)
    | bind (first body : Comp R S)
    | unionCase (value : Value R S) (left right : Comp R S)
    | chooseLeft (value : Value R S)
    | chooseRight (value : Value R S)
    | absurd (value : Value R S)
    | scope (owner : Nat) (body : Comp R S)
    | expose (effectView resultView : ViewOccurrence) (body : Comp R S)
    | request (op : OperationInstance) (payload : Value R S) (continuation : Comp R S)
    | fail (reason : Original.Failure)
    | dynamicCall (function argument : Value R S)
    | handle (handler : Handler R S) (body : Comp R S)
    | tryValue (handler : Handler R S) (value : Value R S) (arms : ValueArms R S)
    | waitValue (handler : Handler R S) (value : Value R S) (remaining : ValueArms R S) (attempt : Comp R S)
    | tryOperation (handler : Handler R S) (op : OperationInstance) (payload : Value R S) (continuation : Comp R S) (arms : OperationArms R S)
    | waitOperation (handler : Handler R S) (op : OperationInstance) (payload : Value R S) (continuation : Comp R S) (remaining : OperationArms R S) (attempt : Comp R S)
  inductive Handler (R S : Type) where
    | mk (identity : Nat) (input output : Ty) (values : ValueArms R S) (operations : OperationArms R S)
  inductive ValueArms (R S : Type) where
    | nil
    | cons (body : Comp R S) (rest : ValueArms R S)
  inductive OperationArms (R S : Type) where
    | nil
    | cons (op : OperationInstance) (eligible : Bool) (body : Comp R S) (rest : OperationArms R S)
  inductive Adapter (R S : Type) where
    | mk (input output : Ty) (body : Comp R S)
        (paths : List PathCorrespondence) (views : List ViewOccurrence)
end


mutual
  inductive ValueTyped (xi : R → Ty) (nu : S → Ty) : Context → Value R S → Ty → Prop
    | ref (r : R) : ValueTyped xi nu env (.ref r) (xi r)
    | recvar (s : S) : ValueTyped xi nu env (.recvar s) (nu s)
    | var : env i = some a → ValueTyped xi nu env (.var i) a
    | unit : ValueTyped xi nu env .unit (.base .unit)
    | bool : ValueTyped xi nu env (.bool v) (.base .bool)
    | int : ValueTyped xi nu env (.int v) (.base .int)
    | floatBits : ValueTyped xi nu env (.floatBits v) (.base .float)
    | string : ValueTyped xi nu env (.string v) (.base .string)
    | bytes : ValueTyped xi nu env (.bytes v) (.base .bytes)
    | path : ValueTyped xi nu env (.path v) (.base .path)
    | char : ValueTyped xi nu env (.char v) (.base .char)
    | delay : CompTyped xi nu env m a → ValueTyped xi nu env (.delay m) (.thunk a)
    | inLeft : ValueTyped xi nu env v a → ValueTyped xi nu env (.inLeft v) (.union a b)
    | inRight : ValueTyped xi nu env v b → ValueTyped xi nu env (.inRight v) (.union a b)
    | both : ValueTyped xi nu env v a → ValueTyped xi nu env v b →
        ValueTyped xi nu env (.both v) (.intersection a b)
    | top : ValueTyped xi nu env v a → ValueTyped xi nu env (.top v) .top
    | view : ValueTyped xi nu env v a → ValueTyped xi nu env (.view v occurrence) a
    | lambdaValue : CompTyped xi nu (extend env a) body b → AdapterTyped xi nu env consumer b r →
        ValueTyped xi nu env (.lambda .value receipt a b r body consumer) (.callable a r)
    | lambdaComputation : CompTyped xi nu (extend env (.thunk a)) body b → AdapterTyped xi nu env consumer b r →
        ValueTyped xi nu env (.lambda .computation receipt a b r body consumer) (.callable a r)
    | wrap : ValueTyped xi nu env f (.callable a b) → AdapterTyped xi nu env input c a →
        AdapterTyped xi nu env output b d → ValueTyped xi nu env (.wrap f input output) (.callable c d)
  inductive CompTyped (xi : R → Ty) (nu : S → Ty) : Context → Comp R S → Ty → Prop
    | ret : ValueTyped xi nu env v a → CompTyped xi nu env (.ret v) a
    | force : ValueTyped xi nu env v (.thunk a) → CompTyped xi nu env (.force v) a
    | bind : CompTyped xi nu env m a → CompTyped xi nu (extend env a) n b →
        CompTyped xi nu env (.bind m n) b
    | unionCase : ValueTyped xi nu env v (.union a b) →
        CompTyped xi nu (extend env a) l c → CompTyped xi nu (extend env b) r c →
        CompTyped xi nu env (.unionCase v l r) c
    | chooseLeft : ValueTyped xi nu env v (.intersection a b) → CompTyped xi nu env (.chooseLeft v) a
    | chooseRight : ValueTyped xi nu env v (.intersection a b) → CompTyped xi nu env (.chooseRight v) b
    | absurd : ValueTyped xi nu env v .bottom → CompTyped xi nu env (.absurd v) a
    | scope : CompTyped xi nu env body a → CompTyped xi nu env (.scope owner body) a
    | expose : CompTyped xi nu env body a → CompTyped xi nu env (.expose ev rv body) a
    | request : ValueTyped xi nu env payload op.payloadType →
        CompTyped xi nu (extend env op.responseType) continuation a →
        CompTyped xi nu env (.request op payload continuation) a
    | fail : CompTyped xi nu env (.fail reason) a
    | dynamicCall : ValueTyped xi nu env f (.callable a b) → ValueTyped xi nu env arg (.thunk a) →
        CompTyped xi nu env (.dynamicCall f arg) b
    | handle : HandlerTyped xi nu env h a b → CompTyped xi nu env m a → CompTyped xi nu env (.handle h m) b
    | tryValue : HandlerTyped xi nu env h a b → ValueTyped xi nu env v a → ValueArmsTyped xi nu env arms a b →
        CompTyped xi nu env (.tryValue h v arms) b
    | waitValue : HandlerTyped xi nu env h a b → ValueTyped xi nu env v a → ValueArmsTyped xi nu env arms a b →
        CompTyped xi nu env attempt (.union (.base .unit) b) → CompTyped xi nu env (.waitValue h v arms attempt) b
    | tryOperation : HandlerTyped xi nu env h a b → ValueTyped xi nu env p op.payloadType →
        CompTyped xi nu (extend env op.responseType) k a → OperationArmsTyped xi nu env arms a b →
        CompTyped xi nu env (.tryOperation h op p k arms) b
    | waitOperation : HandlerTyped xi nu env h a b → ValueTyped xi nu env p op.payloadType →
        CompTyped xi nu (extend env op.responseType) k a → OperationArmsTyped xi nu env arms a b →
        CompTyped xi nu env attempt (.union (.base .unit) b) → CompTyped xi nu env (.waitOperation h op p k arms attempt) b
  inductive HandlerTyped (xi : R → Ty) (nu : S → Ty) : Context → Handler R S → Ty → Ty → Prop where
    | mk : ValueArmsTyped xi nu env vs a b → OperationArmsTyped xi nu env os a b →
        HandlerTyped xi nu env (.mk identity a b vs os) a b
  inductive ValueArmsTyped (xi : R → Ty) (nu : S → Ty) : Context → ValueArms R S → Ty → Ty → Prop where
    | nil : ValueArmsTyped xi nu env .nil a b
    | cons : CompTyped xi nu (extend env a) body (.union (.base .unit) b) →
        ValueArmsTyped xi nu env rest a b → ValueArmsTyped xi nu env (.cons body rest) a b
  inductive OperationArmsTyped (xi : R → Ty) (nu : S → Ty) : Context → OperationArms R S → Ty → Ty → Prop where
    | nil : OperationArmsTyped xi nu env .nil a b
    | cons : CompTyped xi nu (extend (extend env (.callable op.responseType a)) op.payloadType)
          body (.union (.base .unit) b) → OperationArmsTyped xi nu env rest a b →
        OperationArmsTyped xi nu env (.cons op eligible body rest) a b
  inductive AdapterTyped (xi : R → Ty) (nu : S → Ty) : Context → Adapter R S → Ty → Ty → Prop where
    | mk : CompTyped xi nu (extend env a) body b →
        AdapterTyped xi nu env (.mk a b body paths views) a b
end




variable {R S : Type} {xi : R → Ty} {nu : S → Ty}

mutual
  def renameValue (r : Nat → Nat) : Value R S → Value R S
    | .ref r => .ref r
    | .recvar s => .recvar s
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
  def renameComp (r : Nat → Nat) : Comp R S → Comp R S
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
  def renameHandler (r : Nat → Nat) : Handler R S → Handler R S
    | .mk id a b vs os => .mk id a b (renameValueArms r vs) (renameOperationArms r os)
  def renameValueArms (r : Nat → Nat) : ValueArms R S → ValueArms R S
    | .nil => .nil
    | .cons body rest => .cons (renameComp (Original.up r) body) (renameValueArms r rest)
  def renameOperationArms (r : Nat → Nat) : OperationArms R S → OperationArms R S
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (renameComp (Original.up (Original.up r)) body)
        (renameOperationArms r rest)
  def renameAdapter (r : Nat → Nat) : Adapter R S → Adapter R S
    | .mk a b body paths views => .mk a b (renameComp (Original.up r) body) paths views
end

def lift (s : Nat → Value R S) : Nat → Value R S
  | 0 => .var 0
  | n+1 => renameValue Nat.succ (s n)

mutual
  def substValue (s : Nat → Value R S) : Value R S → Value R S
    | .ref r => .ref r
    | .recvar s => .recvar s
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
  def substComp (s : Nat → Value R S) : Comp R S → Comp R S
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
  def substHandler (s : Nat → Value R S) : Handler R S → Handler R S
    | .mk id a b vs os => .mk id a b (substValueArms s vs) (substOperationArms s os)
  def substValueArms (s : Nat → Value R S) : ValueArms R S → ValueArms R S
    | .nil => .nil
    | .cons body rest => .cons (substComp (lift s) body) (substValueArms s rest)
  def substOperationArms (s : Nat → Value R S) : OperationArms R S → OperationArms R S
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (substComp (lift (lift s)) body)
        (substOperationArms s rest)
  def substAdapter (s : Nat → Value R S) : Adapter R S → Adapter R S
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
  theorem renameValue_typed (h : ValueTyped xi nu env v a) (ht : RenamingTyped env target r) :
      ValueTyped xi nu target (renameValue r v) a := by
    cases h with
    | ref r => exact .ref r
    | recvar s => exact .recvar s
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
  theorem renameComp_typed (h : CompTyped xi nu env m a) (ht : RenamingTyped env target r) :
      CompTyped xi nu target (renameComp r m) a := by
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
  theorem renameHandler_typed (h : HandlerTyped xi nu env handler a b) (ht : RenamingTyped env target r) :
      HandlerTyped xi nu target (renameHandler r handler) a b := by
    cases h with
    | mk hv ho => exact .mk (renameValueArms_typed hv ht) (renameOperationArms_typed ho ht)
  theorem renameValueArms_typed (h : ValueArmsTyped xi nu env arms a b) (ht : RenamingTyped env target r) :
      ValueArmsTyped xi nu target (renameValueArms r arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (renameComp_typed hb (up_typed ht _)) (renameValueArms_typed hr ht)
  theorem renameOperationArms_typed (h : OperationArmsTyped xi nu env arms a b) (ht : RenamingTyped env target r) :
      OperationArmsTyped xi nu target (renameOperationArms r arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (renameComp_typed hb (up_typed (up_typed ht _) _)) (renameOperationArms_typed hr ht)
  theorem renameAdapter_typed (h : AdapterTyped xi nu env adapter a b) (ht : RenamingTyped env target r) :
      AdapterTyped xi nu target (renameAdapter r adapter) a b := by
    cases h with
    | mk h => exact .mk (renameComp_typed h (up_typed ht _))
end

def SubstitutionTyped (xi : R → Ty) (nu : S → Ty) (env target : Context) (s : Nat → Value R S) : Prop :=
  ∀ i a, env i = some a → ValueTyped xi nu target (s i) a

theorem lift_typed (h : SubstitutionTyped xi nu env target s) (a : Ty) :
    SubstitutionTyped xi nu (extend env a) (extend target a) (lift s) := by
  intro i b hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst b
      exact .var rfl
  | succ i => exact renameValue_typed (h i b hi) (fun _ _ h => h)

mutual
  theorem substValue_typed (h : ValueTyped xi nu env v a) (ht : SubstitutionTyped xi nu env target s) :
      ValueTyped xi nu target (substValue s v) a := by
    cases h with
    | ref r => exact .ref r
    | recvar s => exact .recvar s
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
  theorem substComp_typed (h : CompTyped xi nu env m a) (ht : SubstitutionTyped xi nu env target s) :
      CompTyped xi nu target (substComp s m) a := by
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
  theorem substHandler_typed (h : HandlerTyped xi nu env handler a b) (ht : SubstitutionTyped xi nu env target s) :
      HandlerTyped xi nu target (substHandler s handler) a b := by
    cases h with
    | mk hv ho => exact .mk (substValueArms_typed hv ht) (substOperationArms_typed ho ht)
  theorem substValueArms_typed (h : ValueArmsTyped xi nu env arms a b) (ht : SubstitutionTyped xi nu env target s) :
      ValueArmsTyped xi nu target (substValueArms s arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (substComp_typed hb (lift_typed ht _)) (substValueArms_typed hr ht)
  theorem substOperationArms_typed (h : OperationArmsTyped xi nu env arms a b) (ht : SubstitutionTyped xi nu env target s) :
      OperationArmsTyped xi nu target (substOperationArms s arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (substComp_typed hb (lift_typed (lift_typed ht _) _)) (substOperationArms_typed hr ht)
  theorem substAdapter_typed (h : AdapterTyped xi nu env adapter a b) (ht : SubstitutionTyped xi nu env target s) :
      AdapterTyped xi nu target (substAdapter s adapter) a b := by
    cases h with
    | mk h => exact .mk (substComp_typed h (lift_typed ht _))
end

def single (v : Value R S) : Nat → Value R S
  | 0 => v
  | n+1 => .var n

theorem substitute_top (hb : CompTyped xi nu (extend env a) body b) (hv : ValueTyped xi nu env v a) :
    CompTyped xi nu env (substComp (single v) body) b := by
  apply substComp_typed hb
  intro i t hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst t
      exact hv
  | succ i => exact .var hi



def emptyTy : Empty → Ty := Empty.elim


theorem lift_cancel (r : Nat → Nat) (s : Nat → Value R S)
    (h : ∀ i, s (r i) = .var i) :
    ∀ i, lift s (Original.up r i) = .var i := by
  intro i
  cases i with
  | zero => rfl
  | succ i => simp only [Original.up, lift, h, renameValue]

mutual
  theorem value_rename_cancel (v : Value R S) (r : Nat → Nat) (s : Nat → Value R S)
      (hcancel : ∀ i, s (r i) = .var i) : substValue s (renameValue r v) = v := by
    cases v with
    | ref r => rfl
    | recvar s => rfl
    | var i => exact hcancel i
    | unit  => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | delay m => 
        simp only [renameValue, substValue]
        rw [comp_rename_cancel m r s hcancel]
    | inLeft v => 
        simp only [renameValue, substValue]
        rw [value_rename_cancel v r s hcancel]
    | inRight v => 
        simp only [renameValue, substValue]
        rw [value_rename_cancel v r s hcancel]
    | both v => 
        simp only [renameValue, substValue]
        rw [value_rename_cancel v r s hcancel]
    | top v => 
        simp only [renameValue, substValue]
        rw [value_rename_cancel v r s hcancel]
    | view v o => 
        simp only [renameValue, substValue]
        rw [value_rename_cancel v r s hcancel]
    | lambda mode receipt a b c body consumer => 
        simp only [renameValue, substValue]
        rw [comp_rename_cancel body (Original.up r) (lift s) (lift_cancel r s hcancel), adapter_rename_cancel consumer r s hcancel]
    | wrap f input output => 
        simp only [renameValue, substValue]
        rw [value_rename_cancel f r s hcancel, adapter_rename_cancel input r s hcancel, adapter_rename_cancel output r s hcancel]
  theorem comp_rename_cancel (v : Comp R S) (r : Nat → Nat) (s : Nat → Value R S)
      (hcancel : ∀ i, s (r i) = .var i) : substComp s (renameComp r v) = v := by
    cases v with
    | ret v => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel]
    | force v => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel]
    | chooseLeft v => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel]
    | chooseRight v => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel]
    | absurd v => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel]
    | bind m n => 
        simp only [renameComp, substComp]
        rw [comp_rename_cancel m r s hcancel, comp_rename_cancel n (Original.up r) (lift s) (lift_cancel r s hcancel)]
    | unionCase v l right => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel, comp_rename_cancel l (Original.up r) (lift s) (lift_cancel r s hcancel), comp_rename_cancel right (Original.up r) (lift s) (lift_cancel r s hcancel)]
    | scope owner body => 
        simp only [renameComp, substComp]
        rw [comp_rename_cancel body r s hcancel]
    | expose ev rv body => 
        simp only [renameComp, substComp]
        rw [comp_rename_cancel body r s hcancel]
    | request op v k => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel v r s hcancel, comp_rename_cancel k (Original.up r) (lift s) (lift_cancel r s hcancel)]
    | fail reason => rfl
    | dynamicCall f a => 
        simp only [renameComp, substComp]
        rw [value_rename_cancel f r s hcancel, value_rename_cancel a r s hcancel]
    | handle h m => 
        simp only [renameComp, substComp]
        rw [handler_rename_cancel h r s hcancel, comp_rename_cancel m r s hcancel]
    | tryValue h v arms => 
        simp only [renameComp, substComp]
        rw [handler_rename_cancel h r s hcancel, value_rename_cancel v r s hcancel, valueArms_rename_cancel arms r s hcancel]
    | waitValue h v arms attempt => 
        simp only [renameComp, substComp]
        rw [handler_rename_cancel h r s hcancel, value_rename_cancel v r s hcancel, valueArms_rename_cancel arms r s hcancel, comp_rename_cancel attempt r s hcancel]
    | tryOperation h op p k arms => 
        simp only [renameComp, substComp]
        rw [handler_rename_cancel h r s hcancel, value_rename_cancel p r s hcancel, comp_rename_cancel k (Original.up r) (lift s) (lift_cancel r s hcancel), operationArms_rename_cancel arms r s hcancel]
    | waitOperation h op p k arms attempt => 
        simp only [renameComp, substComp]
        rw [handler_rename_cancel h r s hcancel, value_rename_cancel p r s hcancel, comp_rename_cancel k (Original.up r) (lift s) (lift_cancel r s hcancel), operationArms_rename_cancel arms r s hcancel, comp_rename_cancel attempt r s hcancel]
  theorem handler_rename_cancel (v : Handler R S) (r : Nat → Nat) (s : Nat → Value R S)
      (hcancel : ∀ i, s (r i) = .var i) : substHandler s (renameHandler r v) = v := by
    cases v with
    | mk id a b vs os => 
        simp only [renameHandler, substHandler]
        rw [valueArms_rename_cancel vs r s hcancel, operationArms_rename_cancel os r s hcancel]
  theorem valueArms_rename_cancel (v : ValueArms R S) (r : Nat → Nat) (s : Nat → Value R S)
      (hcancel : ∀ i, s (r i) = .var i) : substValueArms s (renameValueArms r v) = v := by
    cases v with
    | nil  => rfl
    | cons body rest => 
        simp only [renameValueArms, substValueArms]
        rw [comp_rename_cancel body (Original.up r) (lift s) (lift_cancel r s hcancel), valueArms_rename_cancel rest r s hcancel]
  theorem operationArms_rename_cancel (v : OperationArms R S) (r : Nat → Nat) (s : Nat → Value R S)
      (hcancel : ∀ i, s (r i) = .var i) : substOperationArms s (renameOperationArms r v) = v := by
    cases v with
    | nil  => rfl
    | cons op eligible body rest => 
        simp only [renameOperationArms, substOperationArms]
        rw [comp_rename_cancel body (Original.up (Original.up r)) (lift (lift s)) (lift_cancel (Original.up r) (lift s) (lift_cancel r s hcancel)), operationArms_rename_cancel rest r s hcancel]
  theorem adapter_rename_cancel (v : Adapter R S) (r : Nat → Nat) (s : Nat → Value R S)
      (hcancel : ∀ i, s (r i) = .var i) : substAdapter s (renameAdapter r v) = v := by
    cases v with
    | mk a b body paths views => 
        simp only [renameAdapter, substAdapter]
        rw [comp_rename_cancel body (Original.up r) (lift s) (lift_cancel r s hcancel)]
end

end YulangClosure.HandlerGraph
