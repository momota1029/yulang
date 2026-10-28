import YulangClosure.HigherOrderSubstitution

/-! Full accepted higher-order grammar with graph references and simultaneous
recursive names. Candidate research theory; no native heap interpretation. -/
namespace YulangClosure.HigherOrderGraph
open HigherOrder (Ty Context emptyContext extend ViewOccurrence ReceiptTemplate
  OperationInstance PathCorrespondence)

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
  inductive Adapter (R S : Type) where
    | mk (input output : Ty) (body : Comp R S)
        (paths : List PathCorrespondence) (views : List ViewOccurrence)
end

mutual
  inductive ValueTyped (xi : R → Ty) (nu : S → Ty) : Context → Value R S → Ty → Prop
    | ref (r) : ValueTyped xi nu env (.ref r) (xi r)
    | recvar (s) : ValueTyped xi nu env (.recvar s) (nu s)
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
  inductive AdapterTyped (xi : R → Ty) (nu : S → Ty) : Context → Adapter R S → Ty → Ty → Prop where
    | mk : CompTyped xi nu (extend env a) body b →
        AdapterTyped xi nu env (.mk a b body paths views) a b
end

variable {R S T : Type} {xi : R → Ty} {nu : S → Ty}

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
  theorem substAdapter_typed (h : AdapterTyped xi nu env adapter a b) (ht : SubstitutionTyped xi nu env target s) :
      AdapterTyped xi nu target (substAdapter s adapter) a b := by
    cases h with
    | mk h => exact .mk (substComp_typed h (lift_typed ht _))
end


/- Structural embedding retains every accepted constructor and metadata field. -/
mutual
  def embedValue : HigherOrder.Value → Value R S
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
  def embedComp : HigherOrder.Comp → Comp R S
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
  def embedAdapter : HigherOrder.Adapter → Adapter R S
    | .mk a b body paths views => .mk a b (embedComp body) paths views
end

mutual
  theorem embedValue_typed (h : HigherOrder.ValueTyped env v a) :
      ValueTyped xi nu env (embedValue v) a := by
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
      CompTyped xi nu env (embedComp m) a := by
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
      AdapterTyped xi nu env (embedAdapter adapter) a b := by
    cases h with
    | mk h => exact .mk (embedComp_typed h)
end

def emptyTy : Empty → Ty := Empty.elim

mutual
  def closeNamesValue (f : R → T) (g : S → T) : Value R S → Value T Empty
    | .ref r => .ref (f r)
    | .recvar s => .ref (g s)
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (closeNamesComp f g m)
    | .inLeft v => .inLeft (closeNamesValue f g v)
    | .inRight v => .inRight (closeNamesValue f g v)
    | .both v => .both (closeNamesValue f g v)
    | .top v => .top (closeNamesValue f g v)
    | .view v o => .view (closeNamesValue f g v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (closeNamesComp f g body) (closeNamesAdapter f g consumer)
    | .wrap inner input output => .wrap (closeNamesValue f g inner) (closeNamesAdapter f g input) (closeNamesAdapter f g output)
  def closeNamesComp (f : R → T) (g : S → T) : Comp R S → Comp T Empty
    | .ret v => .ret (closeNamesValue f g v)
    | .force v => .force (closeNamesValue f g v)
    | .chooseLeft v => .chooseLeft (closeNamesValue f g v)
    | .chooseRight v => .chooseRight (closeNamesValue f g v)
    | .absurd v => .absurd (closeNamesValue f g v)
    | .bind m n => .bind (closeNamesComp f g m) (closeNamesComp f g n)
    | .unionCase v l right => .unionCase (closeNamesValue f g v) (closeNamesComp f g l) (closeNamesComp f g right)
    | .scope owner body => .scope owner (closeNamesComp f g body)
    | .expose ev rv body => .expose ev rv (closeNamesComp f g body)
    | .request op v k => .request op (closeNamesValue f g v) (closeNamesComp f g k)
    | .fail reason => .fail reason
    | .dynamicCall fn a => .dynamicCall (closeNamesValue f g fn) (closeNamesValue f g a)
  def closeNamesAdapter (f : R → T) (g : S → T) : Adapter R S → Adapter T Empty
    | .mk a b body paths views => .mk a b (closeNamesComp f g body) paths views
end

variable {tau : T → Ty}

mutual
  theorem closeNamesValue_typed (h : ValueTyped xi nu env v a) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      ValueTyped tau emptyTy env (closeNamesValue f g v) a := by
    cases h with
    | ref r =>
        simpa only [closeNamesValue, hf] using (ValueTyped.ref (xi := tau) (nu := emptyTy) (env := env) (f r))
    | recvar r =>
        simpa only [closeNamesValue, hg] using (ValueTyped.ref (xi := tau) (nu := emptyTy) (env := env) (g r))
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (closeNamesComp_typed h f g hf hg)
    | inLeft h => exact .inLeft (closeNamesValue_typed h f g hf hg)
    | inRight h => exact .inRight (closeNamesValue_typed h f g hf hg)
    | top h => exact .top (closeNamesValue_typed h f g hf hg)
    | view h => exact .view (closeNamesValue_typed h f g hf hg)
    | both h k => exact .both (closeNamesValue_typed h f g hf hg) (closeNamesValue_typed k f g hf hg)
    | lambdaValue h k => exact .lambdaValue (closeNamesComp_typed h f g hf hg) (closeNamesAdapter_typed k f g hf hg)
    | lambdaComputation h k => exact .lambdaComputation (closeNamesComp_typed h f g hf hg) (closeNamesAdapter_typed k f g hf hg)
    | wrap h i o => exact .wrap (closeNamesValue_typed h f g hf hg) (closeNamesAdapter_typed i f g hf hg) (closeNamesAdapter_typed o f g hf hg)
  theorem closeNamesComp_typed (h : CompTyped xi nu env m a) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      CompTyped tau emptyTy env (closeNamesComp f g m) a := by
    cases h with
    | ret h => exact .ret (closeNamesValue_typed h f g hf hg)
    | force h => exact .force (closeNamesValue_typed h f g hf hg)
    | chooseLeft h => exact .chooseLeft (closeNamesValue_typed h f g hf hg)
    | chooseRight h => exact .chooseRight (closeNamesValue_typed h f g hf hg)
    | absurd h => exact .absurd (closeNamesValue_typed h f g hf hg)
    | bind h k => exact .bind (closeNamesComp_typed h f g hf hg) (closeNamesComp_typed k f g hf hg)
    | unionCase h l r =>
        exact .unionCase (closeNamesValue_typed h f g hf hg)
          (closeNamesComp_typed l f g hf hg) (closeNamesComp_typed r f g hf hg)
    | scope h => exact .scope (closeNamesComp_typed h f g hf hg)
    | expose h => exact .expose (closeNamesComp_typed h f g hf hg)
    | request h k => exact .request (closeNamesValue_typed h f g hf hg) (closeNamesComp_typed k f g hf hg)
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (closeNamesValue_typed h f g hf hg) (closeNamesValue_typed k f g hf hg)
  theorem closeNamesAdapter_typed (h : AdapterTyped xi nu env adapter a b) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      AdapterTyped tau emptyTy env (closeNamesAdapter f g adapter) a b := by
    cases h with
    | mk h => exact .mk (closeNamesComp_typed h f g hf hg)
end

end YulangClosure.HigherOrderGraph
